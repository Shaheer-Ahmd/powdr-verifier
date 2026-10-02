"""Batch the current M2 mapping and M3 cheap checks, never SMT or IO proofs.

Each direction runs in a disposable process with a wall-time limit. Results
are streamed so unsupported inputs, timeouts and worker crashes cannot silently
disappear from the coverage denominator. An incomplete map has null residual
counts, not zero. The zero-gadget checker is enabled by default; external
receive-byte assumptions require explicit authorization.
"""
import argparse
from collections import Counter, defaultdict
import csv
from datetime import datetime, timezone
from hashlib import sha256
import json
import multiprocessing as mp
from multiprocessing.connection import wait
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from time import perf_counter
import traceback

from ..lens.resolve import group_dir
from .circuit_partition import partition_circuit
from .witness_mapping import build_mapping
from .collapsed_witness import add_collapsed_witnesses
from .cheap_obligations import cheap_sweep
from .polynomial_matching import POLYNOMIAL_REASONS
from .zero_check import CONTRACT
from . import m3_display

NAME = re.compile(r'apc_candidate_(\d+)_(\d+)(?:_(.+))?\.json$')
SUPPORTED = {'no-local-residuals', 'local-residuals'}
ZERO_REASONS = ('sum-individual-zero-equations', 'quotient-product-with-no-cancellation',
                'uniform-witness-polynomial-identity', 'split-zero-sum-with-no-cancellation')
REASONS = ('canonical-match', 'trivial', 'cache', 'requires-proof', *POLYNOMIAL_REASONS, *ZERO_REASONS)


def discover(directories, *, block=None, first=None, last=None):
    """Only consecutive numbered dumps are pairs; never bridge missing steps."""
    tasks, issues, blocks, excluded = [], [], [], []
    for directory in directories:
        directory = Path(directory).resolve()
        indexed = defaultdict(lambda: defaultdict(list))
        for path in sorted(directory.glob('apc_candidate_*.json')):
            if '.powdr-opt-' in path.name:
                excluded.append(str(path))
                continue
            match = NAME.fullmatch(path.name)
            if match and (block is None or int(match[1]) == block):
                indexed[int(match[1])][int(match[2])].append((path, match[3] or ''))
        for bid, steps in sorted(indexed.items()):
            selected = sorted(n for n in steps if (first is None or n >= first)
                              and (last is None or n <= last))
            if not selected:
                continue
            blocks.append({'group': directory.name, 'block': bid, 'steps': selected})
            duplicates = [n for n in selected if len(steps[n]) != 1]
            if duplicates:
                issues.append({'group': directory.name, 'block': bid, 'kind': 'duplicate-step',
                               'steps': duplicates, 'files': [str(p) for n in duplicates for p, _ in steps[n]]})
                continue
            if len(selected) == 1:
                issues.append({'group': directory.name, 'block': bid, 'kind': 'no-adjacent-pair',
                               'steps': selected})
            for a, b in zip(selected, selected[1:]):
                if b != a + 1:
                    issues.append({'group': directory.name, 'block': bid, 'kind': 'step-gap',
                                   'before': a, 'after': b})
                    continue
                pa, na = steps[a][0]
                pb, nb = steps[b][0]
                subs = directory / f'apc_candidate_{bid}_substitutions.json'
                common = {'group': directory.name, 'block': bid, 'before_step': a, 'after_step': b,
                          'before_pass': na, 'after_pass': nb, 'before_path': str(pa), 'after_path': str(pb),
                          'substitutions_path': str(subs) if subs.is_file() else None}
                for direction in ('completeness', 'soundness'):
                    tasks.append(common | {'direction': direction})
    return tasks, {'blocks': blocks, 'issues': issues, 'excluded_optimizer_auxiliary_files': excluded}


def blank_result(task):
    return dict(task, status='pending', stage='load', error=None, counts=None,
                residual_indices=None, mapping=None, timings={}, inputs={}, seconds=0.0,
                zero_check_enabled=task.get('zero_check', True),
                polynomial_matching_enabled=task.get('polynomial_matching', True),
                polynomial_discharged=None, polynomial_proofs=[],
                authorized_contracts=[CONTRACT] if task.get('reference_recv_bytes', False) else [],
                zero_check_discharged=None, conditional_obligations=None,
                initial_residual_indices=None, zero_check_certificates=[], zero_check_proofs=[], assumptions=[])


def analyze(task, progress=None):
    row = blank_result(task)
    started = perf_counter()
    stage_started = started

    def stage(name):
        nonlocal stage_started
        now = perf_counter()
        row['timings'][row['stage']] = now - stage_started
        row['stage'] = name
        stage_started = now
        if progress:
            progress(row)

    def read(path):
        data = Path(path).read_bytes()
        row['inputs'][str(path)] = {'sha256': sha256(data).hexdigest(), 'bytes': len(data)}
        return json.loads(data)

    try:
        if task.get('reference_recv_bytes', False) and not task.get('zero_check', True):
            raise ValueError('Receive-byte contract requires the zero checker')
        before, after = read(task['before_path']), read(task['after_path'])
        subs = read(task['substitutions_path']) if task['substitutions_path'] else []
        if not isinstance(subs, list):
            raise ValueError('Substitutions file must be a list')
        ref, cand = (before, after) if task['direction'] == 'completeness' else (after, before)
        stage('partition')
        rp, cp = partition_circuit(ref), partition_circuit(cand)
        row['reference_format'], row['candidate_format'] = rp.format, cp.format
        row['candidate_sizes'] = {'algebraic': len(cp.algebraic), 'stateless': len(cp.stateless),
                                  'stateful_excluded': len(cp.stateful), 'derived_metadata': len(cp.derived)}
        stage('mapping')
        mapping = build_mapping(ref, cand, subs)
        # A total map cannot receive further collapsed proposals. Avoid an
        # unnecessary polynomial scan without changing its result.
        proposals = []
        if not mapping.total:
            stage('collapsed-witness')
            mapping, proposals = add_collapsed_witnesses(ref, cand, mapping)
        row['mapping'] = {'mapped': len(mapping.witnesses), 'live': len(mapping.candidate_columns),
                          'total': mapping.total, 'sources': dict(Counter(mapping.sources.values())),
                          'unresolved': mapping.unresolved, 'collapsed_proposals': proposals}
        if not mapping.total:
            row['status'] = 'unmapped'
            row['error'] = f'{len(mapping.unresolved)} candidate columns have no supported witness'
        else:
            stage('cheap-checks')
            goals = cheap_sweep(ref, cand, mapping,
                                polynomial_matching=row['polynomial_matching_enabled'],
                                zero_check_direction=task['direction'] if row['zero_check_enabled'] else None,
                                reference_recv_bytes=task.get('reference_recv_bytes', False))
            polynomial_goals = [g for g in goals if g.reason in POLYNOMIAL_REASONS]
            row['polynomial_proofs'] = [g.proof for g in polynomial_goals]
            row['polynomial_discharged'] = len(polynomial_goals)
            proof_goals = [g for g in goals if g.reason in ZERO_REASONS]
            row['zero_check_discharged'] = len(proof_goals)
            row['conditional_obligations'] = sum(bool(g.proof['claim']['assumptions']) for g in proof_goals)
            # Deduplicate certificates; retain full witnesses only when needed for replay.
            for goal in proof_goals:
                cert = goal.proof['certificate']
                if cert not in row['zero_check_certificates']:
                    row['zero_check_certificates'].append(cert)
                row['zero_check_proofs'].append({
                    'kind': goal.kind, 'index': goal.index,
                    'certificate': row['zero_check_certificates'].index(cert),
                    'claim': goal.proof['claim']})
                for assumption in goal.proof['claim']['assumptions']:
                    if assumption not in row['assumptions']:
                        row['assumptions'].append(assumption)
            if proof_goals or polynomial_goals:
                row['mapping']['witnesses'] = mapping.witnesses
            row['initial_residual_indices'] = {
                kind: [g.index for g in goals if g.kind == kind and (g.status == 'residual' or g.proof)]
                for kind in ('algebraic', 'stateless')}
            counts, indices = {}, {}
            for kind in ('algebraic', 'stateless'):
                selected = [g for g in goals if g.kind == kind]
                reasons = Counter(g.reason for g in selected)
                if set(reasons) - set(REASONS):
                    raise RuntimeError(f'Unrecognized cheap-check reasons: {reasons}')
                indices[kind] = [g.index for g in selected if g.status == 'residual']
                counts[kind] = {'total': len(selected), **{k: reasons[k] for k in REASONS},
                                'residual': len(indices[kind])}
            if sum(v['total'] for v in counts.values()) != len(goals):
                raise RuntimeError('Unexpected obligation kind in M3-only sweep')
            row['counts'], row['residual_indices'] = counts, indices
            row['status'] = 'local-residuals' if any(indices.values()) else 'no-local-residuals'
    except (OSError, json.JSONDecodeError) as error:
        row.update(status='input-error', error=f'{type(error).__name__}: {error}')
    except (ValueError, TypeError, KeyError, RecursionError) as error:
        row.update(status='input-error' if row['stage'] == 'load' else 'unsupported',
                   error=f'{type(error).__name__}: {error}')
    except MemoryError:
        row.update(status='resource-error', error='Worker ran out of memory')
    except Exception as error:
        row.update(status='error', error=f'{type(error).__name__}: {error}', traceback=traceback.format_exc())
    row['timings'][row['stage']] = perf_counter() - stage_started
    row['seconds'] = perf_counter() - started
    return row


def _worker(task, pipe):
    try:
        result = analyze(task, progress=lambda row: pipe.send(('progress', row)))
        pipe.send(('result', result))
    finally:
        pipe.close()


def execute(tasks, *, jobs=1, timeout=10.0, worker=None, result_factory=None):
    """Yield exactly one result per task; isolate failures and enforce limits."""
    worker = _worker if worker is None else worker
    result_factory = blank_result if result_factory is None else result_factory
    context = mp.get_context('fork' if 'fork' in mp.get_all_start_methods() else 'spawn')
    pending = iter(tasks)
    running = {}
    exhausted = False
    try:
        while running or not exhausted:
            while len(running) < jobs and not exhausted:
                try:
                    task = next(pending)
                except StopIteration:
                    exhausted = True
                    break
                parent, child = context.Pipe(duplex=False)
                process = context.Process(target=worker, args=(task, child))
                start = perf_counter()
                process.start()
                child.close()
                running[parent] = [process, start, result_factory(task)]
            if not running:
                break
            ready = set(wait(list(running), timeout=0.05))
            for pipe, state in list(running.items()):
                process, start, row = state
                completed = None
                eof = False
                if pipe in ready:
                    try:
                        while pipe.poll():
                            kind, update = pipe.recv()
                            if kind == 'result':
                                completed = update
                                break
                            row = state[2] = update
                    except EOFError:
                        eof = True
                if completed is None:
                    if perf_counter() - start >= timeout:
                        completed = row | {'status': 'timeout', 'error': f'Direction exceeded {timeout:g}s wall limit',
                                           'seconds': perf_counter()-start}
                    elif eof or (not process.is_alive() and not pipe.poll()):
                        completed = row | {'status': 'worker-error', 'error': f'Worker exited without result ({process.exitcode})',
                                           'seconds': perf_counter()-start}
                if completed is not None:
                    process.join(timeout=0.05)
                    if process.is_alive():
                        process.terminate()
                        process.join(timeout=0.2)
                    if process.is_alive():
                        process.kill()
                        process.join()
                    pipe.close()
                    del running[pipe]
                    completed['worker_wall_seconds'] = perf_counter()-start
                    yield completed
    finally:
        for pipe, (process, _, _) in running.items():
            if process.is_alive():
                process.terminate()
            process.join(timeout=0.2)
            if process.is_alive():
                process.kill()
                process.join()
            pipe.close()


def summarize(rows, expected):
    statuses = Counter(r['status'] for r in rows)
    counts = {kind: Counter() for kind in ('algebraic', 'stateless')}
    passes = {}
    input_hashes, changed_inputs = {}, set()
    for row in rows:
        for path, info in row['inputs'].items():
            if path in input_hashes and input_hashes[path] != info['sha256']:
                changed_inputs.add(path)
            input_hashes[path] = info['sha256']
        key = (row['before_pass'], row['after_pass'], row['direction'])
        bucket = passes.setdefault(key, {'before_pass': key[0], 'after_pass': key[1], 'direction': key[2],
                                         'statuses': Counter(), 'counted_directions': 0,
                                         'algebraic_residuals': 0, 'stateless_residuals': 0})
        bucket['statuses'][row['status']] += 1
        if row['counts'] is not None:
            for kind, data in row['counts'].items():
                counts[kind].update(data)
                bucket[kind+'_residuals'] += data['residual']
            bucket['counted_directions'] += 1
    counted = sum(r['counts'] is not None for r in rows)
    residual_totals = {kind: counts[kind]['residual'] for kind in ('algebraic', 'stateless')}
    residual_totals['total'] = sum(residual_totals.values())
    pairs = defaultdict(list)
    for row in rows:
        pairs[(row['group'], row['block'], row['before_step'], row['after_step'])].append(row)
    return {'expected_directions': expected, 'recorded_directions': len(rows),
            'missing_directions': expected-len(rows), 'statuses': dict(statuses),
            'counted_directions': counted, 'uncounted_directions': len(rows)-counted,
            'residual_totals': residual_totals,
            'polynomial_discharged': sum(r.get('polynomial_discharged') or 0 for r in rows),
            'zero_check_discharged': sum(r.get('zero_check_discharged') or 0 for r in rows),
            'conditional_obligations': sum(r.get('conditional_obligations') or 0 for r in rows),
            'directions_using_contract': sum(bool(r.get('assumptions')) for r in rows),
            'obligation_totals_on_counted_directions_only': counts,
            'pairs_both_directions_supported': sum(len(rs) == 2 and all(r['status'] in SUPPORTED for r in rs)
                                                    for rs in pairs.values()),
            'pairs_no_local_residuals_both_directions': sum(len(rs) == 2 and all(r['status'] == 'no-local-residuals' for r in rs)
                                                           for rs in pairs.values()),
            'by_pass': [passes[k] for k in sorted(passes)], 'input_hash_conflicts': sorted(changed_inputs),
            'scope': 'M2 mapping + M3 algebraic/stateless checks including configured zero-gadget rules; '
                     'contract-dependent discharges are conditional; no SMT, definition audit, or stateful IO proof',
            'NOT_an_equivalence_verdict': True}


def flatten(row):
    out = {k: row.get(k) for k in ('group', 'block', 'before_step', 'before_pass', 'after_step', 'after_pass',
                                  'direction', 'status', 'stage', 'seconds', 'error')}
    for kind in ('algebraic', 'stateless'):
        for key in ('total', *REASONS, 'residual'):
            out[f'{kind}_{key}'] = row['counts'][kind].get(key, 0) if row['counts'] else None
    out['unmapped_columns'] = len(row['mapping']['unresolved']) if row['mapping'] else None
    out['residual_total'] = (sum(c['residual'] for c in row['counts'].values())
                             if row['counts'] is not None else None)
    out['zero_check_enabled'] = row.get('zero_check_enabled', False)
    out['polynomial_matching_enabled'] = row.get('polynomial_matching_enabled', False)
    out['polynomial_discharged'] = row.get('polynomial_discharged')
    out['zero_check_discharged'] = row.get('zero_check_discharged')
    out['conditional_obligations'] = row.get('conditional_obligations')
    out['authorized_contracts'] = ','.join(row.get('authorized_contracts', []))
    return out


def residual_summary(summary):
    """Occurrence totals over counted directions, never estimates for missing maps."""
    totals = summary['residual_totals']
    return (f'residuals={totals["total"]} (algebraic={totals["algebraic"]}, '
            f'stateless={totals["stateless"]}; counted directions={summary["counted_directions"]}, '
            f'uncounted directions={summary["uncounted_directions"]})')


def render(rows, *, sort='residual', limit=30, only_unsupported=False,
           expected=None, elapsed=None, completed=None, output=None):
    rows = list(rows)
    # Totals describe the entire report, not just the displayed/filtered table.
    summary = summarize(rows, len(rows) if expected is None else expected)
    m3_display.results(rows, summary, sort=sort, limit=limit,
                       only_unsupported=only_unsupported, elapsed=elapsed,
                       completed=completed, output=output)


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('group', nargs='?', help='e.g. keccak; all selects every group under --root')
    parser.add_argument('block', nargs='?', type=int, help='omit for every block')
    parser.add_argument('--root', type=Path, default=Path('powdr-dumps'))
    parser.add_argument('--from-step', type=int)
    parser.add_argument('--to-step', type=int)
    parser.add_argument('--jobs', '-j', type=int, default=1)
    parser.add_argument('--timeout', type=float, default=10, help='wall seconds per direction (default 10)')
    parser.add_argument('--output', type=Path, help='new output directory (default: fresh runs/m3-sweep.*)')
    parser.add_argument('--report', type=Path, help='display a saved run without recomputing')
    parser.add_argument('--sort', choices=('residual', 'time', 'block'), default='residual')
    parser.add_argument('--limit', type=int, default=30, help='display rows, 0=all; never limits processing')
    parser.add_argument('--only-unsupported', action='store_true', help='display only uncounted/failing directions')
    parser.add_argument('--zero-check', action=argparse.BooleanOptionalAction, default=True,
                        help='enable syntactic zero-gadget discharge (default on); --no-zero-check restores baseline')
    parser.add_argument('--polynomial-matching', action=argparse.BooleanOptionalAction, default=True,
                        help='bounded polynomial discharge (default on); --no-polynomial-matching restores pre-integration checks')
    parser.add_argument('--reference-recv-bytes', action='store_true',
                        help='explicitly grant reference receive-byte bounds; dependent proofs remain conditional')
    args = parser.parse_args(argv)
    import math
    if args.jobs < 1 or not math.isfinite(args.timeout) or args.timeout <= 0 or args.limit < 0:
        parser.error('jobs/timeout must be positive and limit nonnegative')
    if any(n is not None and n < 0 for n in (args.block, args.from_step, args.to_step)):
        parser.error('block and steps must be nonnegative')
    if args.from_step is not None and args.to_step is not None and args.from_step > args.to_step:
        parser.error('--from-step must not exceed --to-step')
    if args.report:
        rows = [json.loads(line) for line in (args.report / 'results.jsonl').read_text().splitlines() if line]
        def saved_metadata(name):
            path = args.report / name
            return json.loads(path.read_text()) if path.is_file() else {}
        manifest = saved_metadata('manifest.json')
        metadata = saved_metadata('summary.json')
        m3_display.settings(manifest, args.report, saved=True)
        render(rows, sort=args.sort, limit=args.limit, only_unsupported=args.only_unsupported,
               expected=manifest.get('expected_directions', metadata.get('expected_directions', len(rows))),
               elapsed=metadata.get('elapsed_seconds'), completed=metadata.get('completed'))
        return 0
    if args.reference_recv_bytes and not args.zero_check:
        parser.error('--reference-recv-bytes requires --zero-check')
    if not args.group:
        parser.error('specify a group or --report')
    if args.group == 'all':
        directories = sorted(p for p in args.root.iterdir() if p.is_dir())
    else:
        directories = [group_dir(args.group, args.root)]
    tasks, inventory = discover(directories, block=args.block, first=args.from_step, last=args.to_step)
    tasks = [task | {'zero_check': args.zero_check, 'reference_recv_bytes': args.reference_recv_bytes,
                     'polynomial_matching': args.polynomial_matching}
             for task in tasks]
    if not inventory['blocks']:
        parser.error('No snapshots match the selection')
    if args.output:
        out = args.output.resolve()
        out.mkdir(parents=True, exist_ok=False)
    else:
        Path('runs').mkdir(exist_ok=True)
        out = Path(tempfile.mkdtemp(prefix='m3-sweep.', dir='runs')).resolve()
    root = Path(__file__).resolve().parents[2]
    files = [root / 'm3-sweep.py', Path(__file__),
             *(root / 'src/verify' / name for name in ('__init__.py', 'circuit_partition.py', 'witness_mapping.py',
                                                      'collapsed_witness.py', 'polynomial_normalization.py', 'polynomial_matching.py',
                                                      'cheap_obligations.py', 'zero_check.py', 'm3_display.py')),
             *(root / 'src/lens' / name for name in ('resolve.py', 'loader.py', 'diff.py', 'normalize.py', 'metrics.py'))]
    def git(*command):
        return subprocess.check_output(['git', '-C', str(root), *command], text=True).strip()
    manifest = {'created_at_utc': datetime.now(timezone.utc).isoformat(), 'git_head': git('rev-parse', 'HEAD'),
                'git_status': git('status', '--short'), 'python': sys.version,
                'sources_sha256': {str(p.relative_to(root)): sha256(p.read_bytes()).hexdigest() for p in files},
                'selection': {'directories': [str(p.resolve()) for p in directories], 'block': args.block,
                              'from_step': args.from_step, 'to_step': args.to_step},
                'jobs': args.jobs, 'direction_timeout_seconds': args.timeout, 'extra_memory_limit': None,
                'field': 'BabyBear', 'solver_invocations': 0, 'definition_audit': False,
                'zero_check_enabled': args.zero_check,
                'polynomial_matching_enabled': args.polynomial_matching,
                'authorized_contracts': [CONTRACT] if args.reference_recv_bytes else [],
                'mapping_implementation': 'current working-tree modules, including any local recipe support',
                'expected_pairs': len(tasks)//2, 'expected_directions': len(tasks),
                'inventory': inventory, 'tasks': tasks, 'NOT_an_equivalence_verdict': True}
    write_json(out / 'manifest.json', manifest)
    m3_display.settings(manifest, out)
    rows = []
    start, last_progress = perf_counter(), perf_counter()
    def checkpoint(complete=False):
        summary = summarize(rows, len(tasks))
        summary.update(completed=complete, elapsed_seconds=perf_counter()-start,
                       zero_check_enabled=args.zero_check,
                       polynomial_matching_enabled=args.polynomial_matching,
                       authorized_contracts=manifest['authorized_contracts'],
                       inventory_issue_count=len(inventory['issues']), selected_blocks=len(inventory['blocks']))
        write_json(out / 'summary.json', summary)
        return summary
    checkpoint()
    with (out / 'results.jsonl').open('x') as stream, (out / 'results.csv').open('x', newline='') as csvfile:
        writer = None
        try:
            for row in execute(tasks, jobs=args.jobs, timeout=args.timeout):
                rows.append(row)
                stream.write(json.dumps(row) + '\n')
                stream.flush()
                flat = flatten(row)
                if writer is None:
                    writer = csv.DictWriter(csvfile, fieldnames=list(flat))
                    writer.writeheader()
                writer.writerow(flat)
                csvfile.flush()
                if perf_counter()-last_progress >= 5:
                    summary = checkpoint()
                    m3_display.progress(summary)
                    last_progress = perf_counter()
        finally:
            checkpoint()
    summary = checkpoint(complete=True)
    render(rows, sort=args.sort, limit=args.limit, only_unsupported=args.only_unsupported,
           expected=len(tasks), elapsed=summary['elapsed_seconds'], completed=True)
    print(f'Reports: {out}\nExit 0 means the inventory run finished, NOT that circuits are equivalent.')
    return 0 if not inventory['issues'] and not summary['input_hash_conflicts'] and not any(
        r['status'] in {'error', 'worker-error', 'resource-error', 'input-error'} for r in rows) else 1
