"""Coverage accounting, isolation, discovery and real-dump M3 regressions."""
import json
import multiprocessing as mp
import os
from pathlib import Path
import time

import pytest

from src.verify import m3_sweep as sweep


def circuit(constraints=(), buses=(), derived=()):
    return {'constraints': list(constraints), 'bus_interactions': list(buses), 'derived_columns': list(derived)}


def dump(directory, step, data, block=12, suffix='test'):
    directory.mkdir(exist_ok=True)
    path = directory / f'apc_candidate_{block}_{step:03d}_{suffix}.json'
    path.write_text(json.dumps(data))
    return path


def pair(tmp_path, before, after):
    dump(tmp_path, 0, before)
    dump(tmp_path, 1, after)
    return sweep.discover([tmp_path])[0]


def test_cheap_counts_and_indices_include_buses_but_exclude_stateful(tmp_path):
    bus = {'id': 3, 'mult': 1, 'args': ['x@0', 8]}
    mem = {'id': 1, 'mult': 1, 'args': ['x@0']}
    tasks = pair(tmp_path, circuit(['x@0'], [bus, mem]),
                 circuit(['x@0', 'x@0', 0, ['x@0', '-', 1]], [bus, mem]))
    result = sweep.analyze(tasks[0])
    assert result['status'] == 'local-residuals'
    assert result['counts']['algebraic'] == {
        'total': 4, 'canonical-match': 1, 'cache': 1, 'trivial': 1, 'requires-proof': 1, 'residual': 1,
        **dict.fromkeys((*sweep.ZERO_REASONS, *sweep.POLYNOMIAL_REASONS), 0)}
    assert result['residual_indices'] == {'algebraic': [3], 'stateless': []}
    assert result['candidate_sizes']['stateful_excluded'] == 1
    assert result['mapping']['total']
    assert len(result['inputs']) == 2


def test_unmapped_is_not_zero_residuals(tmp_path):
    tasks = pair(tmp_path, circuit(['x@0']), circuit(['y@1']))
    row = sweep.analyze(tasks[0])
    assert row['status'] == 'unmapped'
    assert row['counts'] is None and row['residual_indices'] is None
    assert 'y@1' in row['mapping']['unresolved']
    assert sweep.flatten(row)['algebraic_residual'] is None
    assert sweep.flatten(row)['residual_total'] is None
    summary = sweep.summarize([row], 2)
    assert summary['missing_directions'] == 1 and summary['uncounted_directions'] == 1
    assert summary['residual_totals'] == {'algebraic': 0, 'stateless': 0, 'total': 0}
    assert summary['counted_directions'] == 0


def test_residual_totals_are_occurrences_not_direction_counts(tmp_path, capsys):
    tasks = pair(tmp_path, circuit(), circuit())
    first = sweep.analyze(tasks[0])
    second = sweep.analyze(tasks[1])
    for row, algebraic, stateless in ((first, 4, 2), (second, 1, 3)):
        row['status'] = 'local-residuals'
        row['counts'] = {'algebraic': {'total': algebraic, 'residual': algebraic},
                         'stateless': {'total': stateless, 'residual': stateless}}
    unknown = sweep.blank_result(tasks[0] | {'block': 13})
    unknown['status'] = 'unmapped'
    rows = [first, second, unknown]
    summary = sweep.summarize(rows, 4)
    assert summary['statuses']['local-residuals'] == 2
    assert summary['residual_totals'] == {'algebraic': 5, 'stateless': 5, 'total': 10}
    assert (summary['counted_directions'], summary['uncounted_directions'], summary['missing_directions']) == (2, 1, 1)
    assert sweep.flatten(first)['residual_total'] == 6
    assert 'residuals=10 (algebraic=5, stateless=5;' in sweep.residual_summary(summary)
    for options in ({'limit': 1}, {'only_unsupported': True}):
        sweep.render(rows, **options)
        output = capsys.readouterr().out
        assert '10 counted · 0 discharged · 10 residual' in output
        assert '1 have unknown counts (not zero)' in output


def test_saved_report_recomputes_totals_without_rewriting_or_running(tmp_path, monkeypatch, capsys):
    row = sweep.analyze(pair(tmp_path, circuit(['x@0']), circuit([['x@0', '-', 1]]))[0])
    report = tmp_path/'saved'
    report.mkdir()
    (report/'results.jsonl').write_text(json.dumps(row)+'\n')
    # Historical summary has no residual_totals field; report reads saved rows.
    (report/'summary.json').write_text('{"historical": true}\n')
    before = {p.name: p.read_bytes() for p in report.iterdir()}
    monkeypatch.setattr(sweep, 'execute', lambda *a, **k: pytest.fail('Must not execute'))
    assert sweep.main(['--report', str(report), '--only-unsupported']) == 0
    assert '1 counted · 0 discharged · 1 residual' in capsys.readouterr().out
    assert {p.name: p.read_bytes() for p in report.iterdir()} == before


def test_empty_residual_totals():
    summary = sweep.summarize([], 2)
    assert summary['residual_totals'] == {'algebraic': 0, 'stateless': 0, 'total': 0}
    assert summary['missing_directions'] == 2


def test_readable_progress_and_saved_json_include_residual_totals(tmp_path, monkeypatch, capsys):
    from itertools import count
    tasks = pair(tmp_path/'guest-demo', circuit(['x@0']), circuit([['x@0', '-', 1]]))
    rows = [sweep.analyze(task) for task in tasks]
    monkeypatch.setattr(sweep, 'execute', lambda *a, **k: iter(rows))
    # Force progress checkpoints deterministically, without sleeping.
    monkeypatch.setattr(sweep, 'perf_counter', count(0, 6).__next__)
    out = tmp_path/'run'
    assert sweep.main(['demo', '--root', str(tmp_path), '--output', str(out)]) == 0
    output = capsys.readouterr()
    assert 'Residual obligations: 1 (1 algebraic; 0 stateless)' in output.err
    assert 'Residual obligations: 2 (2 algebraic; 0 stateless)' in output.err
    assert not any(line.startswith('{') for line in output.out.splitlines())
    final = json.loads((out/'summary.json').read_text())
    assert final['residual_totals'] == {'algebraic': 2, 'stateless': 0, 'total': 2}
    assert json.loads((out/'summary.json').read_text())['residual_totals'] == final['residual_totals']
    assert 'residual_total' in (out/'results.csv').read_text().splitlines()[0]


def test_unsupported_partition_and_corrupt_json_are_distinct(tmp_path):
    tasks = pair(tmp_path, circuit(), circuit(buses=[{'id': 99, 'mult': 1, 'args': []}]))
    row = sweep.analyze(tasks[0])
    assert row['status'] == 'unsupported' and row['stage'] == 'partition'
    assert row['counts'] is None
    Path(tasks[0]['after_path']).write_text('{bad json')
    assert sweep.analyze(tasks[0])['status'] == 'input-error'


def test_discovery_excludes_auxiliary_dumps_and_never_bridges_gaps(tmp_path):
    for i in (0, 2, 3):
        dump(tmp_path, i, circuit())
    dump(tmp_path, 2, circuit(), suffix='test.powdr-opt-0')
    (tmp_path / 'apc_candidate_12_substitutions.json').write_text('[]')
    tasks, inventory = sweep.discover([tmp_path])
    assert [(t['before_step'], t['after_step']) for t in tasks] == [(2, 3), (2, 3)]
    assert inventory['issues'][0]['kind'] == 'step-gap'
    assert len(inventory['excluded_optimizer_auxiliary_files']) == 1
    tasks, inventory = sweep.discover([tmp_path], first=2, last=3)
    assert len(tasks) == 2 and not inventory['issues']
    dump(tmp_path, 2, circuit(), suffix='duplicate')
    tasks, inventory = sweep.discover([tmp_path])
    assert not tasks and inventory['issues'][0]['kind'] == 'duplicate-step'


def test_unsuffixed_final_snapshot_is_included(tmp_path):
    dump(tmp_path, 0, circuit())
    (tmp_path / 'apc_candidate_12_001.json').write_text(json.dumps(circuit()))
    tasks, _ = sweep.discover([tmp_path])
    assert len(tasks) == 2 and tasks[0]['after_pass'] == ''


def test_execute_records_each_direction_and_cli_report_does_not_rerun(tmp_path, monkeypatch):
    directory = tmp_path / 'guest-demo'
    pair(directory, circuit([0]), circuit())
    out = tmp_path / 'report'
    assert sweep.main(['demo', '--root', str(tmp_path), '--output', str(out), '-j', '2']) == 0
    summary = json.loads((out / 'summary.json').read_text())
    assert summary['completed'] and summary['recorded_directions'] == 2
    assert summary['pairs_no_local_residuals_both_directions'] == 1
    assert (out / 'results.csv').read_text().count('\n') == 3
    monkeypatch.setattr(sweep, 'execute', lambda *a, **k: pytest.fail('Report must not execute'))
    assert sweep.main(['--report', str(out), '--only-unsupported']) == 0
    with pytest.raises(FileExistsError):
        sweep.main(['demo', '--root', str(tmp_path), '--output', str(out)])


def sleep_worker(task, pipe):
    time.sleep(1)


def crash_worker(task, pipe):
    os._exit(7)


@pytest.mark.skipif('fork' not in mp.get_all_start_methods(), reason='Worker monkeypatch needs fork')
@pytest.mark.parametrize('worker,status', [(sleep_worker, 'timeout'), (crash_worker, 'worker-error')])
def test_worker_timeout_or_crash_never_disappears(tmp_path, monkeypatch, worker, status):
    tasks = pair(tmp_path, circuit(), circuit())
    monkeypatch.setattr(sweep, '_worker', worker)
    rows = list(sweep.execute(tasks, jobs=2, timeout=0.1))
    assert len(rows) == 2
    assert all(r['status'] == status and r['counts'] is None for r in rows)


def test_unexpected_exception_is_not_misclassified_as_unsupported(tmp_path, monkeypatch):
    tasks = pair(tmp_path, circuit(), circuit())
    def broken(*args):
        raise RuntimeError('injected bug')
    monkeypatch.setattr(sweep, 'build_mapping', broken)
    row = sweep.analyze(tasks[0])
    assert row['status'] == 'error' and 'injected bug' in row['traceback']


def test_input_changes_are_flagged(tmp_path):
    tasks = pair(tmp_path, circuit(), circuit())
    a = sweep.analyze(tasks[0])
    dump(tmp_path, 0, circuit([0]))
    b = sweep.analyze(tasks[1])
    summary = sweep.summarize([a, b], 2)
    assert summary['input_hash_conflicts'] == [tasks[0]['before_path']]


@pytest.mark.parametrize('block,first,last,forward,reverse', [
    (2106332, 8, 9, [14, 15], [9, 10, 11, 12, 13]),
    (2106332, 7, 8, [], []),
    (2099512, 14, 15, [], []),
])
def test_real_m3_examples(block, first, last, forward, reverse):
    root = Path(__file__).resolve().parents[1] / 'powdr-dumps/guest-keccak'
    if not root.is_dir():
        pytest.skip('Keccak dumps unavailable')
    tasks, inventory = sweep.discover([root], block=block, first=first, last=last)
    assert not inventory['issues'] and len(tasks) == 2
    for task, expected in zip(tasks, [forward, reverse], strict=True):
        row = sweep.analyze(task | {'zero_check': False, 'polynomial_matching': False})
        assert row['status'] in sweep.SUPPORTED
        assert row['residual_indices'] == {'algebraic': expected, 'stateless': []}


@pytest.mark.parametrize('args', [['--timeout', 'nan'], ['--timeout', '0'], ['-j', '0'],
                                  ['--from-step', '9', '--to-step', '8']])
def test_invalid_budgets_and_selections(args):
    with pytest.raises(SystemExit):
        sweep.main(['keccak', *args])


@pytest.mark.parametrize('flags,remaining,discharged,conditional', [
    (['--no-zero-check'], [2, 5], 0, 0),
    ([], [1, 4], 2, 0),
    (['--reference-recv-bytes'], [0, 0], 7, 5),
])
def test_zero_check_cli_modes_and_persistent_evidence(tmp_path, flags, remaining, discharged, conditional):
    from src.verify.zero_check import _sum, _zero, _weighted, check_certificate, CONTRACT
    from src.verify.witness_mapping import build_mapping
    from src.verify.collapsed_witness import add_collapsed_witnesses
    a = [f'a@{i}' for i in range(4)]
    v = [f'v@{i+4}' for i in range(4)]
    c, f = 'c@8', 'f@9'
    buses = [{'id': 1, 'mult': -1, 'args': [1, 52, *a, 0]}]
    before = circuit([*[_zero(c, x) for x in a], _weighted(a, v, c)], buses)
    after = circuit([_zero(c, _sum(a)), [[f, '*', _sum(a)], '-', c]], buses,
                    [[True, f, {'QuotientOrZero': [c, _sum(a)]}]])
    pair(tmp_path / 'guest-demo', before, after)
    out = tmp_path / 'report'
    assert sweep.main(['demo', '--root', str(tmp_path), '--output', str(out), '-j', '2',
                       '--no-polynomial-matching', *flags]) == 0
    manifest = json.loads((out / 'manifest.json').read_text())
    authorized = [CONTRACT] if conditional else []
    assert manifest['authorized_contracts'] == authorized
    assert manifest['zero_check_enabled'] == ('--no-zero-check' not in flags)
    assert 'src/verify/zero_check.py' in manifest['sources_sha256']
    assert 'src/verify/polynomial_normalization.py' in manifest['sources_sha256']
    rows = sorted([json.loads(line) for line in (out / 'results.jsonl').read_text().splitlines()],
                  key=lambda r: r['direction'])
    assert [r['counts']['algebraic']['residual'] for r in rows] == remaining
    assert [len(r['initial_residual_indices']['algebraic']) for r in rows] == [2, 5]
    for row in rows:
        assert row['authorized_contracts'] == authorized
        ref, cand = (before, after) if row['direction'] == 'completeness' else (after, before)
        mapping, _ = add_collapsed_witnesses(ref, cand, build_mapping(ref, cand))
        for proof in row['zero_check_proofs']:
            assert row['mapping']['witnesses'] == mapping.witnesses
            checked = check_certificate(before, after, mapping, row['zero_check_certificates'][proof['certificate']],
                                        allow_recv_bytes=bool(conditional))
            assert proof['claim'] in checked['claims']
        assert sweep.flatten(row)['conditional_obligations'] == row['conditional_obligations']
    summary = json.loads((out / 'summary.json').read_text())
    assert summary['zero_check_discharged'] == discharged
    assert summary['residual_totals'] == {'algebraic': sum(remaining), 'stateless': 0,
                                         'total': sum(remaining)}
    assert summary['conditional_obligations'] == conditional
    assert summary['directions_using_contract'] == (2 if conditional else 0)
    assert sweep.main(['--report', str(out)]) == 0


def test_contract_rejected_when_zero_check_disabled():
    with pytest.raises(SystemExit):
        sweep.main(['keccak', '--no-zero-check', '--reference-recv-bytes'])


def test_historical_reports_without_zero_check_fields_still_work(tmp_path, capsys):
    row = sweep.analyze(pair(tmp_path, circuit(), circuit())[0])
    for field in ('zero_check_enabled', 'zero_check_discharged', 'conditional_obligations',
                  'assumptions', 'authorized_contracts'):
        row.pop(field)
    for counts in row['counts'].values():
        for reason in sweep.ZERO_REASONS:
            counts.pop(reason)
    assert sweep.flatten(row)['algebraic_sum-individual-zero-equations'] == 0
    assert sweep.summarize([row], 1)['zero_check_discharged'] == 0
    sweep.render([row])
    assert 'CONDITIONAL on' not in capsys.readouterr().out


@pytest.mark.parametrize('contract,forward,reverse', [(False, [15], [9, 10, 11, 12]), (True, [], [])])
def test_real_gadget_zero_check_in_batch(contract, forward, reverse):
    root = Path(__file__).resolve().parents[1] / 'powdr-dumps/guest-keccak'
    if not root.is_dir():
        pytest.skip('Keccak dumps unavailable')
    tasks, _ = sweep.discover([root], block=2106332, first=8, last=9)
    assert len(tasks) == 2
    for task, expected in zip(tasks, [forward, reverse], strict=True):
        row = sweep.analyze(task | {'reference_recv_bytes': contract})
        assert row['status'] in sweep.SUPPORTED
        assert row['residual_indices'] == {'algebraic': expected, 'stateless': []}
