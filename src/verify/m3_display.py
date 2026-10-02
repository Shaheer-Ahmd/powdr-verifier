"""Human-readable M3 presentation, independent of saved schemas and proof rules."""
import sys

from rich import box
from rich.console import Console
from rich.table import Table

from .polynomial_matching import POLYNOMIAL_REASONS


LABELS = {
    'no-local-residuals': 'Locally clear', 'local-residuals': 'Needs proof',
    'unmapped': 'Mapping incomplete', 'unsupported': 'Unsupported input',
    'timeout': 'Time limit reached', 'input-error': 'Input/read error',
    'resource-error': 'Resource error', 'worker-error': 'Worker failed',
    'error': 'Internal error', 'pending': 'Not finished',
}
SUPPORTED = {'no-local-residuals', 'local-residuals'}


def console(*, stderr=False):
    stream = sys.stderr if stderr else sys.stdout
    return Console(file=stream, width=None if stream.isatty() else 120,
                   markup=False, highlight=False)


def table(*columns):
    result = Table(box=box.SIMPLE, header_style='bold', padding=(0, 1))
    for i, label in enumerate(columns):
        result.add_column(label, overflow='fold',
                          justify='left' if i == 0 or (i == 1 and len(columns) > 2) else 'right')
    return result


def settings(manifest, out, *, saved=False, output=None):
    output = output or console()
    output.print('\nM3 solver-free checks — '+('saved run' if saved else 'starting sweep'), style='bold cyan')
    output.print(f'Reports: {out}')
    output.print('One check = one pass pair and one direction. No SMT solver is run.')
    if not manifest:
        output.print('Historical run settings unavailable; counts are reconstructed from saved rows.')
        return
    output.print(f'{len(manifest["inventory"]["blocks"]):,} blocks · '
                 f'{manifest["expected_pairs"]:,} pass pairs · '
                 f'{manifest["expected_directions"]:,} checks · {manifest["jobs"]} workers')
    stages = ['canonical / trivial / cached']
    if manifest.get('polynomial_matching_enabled'):
        stages.append('polynomial')
    if manifest.get('zero_check_enabled'):
        stages.append('zero gadget')
    output.print('Pipeline: '+' → '.join([*stages, 'report residuals']))
    output.print(f'Time limit: {manifest["direction_timeout_seconds"]:g}s per check, including setup.')
    output.print('Receive-byte contract: '+('GRANTED — dependent proofs are conditional.'
                 if manifest.get('authorized_contracts') else 'not granted.'), style='yellow')
    issues = len(manifest['inventory']['issues'])
    if issues:
        output.print(f'WARNING: {issues:,} inventory issues; see manifest.json.', style='yellow')


def progress(summary, *, output=None):
    output = output or console(stderr=True)
    done, expected = summary['recorded_directions'], summary['expected_directions']
    clear = summary['statuses'].get('no-local-residuals', 0)
    left = summary['residual_totals']
    output.print(f'[{summary["elapsed_seconds"]:.0f}s] {done:,}/{expected:,} checks recorded — '
                 f'{clear:,} locally clear; {done-clear:,} need attention')
    output.print(f'  Residual obligations: {left["total"]:,} '
                 f'({left["algebraic"]:,} algebraic; {left["stateless"]:,} stateless). '
                 f'Unknown-count checks: {summary["uncounted_directions"]:,}.')


def results(rows, summary, *, sort='residual', limit=30, only_unsupported=False,
            elapsed=None, completed=None, output=None):
    output = output or console()
    done, expected = summary['recorded_directions'], summary['expected_directions']
    clear = summary['statuses'].get('no-local-residuals', 0)
    output.print('\nResults', style='bold cyan')
    state = 'Complete' if done == expected and completed is not False else 'Partial run'
    output.print(f'{state}: {done:,}/{expected:,} checks recorded'+
                 (f' in {elapsed:.1f}s.' if elapsed is not None else '.'))
    output.print(f'{clear:,} locally clear · {done-clear:,} need attention · '
                 f'{expected-done:,} missing', style='bold')
    for status, n in sorted(summary['statuses'].items(), key=lambda item: (item[0] != 'no-local-residuals', item[0])):
        output.print(f'  {LABELS.get(status, status):24} {n:>7,}')
    if summary['input_hash_conflicts']:
        output.print('WARNING: input hashes changed during this run; results are not one consistent snapshot.', style='red')

    counts = summary['obligation_totals_on_counted_directions_only']
    total = sum(c.get('total', 0) for c in counts.values())
    left = summary['residual_totals']['total']
    poly, zero = summary['polynomial_discharged'], summary['zero_check_discharged']
    output.print('\nObligations — entire report, not just displayed rows', style='bold cyan')
    output.print(f'{total:,} counted · {total-left:,} discharged · {left:,} residual', style='bold')
    output.print(f'Counts available for {summary["counted_directions"]:,} checks; '
                 f'{summary["uncounted_directions"]:,} have unknown counts (not zero).')
    breakdown = table('Result', 'Obligations')
    for label, n in (
        ('Canonical / trivial / cached', total-left-poly-zero),
        ('Polynomial matches', poly), ('Zero-gadget proofs', zero),
        ('Algebraic residuals', summary['residual_totals']['algebraic']),
        ('Stateless lookup residuals', summary['residual_totals']['stateless'])):
        breakdown.add_row(label, f'{n:,}')
        if label == 'Polynomial matches':
            categorized = 0
            for reason in POLYNOMIAL_REASONS:
                category_total = sum(c.get(reason, 0) for c in counts.values())
                categorized += category_total
                breakdown.add_row(f'  {reason}', f'{category_total:,}')
            if categorized < poly:
                breakdown.add_row('  Category not recorded', f'{poly-categorized:,}')
    output.print(breakdown)
    output.print('Indented polynomial categories are included in Polynomial matches, not additional proofs.')
    output.print('Counts are occurrences across passes/directions, not unique constraints. Residual means unproved, not a bug.')
    if summary['conditional_obligations'] or summary['directions_using_contract']:
        output.print(f'CONDITIONAL: {summary["conditional_obligations"]:,} gadget discharges across '
                     f'{summary["directions_using_contract"]:,} checks depend on the receive-byte contract.', style='yellow')

    selected = [r for r in rows if not only_unsupported or r['status'] not in SUPPORTED]
    def remaining(row):
        return sum(c['residual'] for c in row['counts'].values()) if row['counts'] is not None else -1
    keys = {
        'residual': lambda r: (r['status'] == 'no-local-residuals', -remaining(r),
                               r['group'], r['block'], r['before_step'], r['direction']),
        'time': lambda r: -r['seconds'],
        'block': lambda r: (r['group'], r['block'], r['before_step'], r['direction']),
    }
    shown = sorted(selected, key=keys[sort])[:limit or None]
    output.print(f'\nCheck details — showing {len(shown):,} of {len(selected):,}'+
                 (' unsupported/error checks' if only_unsupported else '')+f' (sort: {sort})', style='bold cyan')
    output.print('Completeness = Before → After; soundness = After → Before. Use --limit 0 to show all selected checks.')
    groups = {r['group'] for r in rows}
    if len(groups) == 1:
        output.print(f'Group: {next(iter(groups))}')
    narrow = output.width < 110
    details = (table('Check', 'Outcome', 'Obligations') if narrow else
               table('Block / passes / direction', 'Outcome', 'Algebraic\nleft', 'Stateless\nleft',
                     'Polynomial\nproved', 'Gadget\nproved', 'Time'))
    for row in shown:
        check = (f'{row["group"]} / ' if len(groups) > 1 else '')+str(row['block'])
        check += f'  {row["before_step"]:03d}→{row["after_step"]:03d}\n{row["direction"]}'
        check += f'\n{row["before_pass"] or "(unnamed)"} → {row["after_pass"] or "(unnamed)"}'
        numbers = ([f'{row["counts"][kind]["residual"]:,}' for kind in ('algebraic', 'stateless')]
                   if row['counts'] is not None else ['—', '—'])
        numbers += [f'{row[name]:,}' if row.get(name) is not None else '—'
                    for name in ('polynomial_discharged', 'zero_check_discharged')]
        label = LABELS.get(row['status'], row['status'])
        if row.get('assumptions') or row.get('conditional_obligations'):
            label += '\nCONDITIONAL'
        if narrow:
            values = '\n'.join(f'{name}: {value}' for name, value in zip(
                ('Algebraic left', 'Stateless left', 'Polynomial proved', 'Gadget proved'), numbers, strict=True))
            details.add_row(check, label+f'\n{row["seconds"]:.2f}s', values)
        else:
            details.add_row(check, label, *numbers, f'{row["seconds"]:.2f}s')
    output.print(details)
    for row in shown:
        if row.get('error'):
            output.print(f'{row["group"]}/{row["block"]} {row["before_step"]:03d}→{row["after_step"]:03d} '
                         f'{row["direction"]} — {row["stage"]}: {row["error"]}', style='yellow')
    output.print('“Left” means residual obligations. “—” means not counted or not recorded, never zero.')
    output.print('Locally clear means no local residuals under the recorded assumptions.')
    output.print('\nScope: no SMT, derived-definition audit, or stateful IO proof. '
                 'This is NOT a whole-circuit equivalence verdict.', style='bold yellow')
