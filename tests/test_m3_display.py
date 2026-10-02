"""Presentation preserves coverage, assumptions, and historical report semantics."""
from copy import deepcopy
from io import StringIO

from rich.console import Console

from src.verify import m3_display as display, m3_sweep as sweep


def row(block=1, unknown=False):
    return {
        'group': 'guest-demo', 'block': block, 'before_step': 8, 'after_step': 9,
        'before_pass': 'trivial_simp', 'after_pass': 'rule_based',
        'direction': 'completeness', 'status': 'unmapped' if unknown else 'local-residuals',
        'counts': None if unknown else {
            'algebraic': {'total': 100, 'residual': 2},
            'stateless': {'total': 50, 'residual': 3}},
        'inputs': {}, 'seconds': 1.25, 'stage': 'mapping', 'error': None,
        'polynomial_discharged': None if unknown else 10,
        'zero_check_discharged': None if unknown else 1,
        'conditional_obligations': 0, 'assumptions': [],
    }


def render(rows, width=120, **kwargs):
    stream = StringIO()
    sweep.render(rows, output=Console(file=stream, width=width, color_system=None,
                                     markup=False, highlight=False), **kwargs)
    return stream.getvalue()


def test_readable_totals_and_filter_do_not_mutate_rows():
    rows = [row(), row(2, unknown=True)]
    before = deepcopy(rows)
    text = render(rows, only_unsupported=True)
    assert '150 counted · 145 discharged · 5 residual' in text
    assert '1 have unknown counts (not zero)' in text
    assert 'Mapping incomplete' in text
    assert 'Polynomial matches' in text
    assert '—' in text
    assert rows == before


def test_narrow_terminal_has_labeled_counts_and_no_overflow():
    text = render([row()], width=80)
    assert 'Algebraic left: 2' in text
    assert 'Stateless left: 3' in text
    assert 'Polynomial proved: 10' in text
    assert max(map(len, text.splitlines())) <= 80


def test_conditional_warning_survives_filter_and_partial_run_is_explicit():
    conditional = row()
    conditional.update(conditional_obligations=1, assumptions=['recv-bytes'])
    text = render([conditional], only_unsupported=True, expected=3, completed=False)
    assert 'Partial run: 1/3' in text
    assert '2 missing' in text
    assert 'CONDITIONAL: 1 gadget discharges' in text
    assert 'NOT a whole-circuit equivalence verdict' in text


def test_unknown_counts_sort_before_locally_clear():
    clear = row()
    clear['status'] = 'no-local-residuals'
    for counts in clear['counts'].values():
        counts['residual'] = 0
    text = render([clear, row(2, unknown=True)], limit=1)
    details = text.split('Check details', 1)[1]
    assert 'Mapping incomplete' in details
    assert '2  008→009' in details


def test_progress_is_readable_without_raw_dictionaries():
    summary = sweep.summarize([row()], 2)
    summary['elapsed_seconds'] = 5.0
    stream = StringIO()
    display.progress(summary, output=Console(file=stream, width=120))
    text = stream.getvalue()
    assert '1/2 checks recorded' in text
    assert 'Residual obligations: 5 (2 algebraic; 3 stateless)' in text
    assert '{' not in text


def test_polynomial_categories_sum_across_rows_and_kinds_before_filtering():
    first, second = row(), row(2)
    reasons = display.POLYNOMIAL_REASONS
    for i, reason in enumerate(reasons, start=1):
        first['counts']['algebraic'][reason] = i
        second['counts']['stateless'][reason] = 2*i
    first['polynomial_discharged'] = 15
    second['polynomial_discharged'] = 30
    for options in ({'limit': 1}, {'only_unsupported': True}):
        text = render([first, second], **options)
        total_line = next(line for line in text.splitlines() if line.strip().startswith('Polynomial matches'))
        assert total_line.split()[-1] == '45'
        for i, reason in enumerate(reasons, start=1):
            line = next(line for line in text.splitlines() if reason in line)
            assert line.split()[-1] == str(3*i)
        assert 'Category not recorded' not in text
        assert 'not additional proofs' in text


def test_historical_polynomial_totals_without_category_counts():
    text = render([row()])
    line = next(line for line in text.splitlines() if 'Category not recorded' in line)
    assert line.split()[-1] == '10'


def test_zero_polynomial_categories_are_still_displayed():
    empty = row()
    empty['polynomial_discharged'] = 0
    text = render([empty])
    for reason in display.POLYNOMIAL_REASONS:
        line = next(line for line in text.splitlines() if reason in line)
        assert line.split()[-1] == '0'
