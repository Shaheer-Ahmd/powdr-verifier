"""Builds the PolySolver for one direction. The only place the sweep makes one."""

from __future__ import annotations

from src.polysolver import Expr, PolySolver, VarTable

from .circuit import Circuit, byte_ranges

HINT_TAG = "hint:"  # tag prefix of powdr's substitutions, in verdicts and solved_log


def reference_solver(
    table: VarTable,
    ref: Circuit,
    use_ranges: bool = True,
    hints: list[tuple[str, Expr]] = (),
    constants: bool = False,
    one_hot: bool = True,
    case_split: bool = True,
    two_value: bool = False,
) -> PolySolver:
    """Premises and ranges from the reference side only (the polarity rule).

    The solver first derives domains from the premises and pins what they
    decide (derive): with ``constants`` a premise x - c, with ``one_hot``
    booleanity, flag groups and selectors, with ``case_split`` a case split
    over finite domains (with ``two_value`` also over two-value ones).
    ``hints`` are candidate solved equations x = t over reference columns,
    tried in order. The solver checks each one and keeps only those that
    follow from what it already knows (a hint equal to a pin is kept too); a
    rejected hint costs completeness only. Then it derives again, from the
    premises the hints changed.
    """
    s = PolySolver(
        table,
        declared=ref.columns,
        constants=constants,
        one_hot=one_hot,
        case_split=case_split,
        two_value=two_value,
    )
    for i, c in enumerate(ref.constraints):
        s.add_premise(c, tag=f"{ref.label}:c{i}")
    if use_ranges:
        for x, lo, hi in byte_ranges(ref):
            s.add_range(x, lo, hi, tag=f"{ref.label}:bytes:{x}")
    s.derive()
    for x, t in hints:
        s.add_solved(x, t, tag=f"{HINT_TAG}{x}")
    s.derive()  # a hint can turn a premise into x - c
    return s
