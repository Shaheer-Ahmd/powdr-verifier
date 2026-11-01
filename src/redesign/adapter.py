"""Builds the PolySolver for one direction. The only place the sweep makes one."""

from __future__ import annotations

from src.polysolver import Expr, PolySolver, VarTable

from .circuit import Circuit, byte_ranges

HINT_TAG = "hint:"  # tag prefix of powdr's substitutions, in verdicts and hint_log


def reference_solver(
    table: VarTable,
    ref: Circuit,
    use_ranges: bool = True,
    hints: list[tuple[str, Expr]] = (),
    constants: bool = False,
    one_hot: bool = True,
    case_split: bool = True,
) -> PolySolver:
    """Premises and ranges from the reference side only (the polarity rule).

    The solver first propagates: it derives domains from the premises and
    pins what they decide, with ``constants`` from a premise x - c, with
    ``one_hot`` from booleanity, flag groups and selectors.
    ``hints`` are candidate solved equations x = t over reference columns,
    tried in order. The solver checks each one and keeps only those that
    follow from what it already knows (a hint equal to a pin is kept too); a
    rejected hint costs completeness only. With ``case_split``, a hint about
    a variable with three values that the check cannot decide first gets a
    case split over the variable's group (rule C). Then the solver
    propagates again, from the premises the hints changed.
    """
    s = PolySolver(
        table,
        declared=ref.columns,
        constants=constants,
        one_hot=one_hot,
        case_split=case_split,
    )
    for i, c in enumerate(ref.constraints):
        s.add_premise(c, tag=f"{ref.label}:c{i}")
    if use_ranges:
        for x, lo, hi in byte_ranges(ref):
            s.add_range(x, lo, hi, tag=f"{ref.label}:bytes:{x}")
    s.propagate()
    for x, t in hints:
        s.add_hint(x, t, tag=f"{HINT_TAG}{x}")
    s.propagate()  # a hint can turn a premise into x - c
    return s
