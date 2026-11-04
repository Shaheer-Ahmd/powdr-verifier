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
) -> PolySolver:
    """Premises and ranges from the reference side only (the polarity rule).

    The solver first propagates: it derives domains from the premises and
    pins what they decide, with ``constants`` from a premise x - c, with
    ``one_hot`` from booleanity, flag groups and selectors.
    ``hints`` are candidate solved equations x = t over reference columns,
    given to the solver in one call and tried in order. The solver keeps
    only those that follow from what it knows (a hint equal to a pin is kept
    too), runs D and O after each one it keeps, and tries a rejected hint
    again when something it reads changes. A hint rejected in the end costs
    completeness only. With ``case_split``, a hint about a variable with
    three values that the check cannot decide gets a case split over the
    variable's group (rule C).
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
    if hints:
        s.add_solved_all([(x, t, f"{HINT_TAG}{x}") for x, t in hints])
    return s
