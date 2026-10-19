"""Builds the PolySolver for one direction. The only place the sweep makes one."""

from __future__ import annotations

from src.polysolver import Expr, PolySolver, VarTable

from .circuit import Circuit, byte_ranges


def reference_solver(
    table: VarTable,
    ref: Circuit,
    use_ranges: bool = True,
    hints: list[tuple[str, Expr]] = (),
    constants: bool = False,
    one_hot: bool = True,
) -> PolySolver:
    """Premises and ranges from the reference side only (the polarity rule).

    ``hints`` are candidate solved equations x = t over reference columns,
    tried in order. The solver checks each one and keeps only those that
    follow from what it already knows; a rejected hint costs completeness only.
    With ``constants``, the solver then also solves every premise that pins a
    variable to a constant (after the hints, so the two do not compete for a
    column). ``one_hot`` turns PolySolver's rule O on or off.
    """
    s = PolySolver(table, declared=ref.columns, one_hot=one_hot)
    for i, c in enumerate(ref.constraints):
        s.add_premise(c, tag=f"{ref.label}:c{i}")
    if use_ranges:
        for x, lo, hi in byte_ranges(ref):
            s.add_range(x, lo, hi, tag=f"{ref.label}:bytes:{x}")
    for x, t in hints:
        s.add_solved(x, t, tag=f"hint:{x}")
    if constants:
        s.solve_constants()
    return s
