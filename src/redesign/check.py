"""Run the mapping and the sweep for one Before/After step, in either direction."""

from __future__ import annotations

from pathlib import Path

from src.polysolver import Expr, VarTable, variables

from .adapter import reference_solver
from .circuit import Circuit, load_step, load_substitutions
from .mapping import completeness_mapping, soundness_mapping
from .sweep import Report, sweep

DIRECTIONS = ("completeness", "soundness")


def step_hints(before: Circuit, after: Circuit, subs: dict) -> list[tuple[str, Expr]]:
    """powdr's substitutions for the columns this step removed, in file order.

    Each is a candidate solved equation x = t over Before's columns. They are
    hints only: PolySolver checks every one before using it. An entry whose t
    mentions a column Before does not have cannot be checked and is skipped.
    """
    gone = before.columns - after.columns
    return [
        (x, t)
        for x, t in subs.items()
        if x in gone and variables(t) <= before.columns
    ]


def check_step(
    before: Circuit,
    after: Circuit,
    subs: dict,
    directions=DIRECTIONS,
    use_ranges: bool = True,
    use_hints: bool = True,
    use_constants: bool = True,
    use_one_hot: bool = True,
    use_case_split: bool = True,
    use_two_value: bool = True,
) -> list[Report]:
    """Completeness: Before is the reference. Soundness: After is."""
    steps = {"case_split": use_case_split, "two_value": use_two_value}
    table = VarTable()  # one per step, shared by both directions
    reports = []
    if "completeness" in directions:
        # Completeness only: the hints are about Before's columns. In the
        # soundness direction the same substitutions already define w.
        hints = step_hints(before, after, subs) if use_hints else []
        solver = reference_solver(
            table, before, use_ranges, hints, use_constants, use_one_hot, **steps
        )
        m = completeness_mapping(before, after, subs)
        reports.append(sweep("completeness", before, after, m, solver, hints))
    if "soundness" in directions:
        solver = reference_solver(
            table,
            after,
            use_ranges,
            constants=use_constants,
            one_hot=use_one_hot,
            **steps,
        )
        m = soundness_mapping(after, before, subs, solver) # <- Polysolver used to find missing witnesses
        reports.append(sweep("soundness", after, before, m, solver))
    return reports


def check(
    group: str,
    block: str,
    step_from: str,
    step_to: str,
    directions=DIRECTIONS,
    use_ranges: bool = True,
    root: Path | None = None,
    use_hints: bool = True,
    use_constants: bool = True,
    use_one_hot: bool = True,
    use_case_split: bool = True,
    use_two_value: bool = True,
) -> list[Report]:
    before = load_step(group, block, step_from, root)
    after = load_step(group, block, step_to, root)
    subs = load_substitutions(group, block, root)
    return check_step(
        before,
        after,
        subs,
        directions,
        use_ranges,
        use_hints,
        use_constants,
        use_one_hot,
        use_case_split,
        use_two_value,
    )
