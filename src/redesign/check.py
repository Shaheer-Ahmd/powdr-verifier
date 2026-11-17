"""Run the mapping and the sweep for one Before/After step, in either direction."""

from __future__ import annotations

from pathlib import Path

from src.polysolver import Expr, VarTable, variables

from .adapter import reference_solver
from .circuit import Circuit, load_entry_pc, load_program, load_step, load_substitutions
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
    program: dict[int, tuple[int, ...]] | None = None,
    use_nowrap_pins: bool = True,
    use_lookup_ranges: bool = True,
    use_lookup_facts: bool = True,
    use_table_rung: bool = True,
    entry_pc: int | None = None,
    trust_execution: bool = True,
    use_program_facts: bool = True,
    use_recipe_witness: bool = True,
) -> list[Report]:
    """Completeness: Before is the reference. Soundness: After is.

    ``program``: the block's own instructions by pc, trusted as the PcLookup
    table (see sweep's evaluated-program rung, and program facts as
    premises); None evaluates no PcLookup and gives no program facts.
    ``entry_pc`` and ``trust_execution``: the APC execution assumption
    (execution.py), on both sides alike.
    """
    trusted = dict(
        entry_pc=entry_pc,
        trust_execution=trust_execution,
        program=program,
        use_program_facts=use_program_facts,
    )
    table = VarTable()  # one per step, shared by both directions
    reports = []
    if "completeness" in directions:
        # Completeness only: the hints are about Before's columns. In the
        # soundness direction the same substitutions already define w.
        hints = step_hints(before, after, subs) if use_hints else []
        solver = reference_solver(
            table, before, use_ranges, hints, use_constants, use_one_hot, use_case_split,
            use_nowrap_pins,
            use_lookup_ranges,
            use_lookup_facts,
            **trusted,
        )
        m = completeness_mapping(before, after, subs)
        reports.append(sweep("completeness", before, after, m, solver, hints, program, use_table_rung))
    if "soundness" in directions:
        solver = reference_solver(
            table,
            after,
            use_ranges,
            constants=use_constants,
            one_hot=use_one_hot,
            case_split=use_case_split,
            nowrap_pins=use_nowrap_pins,
            use_lookup_ranges=use_lookup_ranges,
            use_lookup_facts=use_lookup_facts,
            **trusted,
        )
        m = soundness_mapping(after, before, subs, solver, use_recipe_witness)
        reports.append(sweep("soundness", after, before, m, solver, program=program, table_rung=use_table_rung))
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
    trust_program: bool = True,
    use_nowrap_pins: bool = True,
    use_lookup_ranges: bool = True,
    use_lookup_facts: bool = True,
    use_table_rung: bool = True,
    trust_execution: bool = True,
    use_program_facts: bool = True,
    use_recipe_witness: bool = True,
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
        load_program(group, block, root) if trust_program else None,
        use_nowrap_pins,
        use_lookup_ranges,
        use_lookup_facts,
        use_table_rung,
        load_entry_pc(group, block, root),
        trust_execution,
        use_program_facts,
        use_recipe_witness,
    )
