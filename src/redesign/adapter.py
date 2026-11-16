"""Builds the PolySolver for one direction. The only place the sweep makes one."""

from __future__ import annotations

from src.polysolver import Expr, PolySolver, VarTable

from . import lookups
from .circuit import Circuit, byte_ranges
from .execution import execution_facts

HINT_TAG = "hint:"  # tag prefix of powdr's substitutions, in verdicts and solved_log


def reference_solver(
    table: VarTable,
    ref: Circuit,
    use_ranges: bool = True,
    hints: list[tuple[str, Expr]] = (),
    constants: bool = False,
    one_hot: bool = True,
    case_split: bool = True,
    nowrap_pins: bool = True,
    use_lookup_ranges: bool = True,
    use_lookup_facts: bool = True,
    entry_pc: int | None = None,
    trust_execution: bool = True,
    program: dict[int, tuple[int, ...]] | None = None,
    use_program_facts: bool = True,
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
    variable's group (rule C). With ``nowrap_pins``, a premise that is a sum
    of ranged variables that cannot wrap pins each of them to 0 (rule S').
    The reference's own lookups hold for every witness (they are part of
    the reference circuit); lookups.assume reads them by their cases:
    ``use_lookup_ranges`` takes their bounds as ranges (a bare variable and
    a known nonzero multiplicity), ``use_lookup_facts`` their identities as
    premises, gated by the multiplicity (M4i).
    ``trust_execution`` adds the APC execution assumption (execution.py):
    entry at ``entry_pc``, every instruction runs, and each execution-bus
    send equals the next receive. These are trusted, not derived.
    ``use_program_facts`` (needs ``program``, the trusted PcLookup table):
    once a reference PcLookup's pc is known, the program's row at that pc
    gives mult * (arg - row) = 0 per argument (lookups.assume, which
    repeats while facts make new pcs known).
    """
    s = PolySolver(
        table,
        declared=ref.columns,
        constants=constants,
        one_hot=one_hot,
        case_split=case_split,
        nowrap_pins=nowrap_pins,
    )
    for i, c in enumerate(ref.constraints):
        s.add_premise(c, tag=f"{ref.label}:c{i}")
    if use_ranges:
        for x, lo, hi in byte_ranges(ref):
            s.add_range(x, lo, hi, tag=f"{ref.label}:bytes:{x}")
    if trust_execution:
        for name, e in execution_facts(ref, entry_pc, s.p):
            s.add_premise(e, tag=f"{ref.label}:exec:{name}")
    s.propagate()
    # The reference's lookups, read by lookups.cases: identities as premises,
    # bounds as ranges, PcLookup rows from the trusted program.
    lookups.assume(
        s,
        ref.label,
        ref.stateless,
        ranges=use_lookup_ranges,
        facts=use_lookup_facts,
        program=program if use_program_facts and program else None,
    )
    if hints:
        s.add_solved_all([(x, t, f"{HINT_TAG}{x}") for x, t in hints])
    return s

