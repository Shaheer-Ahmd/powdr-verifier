"""Builds the PolySolver for one direction. The only place the sweep makes one."""

from __future__ import annotations

from src.polysolver import Expr, PolySolver, VarTable

from .circuit import Circuit, byte_ranges, lookup_ranges
from .execution import execution_facts
from .tables import PC_LOOKUP, constant, lookup_facts, program_facts

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
    ``use_lookup_ranges`` also takes ranges from the reference's own range
    and bitwise lookups with a constant nonzero multiplicity: such a lookup
    is part of the reference circuit, so it holds for every witness.
    ``use_lookup_facts`` adds the polynomial identities of the reference's
    bitwise and range lookups (tables.lookup_facts, M4i), gated by their
    multiplicity, as premises.
    ``trust_execution`` adds the APC execution assumption (execution.py):
    entry at ``entry_pc``, every instruction runs, and each execution-bus
    send equals the next receive. These are trusted, not derived.
    ``use_program_facts`` (needs ``program``, the trusted PcLookup table):
    once propagation makes a reference PcLookup's pc a constant, the
    program's row at that pc gives mult * (arg - row) = 0 per argument
    (tables.program_facts); repeated while new pcs become constant.
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
    if use_lookup_ranges:
        for x, lo, hi in lookup_ranges(ref):
            s.add_range(x, lo, hi, tag=f"{ref.label}:lookup:{x}")
    if use_lookup_facts:

        def is_bit(e: Expr) -> bool:  # by the ranges and premises so far
            iv = s.interval(e)
            return iv is not None and iv[1] <= 1

        for j, bi in enumerate(ref.stateless):
            for k, e in enumerate(lookup_facts(bi, s.p, is_bit)):
                s.add_premise(e, tag=f"{ref.label}:b{j}:fact{k}")
    if trust_execution:
        for name, e in execution_facts(ref, entry_pc, s.p):
            s.add_premise(e, tag=f"{ref.label}:exec:{name}")
    s.propagate()
    if use_program_facts and program:
        _add_program_facts(s, ref, program)
    if hints:
        s.add_solved_all([(x, t, f"{HINT_TAG}{x}") for x, t in hints])
    return s


def _add_program_facts(s: PolySolver, ref: Circuit, program: dict) -> None:
    """Add program_facts for each PcLookup whose pc propagation made constant.

    A fact can pin flags that make another lookup's pc constant (a branch
    target), so this repeats until a round adds nothing.
    """
    lookups = [(j, bi) for j, bi in enumerate(ref.stateless) if bi["id"] == PC_LOOKUP]
    done: set[int] = set()
    while True:
        added = False
        for j, bi in lookups:
            if j in done or not bi["args"]:
                continue
            nf = s.normal_form(bi["args"][0])
            pc = constant(nf) if nf is not None else None
            if pc is None:
                continue
            done.add(j)
            m = s.normal_form(bi["mult"])
            facts = program_facts(bi, pc, program, constant(m) if m is not None else None)
            for k, e in enumerate(facts):
                s.add_premise(e, tag=f"{ref.label}:b{j}:program{k}")
                added = True
        if not added:
            return
        s.propagate()
