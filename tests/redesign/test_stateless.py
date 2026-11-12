"""Stateless bus interactions (lookups) as obligations, discharged canonically."""

import collections
import copy

import pytest

from src.lens.loader import load, machine_of
from src.lens.resolve import resolve
from src.paths import POWDR_DUMPS_DIR
from src.redesign import mapping as mapping_module
from src.redesign.check import check, check_step
from src.redesign.circuit import STATELESS_BUSES, Circuit, load_step, load_substitutions


def bus_obligations(report, rung=None):
    return [
        o for o in report.obligations if o.kind == "bus" and rung in (None, o.rung)
    ]


def test_stateless_excludes_stateful_buses():
    c = load_step("keccak", "2106332", "009")
    ids = {bi["id"] for bi in c.bus_interactions}
    assert {0, 1} <= ids  # the dump has memory and execution-bridge traffic
    assert {bi["id"] for bi in c.stateless} <= STATELESS_BUSES
    assert len(c.stateless) == sum(bi["id"] in STATELESS_BUSES for bi in c.bus_interactions)


def test_is_zero_step_lookups_unchanged():
    for r in check("keccak", "2106332", "008", "009"):
        lookups = bus_obligations(r)
        assert lookups and all(o.rung == "identical" for o in lookups), r.direction
    _, snd = check("keccak", "2106332", "008", "009")
    assert snd.verified  # adding lookups does not break the soundness result


def test_noop_step_verified_with_lookups():
    for r in check("keccak", "2099512", "014", "015"):
        assert r.verified and r.counts("bus")["identical"] > 0, r.direction


@pytest.mark.parametrize("trust_program", [False, True])
def test_removed_constant_lookups_are_evaluated(trust_program):
    # remove_disconnected drops 14 lookups with constant args: 5 PcLookup,
    # 2 VariableRangeChecker, 7 BitwiseLookup (lens diff: "bus: -14"). The
    # range and bitwise ones are table rows. A PcLookup is evaluated only
    # against the block's own instructions, under its own rung, and not at
    # all unless the program is trusted.
    cmp, snd = check("keccak", "2099512", "005", "006", trust_program=trust_program)
    assert cmp.verified  # every After lookup is still in Before
    assert snd.verified == trust_program
    before = load_step("keccak", "2099512", "005")
    outcome = collections.Counter(
        (before.stateless[int(o.name.split(":b")[1])]["id"], o.rung, o.reason)
        for o in bus_obligations(snd)
        if o.rung in ("undecided", "evaluated", "evaluated-program")
    )
    pc = (2, "evaluated-program", "") if trust_program else (
        2, "undecided", "bus: pc_lookup not trusted")
    assert outcome == {(6, "evaluated", ""): 7, (3, "evaluated", ""): 2, pc: 5}


def test_lookup_only_columns_get_witness_zero(monkeypatch):
    calls = []
    real = mapping_module.find_uniform_witness

    def spy(solver, base_w, unknowns, targets, shortlist):
        calls.append(list(targets))
        return real(solver, base_w, unknowns, targets, shortlist)

    monkeypatch.setattr(mapping_module, "find_uniform_witness", spy)
    _, snd = check("keccak", "2099512", "003", "004")
    assert all(calls_targets for calls_targets in calls)  # never an empty target list
    lookup_only = {
        "reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0@10",
        "reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0@11",
    }
    # They are only range-checked, so the mapping picks 0 for them and the
    # range checks [0, bits] are table rows.
    assert not snd.mapping.unmapped
    assert {c: snd.mapping.defs[c] for c in lookup_only} == dict.fromkeys(lookup_only, 0)
    assert {snd.mapping.source[c] for c in lookup_only} == {"lookup-only zero"}
    assert not snd.mapping.witnesses
    assert not bus_obligations(snd, "undecided")
    # remove_trivial dropped them because their multiplicity is 0: trivial now
    # that their columns are mapped (evaluated, had it been nonzero).
    names = {o.name for o in bus_obligations(snd) if o.rung in ("trivial", "evaluated")}
    assert len(names) >= 2
    assert not snd.counts("constraint")["undecided"]  # constraints are unaffected


@pytest.fixture(scope="module")
def is_zero_dumps():
    def machine(step):
        return machine_of(load(resolve("keccak", "2106332", step, POWDR_DUMPS_DIR).path))

    return machine("008"), machine("009"), load_substitutions("keccak", "2106332")


def _completeness_with(dumps, edit):
    before, after, subs = (copy.deepcopy(d) for d in dumps)
    edit(after)
    (cmp,) = check_step(
        Circuit.from_machine("008", before),
        Circuit.from_machine("009", after),
        subs,
        ("completeness",),
    )
    return cmp


def _first_lookup(machine, bus):
    return next(bi for bi in machine["bus_interactions"] if bi["id"] == bus)


def test_changed_lookup_arg_is_caught(is_zero_dumps):
    def edit(after):
        vrc = _first_lookup(after, 3)  # VariableRangeChecker [x, bits]
        # A narrower width: not implied. (A wider one is, by table semantics.)
        vrc["args"][1] = vrc["args"][1] - 1

    cmp = _completeness_with(is_zero_dumps, edit)
    stuck = bus_obligations(cmp, "undecided")
    assert [o.reason for o in stuck] == ["bus: args differ"]
    assert not cmp.verified


def test_zero_multiplicity_lookup_is_trivial(is_zero_dumps):
    def edit(after):
        vrc = _first_lookup(after, 3)
        vrc["mult"] = 0
        vrc["args"][1] = vrc["args"][1] + 1  # would not match, but asserts nothing

    cmp = _completeness_with(is_zero_dumps, edit)
    assert len(bus_obligations(cmp, "trivial")) == 1
    assert not bus_obligations(cmp, "undecided")


def test_constant_lookup_not_a_row_is_reported(is_zero_dumps):
    def edit(after):
        vrc = _first_lookup(after, 3)
        vrc["args"] = [300, 8]  # 300 does not fit in 8 bits

    cmp = _completeness_with(is_zero_dumps, edit)
    stuck = bus_obligations(cmp, "undecided")
    assert [o.reason for o in stuck] == ["bus: constant args not a row"]


def test_constant_lookup_row_is_evaluated(is_zero_dumps):
    def edit(after):
        bw = _first_lookup(after, 6)
        bw["args"] = [12, 10, 12 ^ 10, 1]  # z = x xor y on bytes

    cmp = _completeness_with(is_zero_dumps, edit)
    assert len(bus_obligations(cmp, "evaluated")) == 1
    assert not bus_obligations(cmp, "undecided")


def test_congruence_through_solved_equations():
    # 013 -> 014 (solver): lookup args were rewritten by powdr's substitutions;
    # with the hints solved, each one is congruent to a Before lookup.
    (cmp,) = check("keccak", "2100224", "013", "014", ("completeness",))
    cong = bus_obligations(cmp, "congruence")
    assert len(cong) >= 1000
    assert all(o.detail.startswith("013_") for o in cong)  # names the Before lookup J
    (plain,) = check(
        "keccak", "2100224", "013", "014", ("completeness",), use_hints=False
    )
    assert len(bus_obligations(plain, "congruence")) < len(cong)  # the hints matter
