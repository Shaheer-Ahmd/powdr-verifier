"""Mapping and sweep on real guest-keccak dumps, plus a synthetic mapping gap."""
import pytest

from src.redesign.check import check, check_step
from src.redesign.circuit import Circuit, byte_ranges, load_step, substitute
from src.redesign.mapping import MissingDefinition

# The is-zero merge of rule_based (008 -> 009); the last five use 1 - cmp.
IS_ZERO = ["2099672", "2105000", "2105468", "2105476", "2106332",
           "2099556", "2103324", "2103880", "2105076", "2105108"]


def _by_rung(report, rung):
    return [o for o in report.obligations if o.rung == rung]


def test_mapping_finds_the_merged_markers():
    _, snd = check("keccak", "2106332", "008", "009")
    markers = [f"diff_inv_marker__{i}_3@{117 + i}" for i in range(4)]
    assert snd.mapping.witnesses == [(markers, "free_var_123@123")]
    assert all(snd.mapping.source[m] == "witness" for m in markers)
    assert not snd.mapping.unmapped


@pytest.mark.parametrize("block", IS_ZERO)
def test_is_zero_soundness_needs_no_solver(block):
    _, snd = check("keccak", block, "008", "009")
    assert snd.verified
    assert len(_by_rung(snd, "normalize")) == 1  # the gadget sum, via the witness
    assert len(_by_rung(snd, "nowrap-split")) == 4  # (1 - cmp) * a_i, via byte ranges
    assert not _by_rung(snd, "undecided")


@pytest.mark.parametrize("block", IS_ZERO)
def test_is_zero_soundness_without_ranges(block):
    (snd,) = check("keccak", block, "008", "009", ("soundness",), use_ranges=False)
    assert len(_by_rung(snd, "undecided")) == 4  # exactly the four products
    assert not _by_rung(snd, "nowrap-split")


@pytest.mark.parametrize("block", IS_ZERO)
def test_is_zero_completeness_by_design(block):
    cmp, _ = check("keccak", block, "008", "009")
    undecided = _by_rung(cmp, "undecided")
    assert len(undecided) == 2  # needs SMT: a sum of premises, and opaque QuotientOrZero
    assert any("opaque" in o.detail for o in undecided)
    assert all(o.rung in ("identical", "undecided") for o in cmp.obligations)


def test_noop_step_both_directions():
    for r in check("keccak", "2099512", "014", "015"):
        assert r.verified, r.direction


def test_completeness_missing_definition_raises():
    before = Circuit.from_machine("b", {"constraints": [["x@0", "-", 1]], "bus_interactions": []})
    after = Circuit.from_machine("a", {"constraints": [["y@1", "-", "x@0"]], "bus_interactions": []})
    with pytest.raises(MissingDefinition, match="y@1"):
        check_step(before, after, subs={}, directions=("completeness",))


def test_completeness_uses_substitutions():
    before = Circuit.from_machine("b", {"constraints": [["x@0", "-", 1]], "bus_interactions": []})
    after = Circuit.from_machine("a", {"constraints": [["y@1", "-", 1]], "bus_interactions": []})
    (r,) = check_step(before, after, subs={"y@1": "z@2", "z@2": "x@0"},
                      directions=("completeness",))
    assert r.mapping.source["y@1"] == "substitution"  # composed through z@2
    assert r.verified


@pytest.mark.parametrize(
    "one_hot, hints, undecided",
    [(True, (6339, 4564), 282), (False, (4285, 6618), 1150)],
    ids=["rule O", "no rule O"],
)
def test_opcode_flag_hints_by_rule_o(one_hot, hints, undecided):
    # solver pass: an opcode flag hint follows only from booleanity, the sum
    # of the flags and the opcode selector together (rule O). The flags then
    # ungate the timestamp checks. With rule O, what stays undecided is in the
    # shift chip.
    (cmp,) = check("keccak", "2100224", "002", "003", ("completeness",),
                   use_one_hot=one_hot)
    assert (cmp.hints_accepted, cmp.hints_rejected) == hints
    assert cmp.counts("constraint")["undecided"] == undecided


def test_soundness_opposite_polarity_is_normalized():
    _, snd = check("keccak", "2099556", "008", "009")
    assert snd.mapping.witnesses and snd.verified


def test_byte_ranges_are_bare_receive_limbs():
    after = load_step("keccak", "2106332", "009")
    names = {x for x, _, _ in byte_ranges(after)}
    assert {"a__0_3@105", "a__3_3@108"} <= names


def test_substitute_does_not_mutate():
    e = [["x", "*", "y"], "+", ["-", "x"]]
    assert substitute(e, {"x": 3}) == [[3, "*", "y"], "+", ["-", 3]]
    assert e == [["x", "*", "y"], "+", ["-", "x"]]
