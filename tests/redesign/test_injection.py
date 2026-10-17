"""Hand-made bug injections on the is-zero step keccak 2106332 008 -> 009.

Each test breaks one thing in a copy of the dumps (in memory; the files are
never touched) and checks that the redesign does not pass the broken step.
Without SMT rungs nothing can produce a counterexample yet, so "caught"
means "not verified", with the undecided obligations pointing at the edit.

Constraint numbers, from ``redesign check keccak 2106332 008 009 -v``:
  After  (009): c14 = (1 - cmp) * sum a,  c15 = f * sum a - cmp,  c0..c13 kept
  Before (008): c9..c12 = (1 - cmp) * a_i,  c13 = sum a_i * inv_i - cmp
"""

import copy

import pytest

from src.lens.loader import load, machine_of
from src.lens.resolve import resolve
from src.paths import POWDR_DUMPS_DIR
from src.redesign.check import check_step
from src.redesign.circuit import Circuit, load_substitutions

P = 2013265921
A = [f"a__{i}_3@{105 + i}" for i in range(4)]
CMP = "cmp_result_3@113"
MARKERS = {f"diff_inv_marker__{i}_3@{117 + i}" for i in range(4)}


@pytest.fixture(scope="module")
def dumps():
    def machine(step):
        path = resolve("keccak", "2106332", step, POWDR_DUMPS_DIR).path
        return machine_of(load(path))

    subs = load_substitutions("keccak", "2106332")
    return machine("008"), machine("009"), subs


def run(dumps, before_edit=None, after_edit=None):
    """Apply the edits to fresh copies, then check both directions."""
    before, after, subs = (copy.deepcopy(d) for d in dumps)
    if before_edit:
        before_edit(before)
    if after_edit:
        after_edit(after)
    cmp, snd = check_step(
        Circuit.from_machine("008_trivial_simp", before),
        Circuit.from_machine("009_rule_based", after),
        subs,
    )
    return cmp, snd


def undecided(report):
    return {o.name.split(":")[1] for o in report.obligations if o.rung == "undecided"}


def test_baseline(dumps):
    cmp, snd = run(dumps)
    assert undecided(cmp) == {"c14", "c15"}  # the gadget, by design (needs SMT)
    assert snd.verified
    assert snd.mapping.witnesses == [(sorted(MARKERS), "free_var_123@123")]


def test_a_drop_a_limb_from_the_after_sum(dumps):
    def edit(after):
        # (1 - cmp) * (a0 + a1 + a2): nothing forces a3 to zero any more.
        after["constraints"][14] = [[1, "-", CMP], "*", [[A[0], "+", A[1]], "+", A[2]]]

    _, snd = run(dumps, after_edit=edit)
    assert not snd.verified
    assert undecided(snd) == {"c12"}  # exactly (1 - cmp) * a3
    assert snd.counts()["nowrap-split"] == 3  # the other three limbs still split


def test_b_change_a_kept_constraint(dumps):
    def edit(after):
        after["constraints"][0] = [after["constraints"][0], "+", 1]

    cmp, snd = run(dumps, after_edit=edit)
    # Caught from both sides: neither c0 follows from the other circuit.
    assert "c0" in undecided(cmp) and not cmp.verified
    assert undecided(snd) == {"c0"} and not snd.verified


def test_c_break_the_witness(dumps):
    def edit(after):
        after["constraints"][15] = [after["constraints"][15], "+", 1]

    cmp, snd = run(dumps, after_edit=edit)
    assert not snd.verified
    assert snd.mapping.unmapped == MARKERS  # no witness exists now
    assert undecided(snd) == {"c13"}  # the gadget sum, which mentions them
    # Completeness cannot see this edit: f is opaque, so c15 was undecided anyway.
    assert undecided(cmp) == {"c14", "c15"}


def test_d_remove_the_byte_ranges(dumps):
    def edit(after):
        # The one receive that reads all four limbs becomes a send, so none
        # of a0..a3 gets a byte range.
        hits = [
            bi
            for bi in after["bus_interactions"]
            if bi["id"] == 1 and bi["mult"] == P - 1 and A[0] in bi["args"]
        ]
        assert len(hits) == 1 and set(A) <= set(hits[0]["args"])
        hits[0]["mult"] = 1

    _, snd = run(dumps, after_edit=edit)
    assert not snd.verified
    # The four products need the ranges (Lean: soundness_needs_noWrap).
    assert undecided(snd) == {"c9", "c10", "c11", "c12"}
    assert snd.counts()["normalize"] == 1  # the witness still works


def test_e_weaken_before(dumps):
    def edit(before):
        del before["constraints"][9]  # (1 - cmp) * a0

    cmp, snd = run(dumps, before_edit=edit)
    # A weaker Before is still implied by After, so soundness rightly passes.
    assert snd.verified and snd.counts()["nowrap-split"] == 3
    # The bug is in completeness: (1 - cmp) * sum a no longer follows. It was
    # already undecided, so the step stays not verified, never passed.
    assert not cmp.verified and "c14" in undecided(cmp)
