"""Soundness of the LessThan rewrite (rule_based, 008 -> 009) with powdr's recipes as witnesses.

rule_based replaces OpenVM's LessThan gadget (b < (1, 0, 0, 0), i.e. b = 0)
with an is-zero pair. Today 009 still has the gadget's residue (marker
booleanity and the range-check send), so the markers and diff_val are shared
columns. Once powdr removes that residue they exist only in Before, and the
soundness mapping must choose them: 0 fails, and powdr's own IfEqZero recipe
(read by PolySolver's rule I) is the witness. These tests simulate the
cleanup in memory; the dump files are never touched.
"""

import copy
import dataclasses
import re

import pytest

from src.polysolver import variables
from src.redesign.check import check_step
from src.redesign.circuit import (
    Circuit,
    load_entry_pc,
    load_program,
    load_step,
    load_substitutions,
)

# The comparators rule_based rewrote: in 009 their columns appear only in
# booleanity constraints and the range-check send. 2106368's comparator 8
# keeps its whole gadget in 009 and must stay.
REWRITTEN = {"2104736": {"1", "2"}, "2106368": {"2"}}
GADGET = re.compile(r"^(?:diff_marker__\d_(\d+)|diff_val_(\d+))@")


def comparator(col: str) -> str | None:
    m = GADGET.match(col)
    return (m.group(1) or m.group(2)) if m else None


def cleaned(after: Circuit, rewritten: set[str]) -> Circuit:
    """009 without the rewritten comparators' residue; derived_columns kept."""

    def residue(e) -> bool:
        return any(comparator(v) in rewritten for v in variables(e))

    cons = [c for c in after.constraints if not residue(c)]
    buses = [
        bi for bi in after.bus_interactions
        if not any(residue(e) for e in [bi["mult"], *bi["args"]])
    ]
    cols = set()
    for e in cons:
        cols |= variables(e)
    for bi in buses:
        for e in [bi["mult"], *bi["args"]]:
            cols |= variables(e)
    return dataclasses.replace(
        after, constraints=cons, bus_interactions=buses, columns=frozenset(cols)
    )


@pytest.fixture(scope="module", params=sorted(REWRITTEN))
def step(request):
    block = request.param
    return dict(
        block=block,
        before=load_step("keccak", block, "008"),
        after=load_step("keccak", block, "009"),
        subs=load_substitutions("keccak", block),
        program=load_program("keccak", block),
        entry_pc=load_entry_pc("keccak", block),
    )


def soundness(step, after, **kw):
    return check_step(
        step["before"], after, step["subs"], ("soundness",),
        program=step["program"], entry_pc=step["entry_pc"], **kw,
    )[0]


def gadget_columns(step) -> list[str]:
    rewritten = REWRITTEN[step["block"]]
    return sorted(c for c in step["before"].columns if comparator(c) in rewritten)


def test_today_the_gadget_columns_are_shared(step):
    r = soundness(step, step["after"])
    assert "recipe" not in r.mapping.source.values()


def test_recipes_verify_the_step_after_cleanup(step):
    after = cleaned(step["after"], REWRITTEN[step["block"]])
    r = soundness(step, after)
    cols = gadget_columns(step)
    assert len(cols) == 5 * len(REWRITTEN[step["block"]])  # 4 markers and diff_val each
    assert all(r.mapping.source.get(c) == "recipe" for c in cols)
    undecided = [o for o in r.obligations if o.rung == "undecided"]
    assert undecided == []
    rungs = {o.rung for o in r.obligations if o.via_mapping}
    assert "cond-split" in rungs and "table-semantics" in rungs


def test_without_recipes_the_columns_stay_unmapped(step):
    after = cleaned(step["after"], REWRITTEN[step["block"]])
    r = soundness(step, after, use_recipe_witness=False)
    assert set(gadget_columns(step)) <= r.mapping.unmapped


def test_a_wrong_recipe_is_caught(step):
    # Flip one marker's hint: m3 := 1 where b3 = 0, else 0.
    after = cleaned(step["after"], REWRITTEN[step["block"]])
    after = dataclasses.replace(after, derived=copy.deepcopy(after.derived))
    m3 = next(c for c in gadget_columns(step) if c.startswith("diff_marker__3_"))
    (recipe,) = after.derived[m3]
    guard = recipe["IfEqZero"][0]
    after.derived[m3] = [{"IfEqZero": [guard, {"Constant": 1}, {"Constant": 0}]}]
    r = soundness(step, after)
    assert r.mapping.source.get(m3) == "recipe"
    undecided = [o for o in r.obligations if o.rung == "undecided"]
    assert undecided
    assert {o.reason for o in undecided} == {"cond case not proved"}
