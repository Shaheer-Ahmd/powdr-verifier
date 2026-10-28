"""derive(): domains, flag groups and selectors pin flags; collapsed domains are substituted."""
from functools import reduce

import pytest

from src.polysolver import BABYBEAR, Implied, PolySolver, Unknown, VarTable

P = BABYBEAR

# An ALU instance: one flag per opcode, exactly one on, and the opcode code
# sub + 2*xor + 3*or + 4*and (add has weight 0).
FLAGS = ["add", "sub", "xor", "or", "and"]
WEIGHTS = {"sub": 1, "xor": 2, "or": 3, "and": 4}
# What every ALU pin rests on: the sum, the selector and each flag's booleanity.
ALU_TAGS = tuple(sorted(["sum", "sel", *(f"b_{x}" for x in FLAGS)]))


def add(*es):
    return reduce(lambda a, b: [a, "+", b], es)


def mul(*es):
    return reduce(lambda a, b: [a, "*", b], es)


def sub(a, b):
    return [a, "-", b]


def boolean(x):
    return mul(x, sub(x, 1))


def selector(weights, k):
    return sub(add(*[mul(w, x) for x, w in weights.items()]), k)


def solver(names, premises, ranges=(), run=True, **kw):
    """Premises tagged by name, then ranges, then derive()."""
    s = PolySolver(VarTable(), declared=names, **kw)
    for tag, e in premises:
        s.add_premise(e, tag=tag)
    for x, lo, hi in ranges:
        s.add_range(x, lo, hi, tag=f"r_{x}")
    if run:
        s.derive()
    return s


def alu(code, flags=FLAGS, weights=WEIGHTS, total=1, extra=(), names=(), run=True):
    """Booleanity, sum = total and the opcode selector = code, plus ``extra``."""
    premises = [(f"b_{x}", boolean(x)) for x in flags]
    premises += [("sum", sub(add(*flags), total)), ("sel", selector(weights, code))]
    premises += [(f"e{i}", e) for i, e in enumerate(extra)]
    return solver([*flags, *names], premises, run=run)


def pins(s):
    """Solved variables and their values (all constants here)."""
    return {s.table.name(v): value.get((), 0) for v, value in s._solved.items()}


def test_xor_instance():
    s = alu(2)
    assert pins(s) == {"add": 0, "sub": 0, "xor": 1, "or": 0, "and": 0}
    assert s.pinned == 5
    v = s.implies(sub("xor", 1))
    assert v.rule == "trivial" and v.solved == ALU_TAGS
    for x in ["add", "sub", "or", "and"]:
        assert s.implies(x).rule == "trivial"
    assert isinstance(s.implies("xor"), Unknown)


def test_nothing_without_the_pass():
    s = alu(2, run=False)
    assert s.pinned == 0 and not s._domains
    assert isinstance(s.implies(sub("xor", 1)), Unknown)


def test_weight_zero_flag():
    # The selector does not mention add, yet code 0 picks it.
    s = alu(0)
    assert pins(s) == {"add": 1, "sub": 0, "xor": 0, "or": 0, "and": 0}


def test_selector_written_negated_and_scaled():
    # 3 * (2 - sub - 2*xor - 3*or - 4*and) and 1 - sum: same zeros, same pins.
    neg = [3, "*", [2, "-", add(*[mul(w, x) for x, w in WEIGHTS.items()])]]
    premises = [(f"b_{x}", boolean(x)) for x in FLAGS]
    premises += [("sum", sub(1, add(*FLAGS))), ("sel", neg)]
    s = solver(FLAGS, premises)
    assert pins(s) == pins(alu(2))


def test_zero_sum_group():
    s = alu(0, total=0)
    assert pins(s) == dict.fromkeys(FLAGS, 0)


def test_tied_weights():
    # xor and or both have weight 2: either could be on, the others cannot.
    s = alu(2, weights={"sub": 1, "xor": 2, "or": 2, "and": 4})
    assert pins(s) == {"add": 0, "sub": 0, "and": 0}
    for x in ["xor", "or"]:
        assert s._domains[s.table.var(x)][:2] == (0, 1)
        assert isinstance(s.implies(x), Unknown)
    assert s.implies(sub(add("xor", "or"), 1)).rule == "normalize"  # the sum, reduced


def test_two_selectors_narrow_together():
    # Weights 1, 1, 2, 2 and 1, 2, 1, 2 (add 0 in both): only xor passes both.
    s = alu(1, weights={"sub": 1, "xor": 1, "or": 2, "and": 2},
            extra=[selector({"sub": 1, "xor": 2, "or": 1, "and": 2}, 2)])
    assert pins(s) == {"add": 0, "sub": 0, "xor": 1, "or": 0, "and": 0}
    assert "e0" in s.implies(sub("xor", 1)).solved


@pytest.mark.parametrize(
    "kw",
    [
        dict(total=2),  # two flags on: the selector no longer says which
        dict(weights={**WEIGHTS, "y": 1}, names=["y"]),  # selector leaves the group
    ],
    ids=["sum is 2", "selector mentions y"],
)
def test_declines(kw):
    s = alu(2, **kw)
    assert s.pinned == 0
    assert isinstance(s.implies(sub("xor", 1)), Unknown)


def test_group_needs_unit_coefficients():
    # add + 2*sub - 1 with booleans does say add = 1, but it is not a group.
    premises = [("b_add", boolean("add")), ("b_sub", boolean("sub"))]
    s = solver(["add", "sub"], premises + [("sum", sub(add("add", mul(2, "sub")), 1))])
    assert s.pinned == 0


def test_member_not_boolean():
    premises = [(f"b_{x}", boolean(x)) for x in FLAGS[:-1]]
    premises += [("sum", sub(add(*FLAGS), 1)), ("sel", selector(WEIGHTS, 2))]
    s = solver(FLAGS, premises)
    assert s.pinned == 0 and s.table.var("and") not in s._domains


@pytest.mark.parametrize("ternary", [False, True])
def test_ternary_flag_is_not_boolean(ternary):
    # f(f-1)(f-2) gives f {0, 1, 2}, not [0, 1], so f + g - 1 is not a group.
    f_is = mul("f", sub("f", 1), sub("f", 2)) if ternary else boolean("f")
    premises = [("f_is", f_is), ("b_g", boolean("g"))]
    premises += [("sum", sub(add("f", "g"), 1)), ("sel", sub(add("f", mul(2, "g")), 2))]
    s = solver(["f", "g"], premises)
    assert pins(s) == ({} if ternary else {"f": 0, "g": 1})


def test_contradiction_is_not_used():
    # The selectors ask for code 2 and code 3 at once: no flag can be on.
    s = alu(2, extra=[selector(WEIGHTS, 3)])
    assert all(lo <= hi for lo, hi, *_ in s._domains.values())


def test_premise_order_does_not_matter():
    premises = [(f"b_{x}", boolean(x)) for x in FLAGS]
    premises += [("sum", sub(add(*FLAGS), 1)), ("sel", selector(WEIGHTS, 2))]
    s = solver(list(reversed(FLAGS)), list(reversed(premises)))
    assert pins(s) == pins(alu(2))


def test_flag_hints_after_the_pass():
    # powdr's hints for one instance, in its file order: each equals a pin.
    s = alu(2)
    hints = [("and", 0), ("add", 0), ("sub", 0), ("xor", 1), ("or", 0)]
    rules = [s.add_solved(x, t, tag=f"h:{x}").rule for x, t in hints]
    assert rules == ["trivial"] * 5
    assert s.solved_accepted == s.solved_agreed == 5 and s.solved_rejected == 0
    assert s.solved_count == 5 and s.pinned == 5


def test_flag_pins_unlock_a_gated_premise():
    # (sum of flags) * (x - y): with the flags pinned it reads x - y.
    gated = mul(add(*FLAGS), sub("x", "y"))
    s = alu(2, extra=[gated], names=["x", "y"])
    v = s.add_solved("x", "y", tag="h:x")
    assert v.rule == "normalize" and v.premises == ("e0",) and v.solved == ALU_TAGS


def test_one_member_group():
    # a is pinned to 0 by a range, so the group reads b - 1.
    premises = [("b_a", boolean("a")), ("b_b", boolean("b")), ("sum", sub(add("a", "b"), 1))]
    s = solver(["a", "b"], premises, ranges=[("a", 0, 0)])
    assert pins(s) == {"a": 0, "b": 1}
    assert s.implies(sub("b", 1)).solved == ("b_b", "r_a", "sum")


def test_range_recheck_before_booleanity():
    # x - 1 is looked at before x(x - 1) gives x its range.
    s = solver(["x"], [("pin", sub("x", 1)), ("b_x", boolean("x"))])
    assert pins(s) == {"x": 1}


def test_range_recheck_after_a_pin():
    # The shape at keccak 2099512 step 000: x(x - 1) is gated by v, and v is
    # pinned only inside the pass. x is first skipped, then x = 0.
    premises = [
        ("x", "x"),
        ("b_v", boolean("v")),
        ("v_on", sub(1, "v")),
        ("b_x", mul("v", boolean("x"))),
    ]
    s = solver(["x", "v"], premises)
    assert pins(s) == {"v": 1, "x": 0}


@pytest.mark.parametrize("gate_on", [True, False])
def test_gated_group(gate_on):
    # v * (a + b - 1) is a group only once v = 1; the selector a + 2b - 2 then picks b.
    premises = [("b_a", boolean("a")), ("b_b", boolean("b")), ("b_v", boolean("v"))]
    premises += [("sum", mul("v", sub(add("a", "b"), 1))), ("sel", sub(add("a", mul(2, "b")), 2))]
    s = solver(["a", "b", "v"], premises, ranges=[("v", 1, 1)] if gate_on else [])
    assert pins(s) == ({"v": 1, "a": 0, "b": 1} if gate_on else {})


def test_screen_skips_premises_with_other_variables():
    # The gated premise mentions x, y, z, which are not 0-or-1 variables: the
    # pass never expands it, also not after the flags are pinned.
    extra = [mul(add(*FLAGS), add(mul("x", "y"), "z"))]
    s = alu(2, extra=extra, names=["x", "y", "z"])
    assert s.premises_expanded == alu(2).premises_expanded
    assert pins(s) == pins(alu(2))


def test_collapsed_range_is_substituted():
    s = solver(["x", "y"], [("p", sub(mul("x", "y"), 3))], ranges=[("x", 3, 3)], run=False)
    assert s.pinned == 1
    assert s.implies(sub("y", 1)).rule == "normalize"
    v = s.implies(sub("x", 3))
    assert v.rule == "trivial" and v.solved == ("r_x",)


def test_contradicting_range_is_ignored():
    s = solver(["x"], [], ranges=[("x", 0, 0)], run=False)
    s.add_range("x", 1, 1, tag="r2")
    assert s._domains[s.table.var("x")][:2] == (0, 0)
    assert pins(s) == {"x": 0}


def test_domains_only_intersect():
    s = solver(["x"], [], ranges=[("x", 0, 10)], run=False)
    x = s.table.var("x")
    # A set filtered by the range; its bounds are its min and max.
    assert s._reduce_domain(x, 0, s.p - 1, ["s"], values=frozenset({1, 5, 20}))
    assert s._domains[x][:3] == (1, 5, frozenset({1, 5}))
    assert not s._reduce_domain(x, 0, 10, ["t"])  # nothing new
    assert not s._reduce_domain(x, 0, 10, ["t"], values=frozenset({7}))  # contradiction: kept
    # A range filters the set too, down to one value.
    assert s._reduce_domain(x, 2, 10, ["u"])
    assert s._domains[x] == (5, 5, frozenset({5}), ["r_x", "s", "u"])
    assert s._collapsed == [x]


def test_rule_s_uses_booleanity_ranges():
    premises = [("b_a", boolean("a")), ("b_b", boolean("b")), ("g_sum", mul("g", add("a", "b")))]
    assert isinstance(solver(["a", "b", "g"], premises, run=False).implies(mul("g", "a")), Unknown)
    v = solver(["a", "b", "g"], premises).implies(mul("g", "a"))
    assert v.rule == "nowrap-split" and v.ranges == ("a", "b")


def test_agreeing_hint_is_implied():
    s = alu(2)
    assert isinstance(s.add_solved("xor", 1, tag="h"), Implied)
    v = s.add_solved("xor", 0, tag="h")
    assert isinstance(v, Unknown) and v.kind == "already-solved"


# ---------------------------------------------------------------- the domain step

HALF = (P + 1) // 2  # 1/2 in F_p


def values(s, x):
    d = s._domains.get(s.table.var(x))
    return d and d.values


def ternary(x):
    """x * ((x - 1) * (x - 2)), nested as OpenVM writes it."""
    return [x, "*", [sub(x, 1), "*", sub(x, 2)]]


def test_domains_from_written_factors():
    s = solver(["f", "c", "x"], [
        ("t_f", ternary("f")), ("c2", mul("c", sub("c", 255))), ("x", sub(mul(3, "x"), 6)),
    ])
    assert values(s, "f") == {0, 1, 2} and values(s, "c") == {0, 255}
    assert pins(s) == {"x": 2} and s.constants_solved == 1 and s.pinned == 0


def test_gated_domain_once_the_gate_is_pinned():
    s = solver(["e", "g"], [("t", mul("e", ternary("g"))), ("e", sub("e", 1))])
    assert values(s, "g") == {0, 1, 2}
    # A gate pinned to 0 makes the premise say nothing.
    s = solver(["e", "g"], [("t", mul("e", ternary("g"))), ("e", "e")])
    assert pins(s) == {"e": 0} and values(s, "g") is None


def test_is_load_domain_after_its_pins():
    # OpenVM's assert_tern(t) with t = mem_as + 2*is_load - 2*is_valid: once
    # mem_as = 2 and is_valid = 1 are pinned, t = 2*is_load.
    t = sub(add("mem_as", mul(2, "is_load")), mul(2, "is_valid"))
    s = solver(["mem_as", "is_load", "is_valid"], [
        ("tern", mul(t, sub(t, 1), sub(t, 2))), ("as", sub("mem_as", 2)), ("valid", sub(1, "is_valid")),
    ])
    assert pins(s) == {"mem_as": 2, "is_valid": 1}
    assert values(s, "is_load") == {0, HALF, 1}
    assert s._domains[s.table.var("is_load")].hi == HALF  # what rule S reads


def test_rule_s_reads_a_set_bound():
    premises = [("t_f", ternary("f")), ("b_b", boolean("b")), ("g_sum", mul("g", add("f", "b")))]
    v = solver(["f", "b", "g"], premises).implies(mul("g", "f"))
    assert v.rule == "nowrap-split" and v.ranges == ("b", "f")


def test_without_constants_a_flag_still_gets_its_value():
    # x - 7 is left alone, but f - 1 on a boolean f is what G did before. It is
    # looked at before f(f - 1), and again once f is in [0, 1].
    premises = [("f", sub("f", 1)), ("b_f", boolean("f")), ("x", sub("x", 7))]
    assert pins(solver(["f", "x"], premises, constants=False)) == {"f": 1}
    assert pins(solver(["f", "x"], premises, one_hot=False)) == {"f": 1, "x": 7}


def test_hint_swaps_a_group_member():
    # The group a + b + x - 1 gets c in place of x from the hint x := c. Only
    # then can the selector b + 2c - 2 use it: c is on.
    premises = [(f"b_{x}", boolean(x)) for x in "abcx"]
    premises += [("sum", sub(add("a", "b", "x"), 1)), ("eq", sub("x", "c")),
                 ("sel", sub(add("b", mul(2, "c")), 2))]
    s = solver(["a", "b", "c", "x"], premises)
    assert s.derive_pins == [0]
    assert isinstance(s.add_solved("x", "c", tag="h:x"), Implied)
    assert s.derive() == 3
    assert pins(s) == {"a": 0, "b": 0, "c": 1, "x": 1}
