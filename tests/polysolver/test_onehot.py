"""Rule O: a flag is 0 or 1 because of booleanity, a sum, and selectors."""
from functools import reduce

import pytest

from src.polysolver import BABYBEAR, Implied, PolySolver, Unknown, VarTable

P = BABYBEAR

# An ALU instance: one flag per opcode, exactly one on, and the opcode code
# sub + 2*xor + 3*or + 4*and (add has weight 0).
FLAGS = ["add", "sub", "xor", "or", "and"]
WEIGHTS = {"sub": 1, "xor": 2, "or": 3, "and": 4}


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


def alu(code, flags=FLAGS, weights=WEIGHTS, total=1, extra=(), names=()):
    """Booleanity, sum = total and the opcode selector = code, plus ``extra``."""
    s = PolySolver(VarTable(), declared=[*flags, *names])
    for x in flags:
        s.add_premise(boolean(x), tag=f"b_{x}")
    s.add_premise(sub(add(*flags), total), tag="sum")
    s.add_premise(selector(weights, code), tag="sel")
    for i, e in enumerate(extra):
        s.add_premise(e, tag=f"e{i}")
    return s


def test_xor_instance():
    s = alu(2)
    v = s.implies(sub("xor", 1))
    assert v.rule == "one-hot"
    # The group first, then the selector, then every member's booleanity.
    assert v.premises[:2] == ("sum", "sel")
    assert sorted(v.premises[2:]) == sorted(f"b_{x}" for x in FLAGS)
    for x in ["add", "sub", "or", "and"]:
        assert s.implies(x).rule == "one-hot"
    assert isinstance(s.implies("xor"), Unknown)
    assert isinstance(s.implies(sub("and", 1)), Unknown)


def test_rule_o_can_be_left_out():
    s = PolySolver(VarTable(), declared=FLAGS, one_hot=False)
    for x in FLAGS:
        s.add_premise(boolean(x), tag=f"b_{x}")
    s.add_premise(sub(add(*FLAGS), 1), tag="sum")
    s.add_premise(selector(WEIGHTS, 2), tag="sel")
    v = s.implies(sub("xor", 1))
    assert isinstance(v, Unknown) and "O:" not in v.note


def test_weight_zero_flag():
    # The selector does not mention add, yet code 0 picks it.
    s = alu(0)
    assert s.implies(sub("add", 1)).rule == "one-hot"
    for x in ["sub", "xor", "or", "and"]:
        assert s.implies(x).rule == "one-hot"


def test_selector_written_negated_and_scaled():
    # 3 * (2 - sub - 2*xor - 3*or - 4*and): same zeros, same verdicts.
    neg = [3, "*", [2, "-", add(*[mul(w, x) for x, w in WEIGHTS.items()])]]
    s = PolySolver(VarTable(), declared=FLAGS)
    for x in FLAGS:
        s.add_premise(boolean(x), tag=f"b_{x}")
    s.add_premise(sub(1, add(*FLAGS)), tag="sum")
    s.add_premise(neg, tag="sel")
    assert s.implies(sub("xor", 1)).rule == "one-hot"
    assert s.implies("or").rule == "one-hot"


def test_zero_sum_group():
    s = alu(0, total=0)
    for x in FLAGS:
        assert s.implies(x).rule == "one-hot"
        assert isinstance(s.implies(sub(x, 1)), Unknown)


def test_tied_weights():
    # xor and or both have weight 2: either could be on, the others cannot.
    s = alu(2, weights={"sub": 1, "xor": 2, "or": 2, "and": 4})
    for x in ["add", "sub", "and"]:
        assert s.implies(x).rule == "one-hot"
    for x in ["xor", "or"]:
        assert isinstance(s.implies(x), Unknown)
        v = s.implies(sub(x, 1))
        assert isinstance(v, Unknown) and "could be on: or, xor" in v.note


def test_two_selectors_narrow_together():
    # Weights 1, 1, 2, 2 and 1, 2, 1, 2 (add 0 in both): only xor passes both.
    s = alu(1, weights={"sub": 1, "xor": 1, "or": 2, "and": 2},
            extra=[selector({"sub": 1, "xor": 2, "or": 1, "and": 2}, 2)])
    v = s.implies(sub("xor", 1))
    assert v.rule == "one-hot" and v.premises[:3] == ("sum", "sel", "e0")


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
    assert isinstance(s.implies(sub("xor", 1)), Unknown)
    assert isinstance(s.implies("and"), Unknown)


def test_group_needs_unit_coefficients():
    # add + 2*sub - 1 with booleans does say add = 1, but it is not a group.
    s = PolySolver(VarTable(), declared=["add", "sub"])
    for x in ["add", "sub"]:
        s.add_premise(boolean(x), tag=f"b_{x}")
    s.add_premise(sub(add("add", mul(2, "sub")), 1), tag="sum")
    assert isinstance(s.implies(sub("add", 1)), Unknown)
    assert isinstance(s.implies("sub"), Unknown)


def test_member_not_boolean():
    s = PolySolver(VarTable(), declared=FLAGS)
    for x in FLAGS[:-1]:
        s.add_premise(boolean(x), tag=f"b_{x}")
    s.add_premise(sub(add(*FLAGS), 1), tag="sum")
    s.add_premise(selector(WEIGHTS, 2), tag="sel")
    v = s.implies("add")
    assert isinstance(v, Unknown) and "no and^2 - and premise" in v.note


@pytest.mark.parametrize("ternary", [False, True])
def test_ternary_flag_is_not_boolean(ternary):
    # f(f-1)(f-2): f may be 2, so the sum no longer says one flag is on.
    s = PolySolver(VarTable(), declared=["f", "g"])
    f_is = mul("f", sub("f", 1), sub("f", 2)) if ternary else boolean("f")
    s.add_premise(f_is, tag="f_is")
    s.add_premise(boolean("g"), tag="b_g")
    s.add_premise(sub(add("f", "g"), 1), tag="sum")
    s.add_premise(sub("g", 1), tag="sel")
    assert isinstance(s.implies("f"), Unknown if ternary else Implied)


def test_contradiction_is_not_used():
    # The selectors ask for code 2 and code 3 at once: no flag can be on.
    s = alu(2, extra=[selector(WEIGHTS, 3)])
    v = s.implies("and")
    assert isinstance(v, Unknown) and "contradict" in v.note


def test_only_flag_values():
    s = alu(2)
    v = s.implies(sub("xor", 2))
    assert isinstance(v, Unknown) and "O: not x = 0 or x = 1" in v.note
    assert isinstance(s.implies(sub("xor", "or")), Unknown)


@pytest.mark.parametrize("order", [FLAGS, list(reversed(FLAGS))])
def test_flag_hints_in_powdr_order(order):
    # powdr's hints for one instance, in its file order. Each is checked by
    # add_solved; the last follows by rule N, once xor = 1 leaves "or" alone
    # in the sum. The reversed interning order makes the shrunk selector
    # 2*xor + 3*or - 2 monic in a different flag.
    s = PolySolver(VarTable(), declared=order)
    for x in FLAGS:
        s.add_premise(boolean(x), tag=f"b_{x}")
    s.add_premise(sub(add(*FLAGS), 1), tag="sum")
    s.add_premise(selector(WEIGHTS, 2), tag="sel")
    hints = [("and", 0), ("add", 0), ("sub", 0), ("xor", 1), ("or", 0)]
    rules = [s.add_solved(x, t, tag=f"h:{x}").rule for x, t in hints]
    assert rules == ["one-hot"] * 4 + ["normalize"]
    assert s.solved_count == 5 and s.solved_rejected == 0


def test_solved_tags_are_reported():
    s = alu(2)
    assert isinstance(s.add_solved("add", 0, tag="h:add"), Implied)
    v = s.implies(sub("xor", 1))
    # The sum now reads sub + xor + or + and - 1 only because of h:add.
    assert v.rule == "one-hot" and v.solved == ("h:add",)
    assert "b_add" not in v.premises


def test_flag_hints_unlock_a_gated_premise():
    # (sum of flags) * (x - y): only once the flags are known is it x - y.
    gated = mul(add(*FLAGS), sub("x", "y"))
    s = alu(2, extra=[gated], names=["x", "y"])
    assert isinstance(s.add_solved("x", "y", tag="h:x"), Unknown)
    for x, t in [("and", 0), ("add", 0), ("sub", 0), ("xor", 1), ("or", 0)]:
        assert isinstance(s.add_solved(x, t, tag=f"h:{x}"), Implied)
    v = s.add_solved("x", "y", tag="h:x")
    assert v.rule == "normalize" and v.premises == ("e0",)
    assert v.solved == tuple(sorted(f"h:{x}" for x in FLAGS))
