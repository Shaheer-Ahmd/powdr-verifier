"""Rule C in derive(): a variable with one value in every combination of its group that fits is pinned."""
from functools import reduce

import pytest

from src.polysolver import BABYBEAR, PolySolver, VarTable

P = BABYBEAR
HALF = (P + 1) // 2  # 1/2 in F_p


def add(*es):
    return reduce(lambda a, b: [a, "+", b], es)


def mul(*es):
    return reduce(lambda a, b: [a, "*", b], es)


def sub(a, b):
    return [a, "-", b]


def boolean(x):
    return mul(x, sub(x, 1))


def ternary(x):
    """x * ((x - 1) * (x - 2)), nested as OpenVM writes it."""
    return [x, "*", [sub(x, 1), "*", sub(x, 2)]]


def tern(t):
    """OpenVM's assert_tern(t): t * (t - 1) * (t - 2) = 0."""
    return mul(t, sub(t, 1), sub(t, 2))


def solver(names, premises, **kw):
    """Premises tagged by their keys, then derive()."""
    s = PolySolver(VarTable(), declared=names, **kw)
    for tag, e in premises.items():
        s.add_premise(e, tag=tag)
    s.derive()
    return s


def pins(s):
    """Solved variables and their values (all constants here)."""
    return {s.table.name(v): value.get((), 0) for v, value in s._solved.items()}


def toy(extra=None, names=(), **kw):
    """Two ternary flags with f + g = 2 and f^2 + g = 4: only f = 2, g = 0 fits."""
    return solver(["f", "g", *names], {
        "t_f": ternary("f"),
        "t_g": ternary("g"),
        "sum": sub(add("f", "g"), 2),
        "dec": sub(add(mul("f", "f"), "g"), 4),
        **(extra or {}),
    }, **kw)


# ---------------------------------------------------------------- the search

def test_toy_pins_both_flags():
    s = toy()
    assert pins(s) == {"f": 2, "g": 0} and s.case_splits == 1 and s.pinned == 2
    v = s.implies(sub("f", 2))
    assert v.rule == "trivial" and v.solved == ("dec", "sum", "t_f", "t_g")


def test_two_fits_that_agree_on_nothing_pin_nothing():
    s = solver(["f", "g"], {"t_f": ternary("f"), "t_g": ternary("g"), "sum": sub(add("f", "g"), 2)})
    assert pins(s) == {} and s.case_splits == 1
    # It stops at the second fit: f = 0 (g = 0, 1, 2), then f = 1 (g = 0, 1).
    assert s.case_split_nodes == 7


def test_variables_every_fit_agrees_on_are_pinned():
    # f + g = 2 has three fits, and h*(f + g) = 4 gives h = 2 in each.
    tern3 = {f"t_{x}": ternary(x) for x in "fgh"}
    s = solver(["f", "g", "h"], {**tern3, "sum": sub(add("f", "g"), 2),
                                 "hsum": sub(mul("h", add("f", "g")), 4)})
    assert pins(s) == {"h": 2}
    # Agreeing in the first two fits is not enough: 2k = f(f - 1) is 0 for
    # f = 0 and f = 1, but 1 for f = 2.
    tern3 = {f"t_{x}": ternary(x) for x in "fgk"}
    s = solver(["f", "g", "k"], {**tern3, "sum": sub(add("f", "g"), 2),
                                 "k": sub(mul(2, "k"), mul("f", sub("f", 1)))})
    assert pins(s) == {} and s.case_splits == 1


def test_contradiction_pins_nothing():
    s = toy(extra={"eq": sub("f", "g")})  # f = g = 1 is the only sum, and fails dec
    assert pins(s) == {} and s.case_splits == 1 and s.case_split_unsat == 1


def test_group_over_the_cap():
    names = [f"x{i}" for i in range(8)]  # 3^8 cases
    premises = {f"t{i}": ternary(x) for i, x in enumerate(names)}
    s = solver(names, {**premises, "sum": sub(add(*names), 16)})
    assert pins(s) == {} and s.case_split_capped == 1 and s.case_splits == 0


def test_premise_with_a_column_without_domain_is_skipped():
    s = toy(extra={"data": mul(sub("f", 1), sub("w", "r"))}, names=["w", "r"])
    assert pins(s) == {"f": 2, "g": 0}
    assert s.implies(sub("w", "r")).rule == "normalize"  # f = 2 ungated it


def test_many_fits_cost_less_than_all_of_them():
    # Six ternary flags summing to 6: 141 combinations fit, and none pins a variable.
    names = [f"m{i}" for i in range(6)]
    premises = {f"t{i}": ternary(x) for i, x in enumerate(names)}
    s = solver(names, {**premises, "sum": sub(add(*names), 6)})
    assert pins(s) == {} and s.case_splits == 1
    assert s.case_split_nodes < 1092  # a full enumeration tries 1092


def quad(x):
    """x * (x - 1) * (x - 2) * (x - 3): four values."""
    return mul(x, sub(x, 1), sub(x, 2), sub(x, 3))


def halves(x):
    """x * (2x - 1) * (x - 1): 0, 1/2 or 1, like is_load."""
    return mul(x, sub(mul(2, x), 1), sub(x, 1))


@pytest.mark.parametrize(
    "domain, mid, split",
    [(boolean, 1, False), (quad, 1, False), (ternary, 1, True), (halves, HALF, True)],
    ids=["two values", "four values", "0, 1, 2", "0, 1/2, 1"],
)
def test_only_three_value_domains_are_split(domain, mid, split):
    # a = b and a + b = 2 * mid: one combination fits, if rule C looks.
    s = solver(["a", "b"], {"d_a": domain("a"), "d_b": domain("b"), "eq": sub("a", "b"),
                            "sum": sub(add("a", "b"), mul(2, mid))})
    assert s.case_splits == int(split)
    assert pins(s) == ({"a": mid, "b": mid} if split else {})


# ---------------------------------------------------------------- the loop

def test_a_pin_can_make_a_new_coupling_premise():
    # a1 + a2 = 2 has three fits. f*y + a1 - a2 couples a1 and a2 only once
    # f = 0 is pinned (by f + h = 2, h^2 + f = 4); then a1 = a2 = 1.
    s = solver(["a1", "a2", "f", "h", "y"], {
        **{f"t_{x}": ternary(x) for x in ["a1", "a2", "f", "h"]},
        "sum_a": sub(add("a1", "a2"), 2),
        "sum_f": sub(add("f", "h"), 2),
        "dec_f": sub(add(mul("h", "h"), "f"), 4),
        "link": add(mul("f", "y"), sub("a1", "a2")),
    })
    assert pins(s) == {"a1": 1, "a2": 1, "f": 0, "h": 2}
    assert s.case_splits == 3  # a's group, f's, then a's again


def test_a_domain_found_later_requeues_its_premises():
    # f + g - 4 is looked at before g has a domain (its premise is gated by e),
    # and again once it has one: then f = g = 2.
    s = solver(["e", "f", "g"], {
        "c": sub(add("f", "g"), 4),
        "t_g": mul("e", ternary("g")),
        "t_f": ternary("f"),
        "e": sub("e", 1),
    })
    assert pins(s) == {"e": 1, "f": 2, "g": 2}


# ---------------------------------------------------------------- load/store

FLAGS = ["f0", "f1", "f2", "f3"]


def selectors():
    """One per opcode variant: a flag at 2 (f(f-1)/2), or two flags at 1 (fi*fj)."""
    out = [mul(f, sub(f, 1), HALF) for f in FLAGS]
    return out + [mul(a, b) for i, a in enumerate(FLAGS) for b in FLAGS[i + 1:]]


def load_store(code=1, loads=(0, 4), **kw):
    """The chip's 9 premises (variant k has code k + 1), plus data gated by f0."""
    total = add(*FLAGS)
    sel = selectors()
    t = sub(add("mem_as", mul(2, "is_load")), mul(2, "is_valid"))
    return solver([*FLAGS, "is_load", "is_valid", "mem_as", "w", "r"], {
        **{f"t_{f}": ternary(f) for f in FLAGS},
        "sum": mul(total, sub(total, 1), sub(total, 2)),
        "gate": mul(sub(total, 1), sub(total, 2), "is_valid"),
        "opcode": sub(add(*[mul(k + 1, e) for k, e in enumerate(sel)]), code),
        "load": sub("is_load", add(*[sel[k] for k in loads])),
        "tern": tern(t),
        "as": sub("mem_as", 2),
        "valid": sub(1, "is_valid"),
        "data": mul(sub("f0", 1), sub("w", "r")),
    }, **kw)


def test_load_store_pinned_before_the_hints():
    s = load_store()
    flags = {"f0": 2, "f1": 0, "f2": 0, "f3": 0}
    assert pins(s) == {"mem_as": 2, "is_valid": 1, **flags, "is_load": 1}
    assert s.case_splits == 1  # the four flags and is_load, in one search
    # powdr's hints, in its order: each agrees with a pin, and the data
    # premise, ungated by f0 = 2, proves the last.
    hints = [("mem_as", 2), ("is_valid", 1), *flags.items(), ("is_load", 1), ("w", "r")]
    rules = [s.add_solved(x, t, tag=f"h:{x}").rule for x, t in hints]
    assert s.solved_rejected == 0 and s.solved_agreed == 7
    assert rules[-1] == "normalize"


@pytest.mark.parametrize(
    "code, flags, is_load",
    [(4, (0, 0, 0, 2), 0), (5, (1, 1, 0, 0), 1), (10, (0, 0, 1, 1), 0)],
    ids=["f3 at 2", "f0 and f1 at 1 (a load)", "f2 and f3 at 1"],
)
def test_load_store_variants(code, flags, is_load):
    s = load_store(code=code)
    want = {**dict(zip(FLAGS, flags)), "is_load": is_load}
    assert {x: pins(s)[x] for x in want} == want
