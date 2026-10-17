"""find_witness: inv_i := f or f * x_i, read off a premise f * (x_1' + ... + x_n') + c.

Each test is one Before/After pair: the premise is After (the solver's side),
the target is Before's constraint with the missing columns inv_i.
"""
from src.polysolver import (
    Implied, PolySolver, VarTable, find_uniform_witness, find_witness,
)

from .test_spec import AFTER, AFTER_GIVEN, BEFORE_C, INVS, A, add, mul, sub

B = ["b0", "b1", "b2", "b3"]
X = [sub(a, b) for a, b in zip(A, B)]  # x_i = a_i - b_i


def solver(given, premises):
    s = PolySolver(VarTable(), declared=given)
    for i, e in enumerate(premises):
        s.add_premise(e, tag=f"p{i}")
    return s


def holds(s, w, target):
    """Plugging w into the target gives exactly a premise (rule N)."""
    v = s.implies(target, s.make_defs(w))
    return isinstance(v, Implied) and v.rule == "normalize"


def test_linear_gives_f_for_every_inv():
    # Before: cmp - (a0*inv0 + .. + a3*inv3)   After: f * (a0 + .. + a3) - cmp
    s = solver(AFTER_GIVEN, AFTER)
    w = find_witness(s, {}, INVS, [BEFORE_C], shortlist=["cmp", "f"])
    assert w == dict.fromkeys(INVS, "f")


def test_squared_gives_f_times_x_i():
    # Before: (a0 - b0)*inv0 + .. - cmp   After: f * ((a0 - b0)^2 + ..) - cmp
    # Like 2103472. No single term works for all inv_i here, so the uniform
    # search fails; find_witness gives inv_i := f * (a_i - b_i).
    s = solver(set(A + B) | {"f", "cmp"}, [sub(mul("f", add(*[mul(x, x) for x in X])), "cmp")])
    target = sub(add(*[mul(x, f"inv{i}") for i, x in enumerate(X)]), "cmp")
    assert find_uniform_witness(s, {}, INVS, [target], shortlist=["f"]) is None
    w = find_witness(s, {}, INVS, [target], shortlist=["f"])
    assert w is not None and holds(s, w, target)
    assert all(w[f"inv{i}"][0] == "f" for i in range(4))  # each is f * (a_i - b_i)


def test_mixed_with_reversed_spelling_and_constants():
    # Like 2100224, mixed: x_0 is squared but spelled (b0 - a0)^2 in After,
    # x_1 = a1 is not squared (so inv1 := f), and x_2 = a2 - 32 compares with a constant.
    s = solver({"a0", "b0", "a1", "a2", "f", "cmp"},
               [sub(mul("f", add(mul(sub("b0", "a0"), sub("b0", "a0")), "a1",
                                 mul(sub("a2", 32), sub("a2", 32)))), "cmp")])
    target = sub(add(mul(X[0], "inv0"), mul("a1", "inv1"), mul(sub("a2", 32), "inv2")), "cmp")
    w = find_witness(s, {}, {"inv0", "inv1", "inv2"}, [target], shortlist=["f"])
    assert w is not None and w["inv1"] == "f" and holds(s, w, target)


def test_powdr_coefficients_and_flipped_sign():
    # powdr keeps the coefficients:  2*x*inv0 + 3*y*inv1 - c  becomes
    # f * (2*x*x + 3*y) - c. Here After is also written the other way round,
    # c - f * (...), so the witness has to absorb a -1 as well.
    s = solver({"x", "y", "f", "c"}, [add(["-", mul("f", add(mul(2, "x", "x"), mul(3, "y")))], "c")])
    target = sub(add(mul(2, "x", "inv0"), mul(3, "y", "inv1")), "c")
    w = find_witness(s, {}, {"inv0", "inv1"}, [target], shortlist=["f"])
    assert w is not None and holds(s, w, target)


def test_no_witness_when_the_premise_does_not_match():
    s = solver(set(A + B) | {"f", "cmp"},
               [add(sub(mul("f", add(*[mul(x, x) for x in X])), "cmp"), 1)])  # After + 1: wrong c
    target = sub(add(*[mul(x, f"inv{i}") for i, x in enumerate(X)]), "cmp")
    assert find_witness(s, {}, INVS, [target], shortlist=["f"]) is None


def test_not_linear_in_the_unknowns():
    # inv0 * inv1 has no single x_i per inv_i, so there is nothing to read off.
    s = solver(AFTER_GIVEN, AFTER)
    target = sub(mul("inv0", "inv1"), "cmp")
    assert find_witness(s, {}, {"inv0", "inv1"}, [target], shortlist=["f"]) is None


def test_renamed_column_is_left_to_the_uniform_search():
    # Before: inv - cmp   After: g - cmp. There is no f * (...) to read off,
    # but the uniform search finds inv := g. This is why it stays as a fallback.
    s = solver({"g", "cmp"}, [sub("g", "cmp")])
    target = sub("inv", "cmp")
    assert find_witness(s, {}, {"inv"}, [target], shortlist=["g"]) is None
    assert find_uniform_witness(s, {}, {"inv"}, [target], shortlist=["g"]) == "g"
