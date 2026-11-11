"""Rules S' (no-wrap pins), L (sum of implied terms) and Q (quotient split, with its fork)."""

import pytest

from src.polysolver import (
    BABYBEAR,
    Implied,
    InvalidDefs,
    PolySolver,
    Quotient,
    Unknown,
    VarTable,
    poly,
)

from .test_spec import add, mul, sub

P = BABYBEAR
A = ["a0", "a1", "a2", "a3"]
INV = ["i0", "i1", "i2", "i3"]
SUM = add(*A)


def is_zero_gadget(ranges=True, **kw):
    """Before of the is-zero merge: cmp = 1 iff some a_i is nonzero."""
    s = PolySolver(VarTable(), declared=[*A, *INV, "cmp"], **kw)
    s.add_premise(mul("cmp", sub("cmp", 1)), "bool")
    for a in A:
        s.add_premise(mul(sub(1, "cmp"), a), f"gate:{a}")
    s.add_premise(sub(add(*(mul(a, i) for a, i in zip(A, INV))), "cmp"), "inv")
    if ranges:
        for a in A:
            s.add_range(a, 0, 255, f"byte:{a}")
    s.propagate()
    return s


# ------------------------------------------------------------ rule S'


def test_nowrap_sum_pins_every_summand():
    s = PolySolver(VarTable(), declared=["a", "b", "c", "y"])
    s.add_premise(add("a", mul(2, "b"), mul(3, "c")), "sum")
    s.add_premise(sub("y", add("a", 7)), "y")
    for x in "abc":
        s.add_range(x, 0, 255, f"byte:{x}")
    assert s.propagate() == 4 and s.nowrap_pins == 3  # y = 7 follows by rule D
    v = s.implies(sub("y", 7))
    assert isinstance(v, Implied)
    assert {"sum", "byte:a", "byte:b", "byte:c"} <= set(v.solved)  # what the pin rests on


@pytest.mark.parametrize(
    "premise, ranged",
    [
        (add("a", "b", 1), "ab"),  # a constant term: the sum is not 0
        (add("a", "b"), "a"),  # b has no range
        (sub("a", "b"), "ab"),  # mixed signs: a = b, not a = b = 0
        (add("a", mul("a", "b")), "ab"),  # not linear
    ],
)
def test_nowrap_pins_decline(premise, ranged):
    s = PolySolver(VarTable(), declared=["a", "b"])
    s.add_premise(premise, "p")
    for x in ranged:
        s.add_range(x, 0, 255, f"byte:{x}")
    assert s.propagate() == 0 and s.nowrap_pins == 0


def test_nowrap_pins_need_the_bound():
    s = PolySolver(VarTable(), declared=["a", "b"])
    s.add_premise(add("a", "b"), "p")
    s.add_range("a", 0, P - 1, "wide")
    s.add_range("b", 0, 255, "byte")
    assert s.propagate() == 0  # a + b may wrap: a = p - 1, b = 1


def test_nowrap_pins_switch():
    s = PolySolver(VarTable(), declared=["a", "b"], nowrap_pins=False)
    s.add_premise(add("a", "b"), "p")
    s.add_range("a", 0, 255, "a")
    s.add_range("b", 0, 255, "b")
    assert s.propagate() == 0 and isinstance(s.implies("a"), Implied)  # rule S still splits


def test_nowrap_pins_after_a_substitution():
    # a + b + x reads as a sum of ranged variables only once x is pinned.
    s = PolySolver(VarTable(), declared=["a", "b", "x"])
    s.add_premise(add("a", "b", "x"), "sum")
    s.add_range("a", 0, 255, "a")
    s.add_range("b", 0, 255, "b")
    s.propagate()
    assert isinstance(s.implies("a"), Unknown)
    s.add_premise("x", "x")
    s.propagate()
    assert isinstance(s.implies("a"), Implied) and isinstance(s.implies("b"), Implied)


def test_nowrap_pins_are_sound_on_small_field():
    # Brute force over F_7: every model of the premise and ranges has a = b = 0
    # exactly when S' pins.
    for hi_a in range(7):
        for hi_b in range(7):
            for ca in range(1, 7):
                for cb in range(1, 7):
                    s = PolySolver(VarTable(), declared=["a", "b"], p=7, max_terms=6)
                    s.add_premise(add(mul(ca, "a"), mul(cb, "b")), "p")
                    s.add_range("a", 0, hi_a, "a")
                    s.add_range("b", 0, hi_b, "b")
                    s.propagate()
                    models = [
                        (a, b)
                        for a in range(hi_a + 1)
                        for b in range(hi_b + 1)
                        if (ca * a + cb * b) % 7 == 0
                    ]
                    for name, i in (("a", 0), ("b", 1)):
                        if isinstance(s.implies(name), Implied):
                            assert all(m[i] == 0 for m in models), (hi_a, hi_b, ca, cb)


# ------------------------------------------------------------ rule L


def test_sum_of_implied_products():
    s = is_zero_gadget(ranges=False)
    v = s.implies(mul(sub(1, "cmp"), SUM))
    assert isinstance(v, Implied) and v.rule == "sum"
    assert v.premises == tuple(f"gate:{a}" for a in A)
    # The sum may come first, and a summand may carry a sign or a coefficient.
    assert s.implies(mul(sub(add("a0", mul(3, "a1")), "a2"), sub(1, "cmp"))).rule == "sum"


def test_sum_needs_every_term():
    s = is_zero_gadget(ranges=False)
    v = s.implies(mul(sub(1, "cmp"), add(SUM, "i0")))
    assert isinstance(v, Unknown)
    assert isinstance(s.implies(mul("cmp", SUM)), Unknown)  # the wrong gate
    assert isinstance(s.implies(SUM), Unknown)  # not a product: nothing gates it


def test_sum_terms_may_come_from_rule_s():
    # G * (a + b) splits into G * a and G * b (rule S); L adds them up with others.
    s = PolySolver(VarTable(), declared=["g", "a", "b", "c"])
    s.add_premise(mul("g", add("a", "b")), "ab")
    s.add_premise(mul("g", "c"), "c")
    s.add_range("a", 0, 255, "a")
    s.add_range("b", 0, 255, "b")
    v = s.implies(mul("g", add("a", "c")))
    assert v.rule == "sum" and set(v.premises) == {"ab", "c"} and set(v.ranges) == {"a", "b"}


def test_sum_through_defs():
    s = is_zero_gadget(ranges=False)
    defs = s.make_defs({"g": sub(1, "cmp")})
    v = s.implies(mul("g", SUM), defs)
    assert v.rule == "sum" and v.defs == ("g",)


# ------------------------------------------------------------ rule Q


def quotient_query(s, n="cmp", d=SUM):
    defs = s.make_defs({"f": Quotient(n, d)})
    return s.implies(sub(mul("f", SUM), "cmp"), defs)


def test_quotient_split_on_the_is_zero_gadget():
    s = is_zero_gadget()
    v = quotient_query(s)
    assert isinstance(v, Implied) and v.rule == "quotient-split"
    assert "assume f's denominator = 0" in v.premises
    assert v.defs == ("f",)
    # The zero case rests on the ranges, the gadget sum and booleanity.
    assert {"byte:a0", "byte:a3", "inv"} <= set(v.solved)
    assert s.forks == 1
    assert isinstance(s.implies("cmp"), Unknown)  # nothing leaks out of the fork
    assert s.nowrap_pins == 0


def test_quotient_zero_case_needs_the_ranges():
    v = quotient_query(is_zero_gadget(ranges=False))
    assert isinstance(v, Unknown) and v.kind == "quotient" and "= 0" in v.note
    v = quotient_query(is_zero_gadget(nowrap_pins=False))
    assert isinstance(v, Unknown) and v.kind == "quotient"


def test_quotient_nonzero_case_is_checked():
    s = is_zero_gadget()
    defs = s.make_defs({"f": Quotient("cmp", SUM)})
    v = s.implies(add(sub(mul("f", SUM), "cmp"), 1), defs)  # reads 1 when sum != 0
    assert isinstance(v, Unknown) and v.kind == "quotient" and "!= 0" in v.note
    # A wrong numerator: f * sum = 1 - cmp, not cmp.
    v = quotient_query(s, n=sub(1, "cmp"))
    assert isinstance(v, Unknown) and "!= 0" in v.note


def test_quotient_declines():
    s = is_zero_gadget()
    defs = s.make_defs({"f": Quotient("cmp", SUM), "g": Quotient(1, "a0")})
    v = s.implies(mul("f", "f"), defs)
    assert isinstance(v, Unknown) and v.kind == "opaque" and "not linear" in v.note
    v = s.implies(add("f", "g"), defs)
    assert isinstance(v, Unknown) and v.kind == "opaque" and "several" in v.note


def test_quotient_with_constant_denominator():
    s = PolySolver(VarTable(), declared=["x", "z"])
    s.add_premise("z", "z")
    s.propagate()
    half = s.make_defs({"f": Quotient("x", 2)})
    assert isinstance(s.implies(sub(mul(2, "f"), "x"), half), Implied)  # f = x / 2
    assert isinstance(s.implies("f", half), Unknown)
    by_zero = s.make_defs({"f": Quotient("x", "z")})  # z = 0 in every model: f = 0
    assert isinstance(s.implies("f", by_zero), Implied)
    assert isinstance(s.implies(sub("f", "x"), by_zero), Unknown)
    assert s.forks == 0


def test_quotient_that_cancels_out():
    s = is_zero_gadget()
    defs = s.make_defs({"f": Quotient("cmp", SUM)})
    assert isinstance(s.implies(mul(sub("f", "f"), "a0"), defs), Implied)


def test_quotient_defs_are_validated():
    s = PolySolver(VarTable(), declared=["x"])
    with pytest.raises(InvalidDefs):
        s.make_defs({"f": Quotient("x", "nope")})
    with pytest.raises(InvalidDefs):
        s.make_defs({"x": Quotient(1, "x")})
    assert s.normal_form("f", s.make_defs({"f": Quotient(1, "x")})) is None


def test_quotient_split_is_sound_on_small_field():
    # Brute force over F_101: whenever Q says Implied, q is 0 in every model.
    p = 101
    queries = [
        sub(mul("f", "d"), "n"),
        mul("f", sub(mul("f", "d"), "n")),
        sub(mul("f", "d"), mul("n", "d")),
        mul("d", sub(mul("f", "d"), "n")),
        add(mul("f", "n"), "d"),
        "f",
        sub("f", "n"),
    ]
    premises = [None, "d", sub("d", 1), mul("n", "d"), mul("d", sub("d", 1)), sub("n", "d")]

    def value(e, env):
        return poly.expand(e, lambda name: poly.const(env[name], p), p).get((), 0)

    for prem in premises:
        s = PolySolver(VarTable(), declared=["n", "d"], p=p, max_terms=64)
        if prem is not None:
            s.add_premise(prem, "p")
        s.propagate()
        defs = s.make_defs({"f": Quotient("n", "d")})
        models = [
            {"n": n, "d": d, "f": n * pow(d, p - 2, p) % p if d else 0}
            for n in range(p)
            for d in range(p)
            if prem is None or value(prem, {"n": n, "d": d}) == 0
        ]
        proved = 0
        for q in queries:
            if isinstance(s.implies(q, defs), Implied):
                proved += 1
                assert all(value(q, m) == 0 for m in models), (prem, q)
        assert proved  # f * d - n * d... at least one holds under every premise


def test_split_linear():
    x, y = 0, 1
    a = {((x, 1), (y, 1)): 2, ((y, 2),): 3, ((x, 1),): 4, (): 5}
    assert poly.split_linear(a, x) == ({((y, 1),): 2, (): 4}, {((y, 2),): 3, (): 5})
    assert poly.split_linear(a, y) is None
    assert poly.split_linear({}, x) == ({}, {})


# ------------------------------------------------------------ rule S': squares


def square(e):
    return mul(e, e)


def ranged(names, premise, hi=255, **kw):
    s = PolySolver(VarTable(), declared=names, **kw)
    s.add_premise(premise, "p")
    for x in names:
        s.add_range(x, 0, hi, f"r:{x}")
    s.propagate()
    return s


def test_sum_of_squares_gives_equations():
    # (a0 - b0)^2 + (a1 - b1)^2 = 0 over bytes: a0 = b0 and a1 = b1.
    s = ranged(["a0", "b0", "a1", "b1"], add(square(sub("a0", "b0")), square(sub("a1", "b1"))))
    assert s.nowrap_equations == 2
    v = s.implies(sub("a0", "b0"))
    assert isinstance(v, Implied) and {"p", "r:a0", "r:b0"} <= set(v.solved)
    assert isinstance(s.implies(sub("a1", "b1")), Implied)
    assert isinstance(s.implies(sub("a0", "b1")), Unknown)


def test_affine_squares_and_linear_terms_mix():
    # keccak 2100224: (a0 - 32)^2 + (a1 - 99)^2 + (a2 - 32)^2 + a3 = 0.
    d = add(square(sub("a0", 32)), square(sub("a1", 99)), square(sub("a2", 32)), "a3")
    s = ranged(A, d)
    assert s.nowrap_pins == 4
    for name, value in zip(A, (32, 99, 32, 0)):
        assert isinstance(s.implies(sub(name, value)), Implied)


def test_square_with_weights():
    # The unit multiple is tried among the inverses of the coefficients, as in
    # rule S: 1/4 of this premise's key reads (2a - b)^2 + 2c.
    s = ranged(["a", "b", "c"], add(mul(3, square(sub(mul(2, "a"), "b"))), mul(6, "c")))
    assert isinstance(s.implies(sub(mul(2, "a"), "b")), Implied)
    assert isinstance(s.implies("c"), Implied)
    assert isinstance(s.implies("a"), Unknown)


@pytest.mark.parametrize(
    "premise",
    [
        sub(square(sub("a", "b")), square("c")),  # a difference of squares
        add(square(sub("a", "b")), 1),  # a constant that no square accounts for
        add(mul("a", "b"), "c"),  # a product, not a square
        add(square(sub("a", "b")), mul("a", "c")),  # a stray cross term
        add(square(sub("a", "b")), "a"),  # a linear term on a squared variable
        add(mul("a", mul("a", "a")), "b"),  # degree 3
    ],
)
def test_squares_decline(premise):
    s = ranged(["a", "b", "c"], premise)
    assert s.nowrap_pins == 0 and s.nowrap_equations == 0


def test_squares_need_the_bound():
    # Over 16-bit ranges four squares can reach 4 * 65535^2 > p.
    names = ["a0", "b0", "a1", "b1"]
    s = ranged(names, add(square(sub("a0", "b0")), square(sub("a1", "b1"))), hi=2**16 - 1)
    assert s.nowrap_equations == 0
    s = ranged(names, add(square(sub("a0", "b0")), square(sub("a1", "b1"))), hi=2**14)
    assert s.nowrap_equations == 2


def test_squares_need_every_range():
    s = PolySolver(VarTable(), declared=["a", "b"])
    s.add_premise(square(sub("a", "b")), "p")  # sound even so, but D and S' both pass
    s.add_range("a", 0, 255, "a")
    s.propagate()
    assert s.nowrap_equations == 0


def test_squares_are_sound_on_small_field():
    # Brute force over F_101: whatever S' concludes holds in every model.
    p = 101
    shapes = [
        lambda c, w, t: add(mul(c, square(add("a", mul(w, "b"), t))), "c"),
        lambda c, w, t: add(square(sub("a", mul(w, "b"))), mul(c, square(sub("c", t)))),
        lambda c, w, t: add(mul(c, square(sub("a", "b"))), mul(w, "c"), t),
    ]
    fired = 0
    for shape in shapes:
        for c in (1, 2, 50, 100):
            for w in (1, 3, 100):
                for t in (0, 1, 99):
                    for hi in (1, 3, 6, 40):
                        e = shape(c, w, t)
                        s = PolySolver(VarTable(), declared=["a", "b", "c"], p=p, max_terms=64)
                        s.add_premise(e, "p")
                        for x in "abc":
                            s.add_range(x, 0, hi, x)
                        s.propagate()
                        if not (s.nowrap_pins or s.nowrap_equations):
                            continue
                        fired += 1
                        queries = ["a", "b", "c", sub("a", "b"), sub("a", mul(w, "b")),
                                   add("a", mul(w, "b"), t), sub("c", t)]
                        proved = [q for q in queries if isinstance(s.implies(q), Implied)]
                        for a in range(hi + 1):
                            for b in range(hi + 1):
                                for cc in range(hi + 1):
                                    env = {"a": a, "b": b, "c": cc}
                                    val = lambda q: poly.expand(
                                        q, lambda n: poly.const(env[n], p), p).get((), 0)
                                    if val(e) == 0:
                                        assert all(val(q) == 0 for q in proved), (c, w, t, hi)
    assert fired > 20


def test_squared_is_zero_gadget_through_rule_q():
    b = ["b0", "b1", "b2", "b3"]
    diffs = [sub(x, y) for x, y in zip(A, b)]
    s = PolySolver(VarTable(), declared=[*A, *b, *INV, "cmp"])
    s.add_premise(mul("cmp", sub("cmp", 1)), "bool")
    s.add_premise(sub(add(*(mul(d, i) for d, i in zip(diffs, INV))), "cmp"), "inv")
    for x in [*A, *b]:
        s.add_range(x, 0, 255, f"byte:{x}")
    s.propagate()
    d = add(*(square(x) for x in diffs))
    defs = s.make_defs({"f": Quotient("cmp", d)})
    v = s.implies(sub(mul("f", d), "cmp"), defs)
    assert isinstance(v, Implied) and v.rule == "quotient-split"
    assert s.nowrap_equations == 0  # the equations stay in the fork
