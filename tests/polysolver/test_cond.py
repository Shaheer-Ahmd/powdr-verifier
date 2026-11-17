"""Rule I (conditional split), AnyOf, and what forks read from the nonzero index."""

import pytest

from src.polysolver import (
    BABYBEAR,
    COND_CAP,
    AnyOf,
    Bounded,
    Cond,
    Implied,
    InvalidDefs,
    PolySolver,
    Quotient,
    Unknown,
    VarTable,
    Zero,
)

from .test_spec import mul, sub

P = BABYBEAR


def solver(declared, premises=(), ranges=()):
    s = PolySolver(VarTable(), declared=declared)
    for i, e in enumerate(premises):
        s.add_premise(e, f"p{i}")
    for x, hi in ranges:
        s.add_range(x, 0, hi, f"r:{x}")
    s.propagate()
    return s


def three_valued():
    """x in {0, 1, 2}."""
    return solver(["x", "y"], premises=[mul("x", sub("x", 1), sub("x", 2))])


# ------------------------------------------------------------ rule I


def test_split_proves_what_holds_in_both_cases():
    s = three_valued()
    defs = s.make_defs({"f": Cond("x", 5, 7)})
    assert isinstance(s.implies(sub("f", 5), defs), Unknown)  # 7 where x != 0
    v = s.implies(mul(sub("f", 5), sub("f", 7)), defs)
    assert isinstance(v, Implied) and v.rule == "cond-split"
    assert "assume f's guard != 0" in v.premises and "assume f's guard = 0" in v.premises
    assert v.defs == ("f",)


def test_a_decided_guard_needs_no_fork():
    s = solver(["x"], premises=["x"])  # x = 0
    defs = s.make_defs({"f": Cond("x", 5, 7)})
    v = s.implies(sub("f", 5), defs)
    assert isinstance(v, Implied) and s.forks == 0
    s = solver(["x"])
    v = s.implies(sub("f", 7), s.make_defs({"f": Cond(3, 5, 7)}))  # 3 != 0
    assert isinstance(v, Implied) and s.forks == 0


def test_a_shared_guard_is_split_once():
    s = three_valued()
    defs = s.make_defs({"f": Cond("x", 1, 0), "h": Cond("x", 0, 1)})
    v = s.implies(sub(["f", "+", "h"], 1), defs)
    assert isinstance(v, Implied) and v.rule == "cond-split"
    assert s.forks == 2  # one split: the forks decide h's guard too


def test_nested_guards():
    s = solver(["x", "y"], premises=[mul("x", sub("x", 1)), mul("y", sub("y", 1))])
    defs = s.make_defs({"f": Cond("x", Cond("y", 1, 2), 3)})
    v = s.implies(mul(sub("f", 1), sub("f", 2), sub("f", 3)), defs)
    assert isinstance(v, Implied)
    assert isinstance(s.implies(mul(sub("f", 1), sub("f", 2)), defs), Unknown)


def test_a_branch_may_be_a_quotient():
    # x = 0: f = 0, so x*f = 0 = x*y; x != 0: f = y.
    s = solver(["x", "y"])
    defs = s.make_defs({"f": Cond("x", 0, Quotient("y", 1))})
    assert isinstance(s.implies(sub(mul("x", "f"), mul("x", "y")), defs), Implied)


def test_definitions_are_checked_through_every_branch():
    s = solver(["x"])
    with pytest.raises(InvalidDefs):
        s.make_defs({"f": Cond("u", 0, 1)})  # undeclared guard
    with pytest.raises(InvalidDefs):
        s.make_defs({"f": Cond("x", 0, Cond("x", "u", 1))})  # undeclared in a branch


def test_over_the_cap_is_a_decline():
    names = [f"x{i}" for i in range(COND_CAP + 1)]
    s = solver(names)
    rhs = 1
    for x in names:
        rhs = Cond(x, rhs, 1)
    v = s.implies(sub("f", 1), s.make_defs({"f": rhs}))
    assert isinstance(v, Unknown) and v.kind == "opaque"


def test_a_failed_case_names_the_guard():
    s = three_valued()
    v = s.implies(sub("f", 5), s.make_defs({"f": Cond("x", 5, 7)}))
    assert v.kind == "cond" and "f's guard != 0" in v.note


# ------------------------------------------------------------ bounded, nonzero index


def test_bounded_splits_and_reads_the_assumption_as_a_range():
    s = solver(["y"], ranges=[("y", 255)])
    # y != 0 gives y in [1, 255], so y - 1 >= 0.
    v = s.bounded("f", 255, s.make_defs({"f": Cond("y", 0, sub("y", 1))}))
    assert isinstance(v, Implied) and v.rule == "cond-split"


def test_endpoint_removal_runs_to_a_fixpoint():
    s = solver(["y"], ranges=[("y", 255)])
    # y - 1 != 0 is read before y != 0 raises the bound; y - 2 needs both.
    defs = s.make_defs({"f": Cond("y", 0, Cond(sub("y", 1), 0, sub("y", 2)))})
    assert isinstance(s.bounded("f", 253, defs), Implied)
    assert isinstance(s.bounded("f", 252, defs), Unknown)  # y = 255 gives 253


def test_a_quotient_by_a_nonzero_constant_is_a_polynomial():
    s = solver(["y"], ranges=[("y", 255)])
    defs = s.make_defs({"f": Quotient(mul(2, "y"), 2)})
    assert s.normal_form("f", defs) is not None
    assert isinstance(s.bounded("f", 255, defs), Implied)
    # A denominator that is a variable stays a quotient.
    assert s.normal_form("g", s.make_defs({"g": Quotient("y", "y")})) is None


def test_a_nonzero_factor_is_dropped_in_a_fork():
    # x*y = 0 with y != 0 gives x = 0, in the fork that assumes y != 0.
    s = solver(["x", "y"], premises=[mul("x", "y")], ranges=[("y", 255)])
    v = s.implies("f", s.make_defs({"f": Cond("y", 0, "x")}))
    assert isinstance(v, Implied)


def test_a_factor_whose_interval_excludes_zero_is_dropped_in_a_fork():
    # x*(y + 1) with y a byte: y + 1 is in [1, 256]. Only forks look.
    s = solver(["x", "y", "z"], premises=[mul("x", ["y", "+", 1])], ranges=[("y", 255)])
    assert isinstance(s.implies("x"), Unknown)  # not at the root (a cost policy)
    defs = s.make_defs({"f": Cond("z", "x", "x")})  # any split: the fork reads x*(y+1)
    assert isinstance(s.implies("f", defs), Implied)


# ------------------------------------------------------------ AnyOf


def flag_and_value():
    """m = [y != 0] and e = y - 1 where y != 0, else -1: e is a byte only where m != 0."""
    s = solver(["y"], ranges=[("y", 255)])
    defs = s.make_defs({"m": Cond("y", 0, 1), "e": Cond("y", P - 1, sub("y", 1))})
    return s, defs


def test_any_of_is_decided_case_by_case():
    s, defs = flag_and_value()
    g = AnyOf((("zero", (Zero("m"),)), ("row", (Bounded("e", 255),))))
    v = s.entails([g], defs)
    assert isinstance(v, Implied) and v.rule == "cond-split"
    assert set(v.chosen) == {"zero", "row"}
    # Neither option holds in every case on its own.
    assert isinstance(s.entails([Zero("m")], defs), Unknown)
    assert isinstance(s.entails([Bounded("e", 255)], defs), Unknown)


def test_any_of_without_conditionals_takes_the_first_option_that_holds():
    s = solver(["x", "y"], premises=["x"], ranges=[("y", 255)])
    g = AnyOf((("a", (Zero("y"),)), ("b", (Zero("x"),)), ("c", (Bounded("y", 255),))))
    v = s.entails([g])
    assert isinstance(v, Implied) and v.chosen == ("b",)
    none = s.entails([AnyOf((("a", (Zero("y"),)),))])
    assert isinstance(none, Unknown) and "a:" in none.note
