"""Solved equations: add_solved checks x = t, then replaces x by t everywhere."""
from functools import reduce

from src.polysolver import BABYBEAR, Implied, PolySolver, Unknown, VarTable

P = BABYBEAR


def add(*es):
    return reduce(lambda a, b: [a, "+", b], es)


def mul(*es):
    return reduce(lambda a, b: [a, "*", b], es)


def sub(a, b):
    return [a, "-", b]


def solver(given, premises=()):
    s = PolySolver(VarTable(), declared=given)
    for i, e in enumerate(premises):
        s.add_premise(e, tag=f"p{i}")
    return s


def test_substituted_constraint_needs_the_solved_equation():
    # Before: x = a + b and x*y = c. After (powdr substituted x): (a + b)*y = c.
    s = solver({"x", "y", "a", "b", "c"}, [sub("x", add("a", "b")), sub(mul("x", "y"), "c")])
    q = sub(mul(add("a", "b"), "y"), "c")
    assert isinstance(s.implies(q), Unknown)  # one premise at a time: no match
    v = s.add_solved("x", add("a", "b"), tag="h:x")
    assert isinstance(v, Implied) and v.premises == ("p0",)
    w = s.implies(q)
    assert w.rule == "normalize" and w.premises == ("p1",) and w.solved == ("h:x",)
    assert s.solved_count == 1


def test_unimplied_equation_is_rejected_and_changes_nothing():
    s = solver({"x", "y", "a", "b", "c"}, [sub("x", "a"), sub(mul("x", "y"), "c")])
    v = s.add_solved("x", "b", tag="h:x")  # x = b does not follow
    assert isinstance(v, Unknown)
    assert s.solved_count == 0 and s.solved_rejected == 1
    assert isinstance(s.implies(sub(mul("b", "y"), "c")), Unknown)
    # The right equation is still accepted afterwards.
    assert isinstance(s.add_solved("x", "a", tag="h:x"), Implied)
    assert s.implies(sub(mul("a", "y"), "c")).rule == "normalize"


def test_every_verdict_is_logged():
    s = solver({"x", "a", "b"}, [sub("x", "a")])
    no = s.add_solved("x", "b", tag="h:x")
    ok = s.add_solved("x", "a", tag="h:x")
    s.solve_constants()  # nothing to pin, so nothing more is logged
    assert s.solved_log == [("h:x", no), ("h:x", ok)]
    assert isinstance(no, Unknown) and isinstance(ok, Implied)


def test_value_must_not_mention_x():
    s = solver({"x", "a"}, [sub("x", add("x", "a"))])
    v = s.add_solved("x", add("x", "a"), tag="h")
    assert isinstance(v, Unknown) and v.kind == "not-solved"


def test_solved_once():
    # A second equation for x is checked against x's value: the same value is
    # accepted and changes nothing, another one is rejected.
    s = solver({"x", "a", "b"}, [sub("x", "a")])
    assert isinstance(s.add_solved("x", "a", tag="h1"), Implied)
    v = s.add_solved("x", "a", tag="h2")
    assert v.rule == "trivial" and s.solved_count == 1 and s.solved_accepted == 2
    v = s.add_solved("x", "b", tag="h3")
    assert isinstance(v, Unknown) and v.kind == "already-solved"
    assert s.implies(sub("x", "a")).solved == ("h1",)


def test_check_uses_earlier_solved_equations():
    # x = a + 1 (p0), y = 2*x (p1). Hint y := 2a + 2 holds only after x is solved.
    s = solver({"x", "y", "a"}, [sub("x", add("a", 1)), sub("y", mul(2, "x"))])
    assert isinstance(s.add_solved("y", add(mul(2, "a"), 2), tag="h:y"), Unknown)
    assert isinstance(s.add_solved("x", add("a", 1), tag="h:x"), Implied)
    assert isinstance(s.add_solved("y", add(mul(2, "a"), 2), tag="h:y"), Implied)


def test_back_substitution_keeps_values_reduced():
    # y := 2x first, then x := a + 1: y's value must become 2a + 2.
    s = solver({"x", "y", "a"}, [sub("y", mul(2, "x")), sub("x", add("a", 1))])
    assert isinstance(s.add_solved("y", mul(2, "x"), tag="h:y"), Implied)
    assert isinstance(s.add_solved("x", add("a", 1), tag="h:x"), Implied)
    v = s.implies(sub("y", add(mul(2, "a"), 2)))
    assert v.rule == "trivial" and v.solved == ("h:y",)


def test_premise_found_through_a_solved_value():
    # Premise p1 mentions only y (and a constant); after y := a + b its key
    # mentions a and b, which p1 never mentions as written.
    s = solver({"y", "a", "b"}, [sub("y", add("a", "b")), sub("y", 5)])
    assert isinstance(s.add_solved("y", add("a", "b"), tag="h:y"), Implied)
    v = s.implies(sub(add("a", "b"), 5))
    assert v.rule == "normalize" and v.premises == ("p1",) and v.solved == ("h:y",)


def test_defs_see_solved_equations():
    s = solver({"x", "a"}, [sub("x", "a")])
    assert isinstance(s.add_solved("x", "a", tag="h:x"), Implied)
    defs = s.make_defs({"w": "x"})  # w is fresh (a candidate column)
    v = s.implies(sub("w", "a"), defs)
    assert v.rule == "trivial" and v.defs == ("w",) and v.solved == ("h:x",)


def test_gated_premise_becomes_usable():
    # The solver-step shape: G*L = 0 with G = f1 + f2 = 1. Hint f1 := 1 - f2
    # turns the premise into L = 0, so L (as powdr wrote it) is implied.
    G = add("f1", "f2")
    L = sub("t", add("u", 1))
    s = solver({"f1", "f2", "t", "u"}, [mul(G, L), sub(1, G)])
    assert isinstance(s.implies(L), Unknown)
    assert isinstance(s.add_solved("f1", sub(1, "f2"), tag="h:f1"), Implied)
    assert s.implies(L).rule == "normalize"


# ---------------------------------------------------------------- constants

def test_solve_constants_propagates():
    # pc0 is pinned; pc1 - pc0 - 4 becomes a pin once pc0 is known.
    s = solver({"pc0", "pc1"}, [sub("pc1", add("pc0", 4)), sub("pc0", 100)])
    assert s.solve_constants() == 2
    v = s.implies(sub("pc1", 104))
    # Provenance is direct: pc1's equation (from p0), which itself rested on pc0's.
    assert v.rule == "trivial" and v.solved == ("p0",)


def test_solve_constants_scales_and_zero():
    s = solver({"x", "y"}, [sub(mul(3, "x"), 12), mul(5, "y")])  # 3x = 12, 5y = 0
    assert s.solve_constants() == 2
    assert s.implies(sub("x", 4)).rule == "trivial"
    assert s.implies("y").rule == "trivial"


def test_solve_constants_leaves_the_rest():
    # Two variables, a square, a product: none of them pins a variable.
    s = solver({"x", "y", "z"}, [sub("x", "y"), mul("z", sub("z", 1)), mul("x", "y")])
    assert s.solve_constants() == 0 and s.solved_count == 0


def test_solve_constants_after_hints():
    # The hint makes p1 a pin: y - x - 1 with x := 2 becomes y - 3.
    s = solver({"x", "y"}, [sub("x", 2), sub("y", add("x", 1))])
    assert isinstance(s.add_solved("x", 2, tag="h:x"), Implied)
    assert s.solve_constants() == 1
    assert s.implies(sub("y", 3)).rule == "trivial"
    assert s.solved_rejected == 0



# ---------------------------------------------------------------- equality, normal form

def test_implies_equal_is_value_equality():
    s = solver({"x", "y", "z"}, [sub("x", "y")])
    assert s.implies_equal("x", "y").rule == "normalize"
    assert isinstance(s.implies_equal("x", "z"), Unknown)
    assert s.implies_equal(add("x", 1), add(1, "x")).rule == "trivial"


def test_normal_form_sees_solved_equations_and_defs():
    s = solver({"x", "a"}, [sub("x", add("a", 1))])
    assert isinstance(s.add_solved("x", add("a", 1), tag="h"), Implied)
    assert s.normal_form("x") == s.normal_form(add("a", 1))
    defs = s.make_defs({"w": "x"})
    assert s.normal_form("w", defs) == s.normal_form(add(1, "a"))
    assert s.normal_form("w") is None  # w is unknown without the defs
