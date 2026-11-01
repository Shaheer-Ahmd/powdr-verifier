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


def solver(given, premises=(), **kw):
    s = PolySolver(VarTable(), declared=given, **kw)
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
    s.derive()  # nothing to pin, so nothing more is logged
    assert s.solved_log == [("h:x", no, False), ("h:x", ok, False)]
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
    assert s.solved_agreed == 1 and [a for _, _, a in s.solved_log] == [False, True]
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
    # mentions a and b, which p1 never mentions as written. With constants
    # on, p1 would pin y = 5 as it is added.
    s = solver({"y", "a", "b"}, [sub("y", add("a", "b")), sub("y", 5)], constants=False)
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


# ---------------------------------------------------------------- constants (derive)

def test_constants_pinned_in_turn():
    # pc0 is pinned as its premise is added; pc1 - pc0 - 4 becomes a pin in
    # derive(), once pc0 is known.
    s = solver({"pc0", "pc1"}, [sub("pc1", add("pc0", 4)), sub("pc0", 100)])
    assert s.constants_solved == 1
    assert s.derive() == 1 and s.constants_solved == 2 and s.pinned == 0
    v = s.implies(sub("pc1", 104))
    # pc1's pin rests on p0 as rewritten by pc0's pin, which came from p1.
    assert v.rule == "trivial" and v.solved == ("p0", "p1")


def test_constants_scaled_and_zero():
    s = solver({"x", "y"}, [sub(mul(3, "x"), 12), mul(5, "y")])  # 3x = 12, 5y = 0
    assert s.constants_solved == 2  # as they are added
    assert s.implies(sub("x", 4)).rule == "trivial"
    assert s.implies("y").rule == "trivial"


def test_constants_leave_the_rest():
    # Two variables, a square, a product: none of them pins a variable.
    s = solver({"x", "y", "z"}, [sub("x", "y"), mul("z", sub("z", 1)), mul("x", "y")])
    assert s.derive() == 0 and s.solved_count == 0


def test_hint_agrees_with_a_constant():
    s = solver({"x", "y"}, [sub("x", 2), sub("y", add("x", 1))])
    assert s.derive() == 1  # x = 2 as it is added, then y = 3
    assert isinstance(s.add_solved("x", 2, tag="h:x"), Implied)
    assert s.solved_agreed == 1 and s.solved_rejected == 0


def test_hint_turns_a_premise_into_a_constant():
    # y + x - a - 3 mentions a until the hint x := a cancels it: then y = 3.
    s = solver({"x", "y", "a"}, [sub("x", "a"), sub(add("y", "x"), add("a", 3))])
    assert s.derive() == 0
    assert isinstance(s.add_solved("x", "a", tag="h:x"), Implied)
    assert s.derive() == 1 and s.derive_pins == [0, 1]
    v = s.implies(sub("y", 3))
    assert v.rule == "trivial" and v.solved == ("h:x", "p1")


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
