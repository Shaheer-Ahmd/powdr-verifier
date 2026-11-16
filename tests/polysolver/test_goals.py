"""Goals: Zero and Bounded, and entails for a conjunction of them."""

import pytest

from src.polysolver import Bounded, Implied, PolySolver, Unknown, VarTable, Zero


def solver():
    s = PolySolver(VarTable(), declared=["x", "y", "z"])
    s.add_premise(["z", "-", "x"], "p0")
    s.add_range("x", 0, 255, "rx")
    s.add_range("y", 0, 1, "ry")
    s.propagate()
    return s


def test_bounded_reads_the_interval():
    s = solver()
    v = s.bounded(["x", "+", "y"], 256)
    assert isinstance(v, Implied) and v.rule == "interval"
    assert set(v.ranges) == {"x", "y"}
    assert s.bounded("x", 254).kind == "interval-bound"  # x may be 255
    assert s.bounded(["x", "*", "y"], 10**6).kind == "no-interval"  # not affine
    assert s.bounded(["x", "-", "y"], 255).kind == "no-interval"  # may wrap


def test_bounded_reports_definitions():
    s = solver()
    defs = s.make_defs({"w": ["x", "+", 1]})
    v = s.bounded("w", 256, defs)
    assert isinstance(v, Implied) and v.defs == ("w",)
    assert isinstance(s.bounded("w", 255, defs), Unknown)


def test_entails_merges_what_the_goals_rest_on():
    s = solver()
    v = s.entails([Zero(["z", "-", "x"]), Bounded("y", 1)])
    assert isinstance(v, Implied) and v.rule == "conjunction"
    assert v.premises == ("p0",) and v.ranges == ("y",)


def test_entails_single_goal_is_its_own_verdict():
    s = solver()
    assert s.entails([Zero(["z", "-", "x"])]) == s.implies(["z", "-", "x"])
    assert s.entails([Bounded("x", 255)]) == s.bounded("x", 255)


def test_entails_no_goals_is_trivial():
    v = solver().entails([])
    assert isinstance(v, Implied) and v.rule == "trivial"


def test_entails_reports_the_first_goal_not_implied():
    s = solver()
    v = s.entails([Bounded("x", 255), Zero(["y", "-", "x"]), Bounded("x", 3)])
    assert isinstance(v, Unknown) and v.note.startswith("goal 1 ")


def test_entails_rejects_a_bare_expression():
    with pytest.raises(TypeError):
        solver().entails([["x", "-", "z"]])
