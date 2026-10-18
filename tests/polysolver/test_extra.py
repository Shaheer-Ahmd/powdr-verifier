"""PolySolver checks beyond the spec sketches: limits, caching, isolation, soundness."""
import ast
import random
from pathlib import Path

from src.polysolver import BABYBEAR, Implied, PolySolver, Unknown, VarTable, variables
from src.polysolver import poly

from .test_spec import AFTER, AFTER_GIVEN, BEFORE_C, INVS, add, mul, sub

P = BABYBEAR


def test_expansion_limit_is_unknown():
    s = PolySolver(VarTable(), declared=["x", "y"], max_terms=8)
    big = mul(*[add("x", "y", 1)] * 6)  # (x + y + 1)^6 has 28 terms
    v = s.implies(big)
    assert isinstance(v, Unknown) and "expansion limit" in v.note


def test_ranges_intersect():
    s = PolySolver(VarTable(), declared=["cmp", "a0", "a1"])
    s.add_premise(mul("cmp", add("a0", "a1")), tag="p")
    s.add_range("a0", 0, P - 1, "wide")
    s.add_range("a1", 0, 255, "byte")
    assert isinstance(s.implies(mul("cmp", "a0")), Unknown)  # a0 too wide
    s.add_range("a0", 0, 255, "byte")  # intersects to [0, 255]
    assert s.implies(mul("cmp", "a0")).rule == "nowrap-split"


def test_implied_never_becomes_unknown():
    s = PolySolver(VarTable(), declared=["x", "y", "z"])
    s.add_premise(sub("x", "y"), tag="p")
    q = sub("y", "x")
    assert s.implies(q).rule == "normalize"
    s.add_premise(sub("z", 1), tag="q")
    s.add_range("z", 0, 1, "bit")
    assert s.implies(q).rule == "normalize"


def test_verdict_reports_defs_used():
    s = PolySolver(VarTable(), declared=AFTER_GIVEN)
    for i, e in enumerate(AFTER):
        s.add_premise(e, tag=f"p{i}")
    d = s.make_defs({i: "f" for i in INVS})
    assert set(s.implies(BEFORE_C, d).defs) == INVS


def test_lazy_index_expands_only_relevant_premises():
    s = PolySolver(VarTable(), declared=["x", "y"] + [f"z{i}" for i in range(50)])
    for i in range(50):
        s.add_premise(sub(f"z{i}", i), tag=f"z{i}")
    s.add_premise(sub("x", "y"), tag="xy")
    assert s.implies(sub("y", "x")).rule == "normalize"
    assert s.premises_expanded == 1


def _eval(e, env):
    return poly.expand(e, lambda n: poly.const(env[n], P), P).get((), 0)


def test_normalize_hits_have_constant_ratio():
    """Acceptance (4): q[Defs] and the matched premise differ by a constant factor."""
    s = PolySolver(VarTable(), declared=AFTER_GIVEN)
    for i, e in enumerate(AFTER):
        s.add_premise(e, tag=f"p{i}")
    q_defs = add(*[mul(a, "f") for a in ["a0", "a1", "a2", "a3"]], [P - 1, "*", "cmp"])
    v = s.implies(BEFORE_C, s.make_defs({i: "f" for i in INVS}))
    assert isinstance(v, Implied)
    premise = AFTER[int(v.premises[0][1:])]
    rng = random.Random(0)
    ratios = set()
    for _ in range(100):
        env = {n: rng.randrange(P) for n in AFTER_GIVEN}
        a, b = _eval(q_defs, env), _eval(premise, env)
        if b:
            ratios.add(a * pow(b, P - 2, P) % P)
    assert len(ratios) == 1


def test_variables_rejects_junk():
    import pytest
    from src.polysolver import UnsupportedExpr
    for junk in [True, {"QuotientOrZero": [1, 2]}, ["x", "/", "y"], [1, 2, 3, 4]]:
        with pytest.raises(UnsupportedExpr):
            variables(junk)


def test_polysolver_imports_nothing_from_the_verifier():
    root = Path(__file__).resolve().parents[2] / "src" / "polysolver"
    for path in root.glob("*.py"):
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.ImportFrom):
                top = (node.module or "").split(".")[0]
                assert node.level > 0 or top in ("__future__", "collections",
                                                 "dataclasses", "typing"), path
            elif isinstance(node, ast.Import):
                assert all(a.name.split(".")[0] != "src" for a in node.names), path


def test_unknown_kinds():
    s = PolySolver(VarTable(), declared=AFTER_GIVEN)
    for i, e in enumerate(AFTER):
        s.add_premise(e, tag=f"p{i}")
    for a in ["a0", "a1", "a2"]:
        s.add_range(a, 0, 255, f"r_{a}")
    assert s.implies(mul(sub(1, "cmp"), "a0")).kind == "nowrap-missing-range"
    assert s.implies(sub("a0", "a1")).kind == "no-match"
    assert s.implies(7).kind == "nonzero-constant"
    wide = PolySolver(VarTable(), declared=["c", "x", "y"])
    wide.add_premise(mul("c", add("x", "y")), tag="p")
    wide.add_range("x", 0, P - 1, "rx")
    wide.add_range("y", 0, 255, "ry")
    assert wide.implies(mul("c", "x")).kind == "nowrap-bound"


def test_add_premise_expands_nothing():
    s = PolySolver(VarTable(), declared=AFTER_GIVEN)
    for i, e in enumerate(AFTER):
        s.add_premise(e, tag=f"p{i}")
    assert s.premises_expanded == 0 and s.premises_split == 0


def test_rule_s_finds_a_sum_hidden_by_cancellation():
    # c * (x*y - x*y + a + b): only a sum after expansion. A syntactic degree
    # check would have skipped it; rule S must still split it.
    s = PolySolver(VarTable(), declared=["c", "x", "y", "a", "b"])
    s.add_premise(mul("c", add(sub(mul("x", "y"), mul("x", "y")), "a", "b")), tag="p")
    s.add_range("a", 0, 255, "ra")
    s.add_range("b", 0, 255, "rb")
    v = s.implies(mul("c", "a"))
    assert v.rule == "nowrap-split" and set(v.ranges) == {"a", "b"}


def test_rule_s_rejects_a_sum_of_squares():
    sq = add(*[mul(sub(f"a{i}", f"b{i}"), sub(f"a{i}", f"b{i}")) for i in range(4)])
    names = ["c"] + [f"{x}{i}" for x in "ab" for i in range(4)]
    s = PolySolver(VarTable(), declared=names)
    s.add_premise(mul("c", sq), tag="p")
    s.add_range("a0", 0, 255, "r")
    assert isinstance(s.implies(mul("c", "a0")), Unknown)
    assert s._premises[0].sums == []  # expanded, found nonlinear, not a sum


def _weighted(order, premise, hi=255):
    t = VarTable()
    for n in order:  # interning order decides which term the zero key makes monic
        t.var(n)
    s = PolySolver(t, declared=order)
    s.add_premise(premise, tag="p")
    for n in order:
        s.add_range(n, 0, hi, f"r_{n}")
    return s


def test_rule_s_weighted_sum_in_any_variable_order():
    # 2a + 3b = 0 with bytes: at most 1275 < p, so a = b = 0. Made monic it is
    # a + (3/2)b or (2/3)a + b, and 3/2, 2/3 are huge in F_p.
    for order in (["a", "b"], ["b", "a"]):
        s = _weighted(order, add(mul(2, "a"), mul(3, "b")))
        assert s.implies("a").rule == "nowrap-split"
        assert s.implies("b").rule == "nowrap-split"


def test_rule_s_negated_weighted_sum():
    # -2a - 3b = 0, written with p - 2 and p - 3: its negation is the small sum.
    s = _weighted(["a", "b"], add(mul(P - 2, "a"), mul(P - 3, "b")))
    assert s.implies("a").rule == "nowrap-split"


def test_rule_s_weighted_bound_edge():
    edge = (P - 1) // 5  # 2*edge + 3*edge < p, one more and it is not
    s2a3b = add(mul(2, "a"), mul(3, "b"))
    assert _weighted(["a", "b"], s2a3b, edge).implies("a").rule == "nowrap-split"
    v = _weighted(["a", "b"], s2a3b, edge + 1).implies("a")
    assert isinstance(v, Unknown) and v.kind == "nowrap-bound"


def test_rule_s_no_scaling_rescues_mixed_signs():
    # 2a - 3b = 0 holds for the bytes a = 3, b = 2: splitting it would be unsound.
    for order in (["a", "b"], ["b", "a"]):
        v = _weighted(order, add(mul(2, "a"), mul(P - 3, "b"))).implies("a")
        assert isinstance(v, Unknown) and v.kind == "nowrap-bound"


def test_rule_s_split_is_lazy_and_cached():
    s = PolySolver(VarTable(), declared=AFTER_GIVEN)
    for i, e in enumerate(AFTER):
        s.add_premise(e, tag=f"p{i}")
    for a in ["a0", "a1", "a2", "a3"]:
        s.add_range(a, 0, 255, f"r_{a}")
    for a in ["a0", "a1", "a2", "a3"]:
        assert s.implies(mul(sub(1, "cmp"), a)).rule == "nowrap-split"
    # p0 matches first and is split once for all four queries; p1 is never split.
    assert s.premises_split == 1
