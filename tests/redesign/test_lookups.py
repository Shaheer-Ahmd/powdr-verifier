"""lookups: every Case agrees with is_row, and both sides read the same cases."""

import itertools

import pytest

from src.polysolver import BABYBEAR, Bounded, PolySolver, VarTable, Zero, poly
from src.redesign import lookups as L

P = BABYBEAR
BYTES = [0, 1, 2, 127, 128, 254, 255, 256, 300]
PROGRAM = {100: (529, 7), 104: (530, 0)}


def lookup(bus, *args, mult=1):
    return {"id": bus, "mult": mult, "args": list(args)}


def ev(e, env):
    return poly.expand(e, lambda n: poly.const(env[n], P), P).get((), 0)


def written(e):
    return e if isinstance(e, int) else None


def true(g, env):
    """A goal holds under the assignment."""
    if isinstance(g, Zero):
        return ev(g.e, env) == 0
    assert isinstance(g, Bounded)
    return ev(g.e, env) <= g.hi


def check_case(c, bus, env, args, program=None):
    """For one assignment: if the case is selected, it agrees with is_row as it claims."""
    if not all(true(g, env) for g in c.when):
        return False
    row = L.is_row(bus, [ev(a, env) for a in args], program)
    holds = all(true(g, env) for g in c.row)
    if row:
        assert holds, (c.name, env)  # => : sound as a premise
    if c.exact and holds:
        assert row, (c.name, env)  # <= : sound as a proof
    return True


# Argument patterns: a variable, or a constant written in. Each pattern gets
# its own cases (value() reads the written constants), checked on a grid.
XOR_PATTERNS = [
    ("x", "y", "z", 1), ("x", 0, "z", 1), (0, "y", "z", 1), ("x", 255, "z", 1),
    (255, "y", "z", 1), ("x", "y", 0, 1), ("x", "x", "z", 1), (3, 5, "z", 1),
    ("x", "y", "z", 0), ("x", "y", "z", "o"),
]


@pytest.mark.parametrize("pattern", XOR_PATTERNS)
def test_bitwise_cases_agree_with_is_row(pattern):
    names = sorted({a for a in pattern if isinstance(a, str)})
    bi = lookup(L.BITWISE_LOOKUP, *pattern)
    cs = L.cases(bi, written)
    if "o" in names:  # op unknown: no case can be picked
        assert cs == []
        return
    assert cs
    selected = set()
    envs = [dict(zip(names, vals)) for vals in itertools.product(BYTES, repeat=len(names))]
    # Also z = x xor y (and one off), so the rows themselves are in the grid.
    for x, y in itertools.product(BYTES, BYTES):
        for dz in (0, 1):
            full = {"x": x, "y": y, "z": (x ^ y) + dz}
            envs.append({n: full[n] for n in names})
    for env in envs:
        for c in cs:
            if check_case(c, bi["id"], env, bi["args"]):
                selected.add(c.name)
    assert selected  # some case was selected and checked


@pytest.mark.parametrize("bits", [0, 1, 2, 8, 17])
def test_range_cases_agree_with_is_row(bits):
    bi = lookup(L.VARIABLE_RANGE_CHECKER, "x", bits)
    cs = L.cases(bi, written)
    assert cs
    hi = 2**bits
    for x in {0, 1, 2, hi - 1, hi, hi + 1, P - 1}:
        for c in cs:
            check_case(c, bi["id"], {"x": x}, bi["args"])


def test_range_wider_than_max_bits_has_no_case():
    assert L.cases(lookup(L.VARIABLE_RANGE_CHECKER, "x", L.MAX_BITS + 1), written) == []


def test_tuple_cases_agree_with_is_row():
    bi = lookup(L.TUPLE_RANGE_CHECKER, "x", "y")
    (c,) = L.cases(bi, written)
    for x, y in itertools.product([0, 255, 256], [0, 2047, 2048]):
        check_case(c, bi["id"], {"x": x, "y": y}, bi["args"])


def test_program_cases_agree_with_is_row():
    bi = lookup(L.PC_LOOKUP, 100, "op", "a")
    (c,) = L.cases(bi, written, PROGRAM)
    for op, a in itertools.product([528, 529, 530], [0, 7, 8]):
        check_case(c, bi["id"], {"op": op, "a": a}, bi["args"], PROGRAM)
    assert L.cases(bi, written) == []  # no program: no case
    assert L.cases(lookup(L.PC_LOOKUP, 108, "op", "a"), written, PROGRAM) == []  # not covered
    assert L.cases(lookup(L.PC_LOOKUP, 100, "op"), written, PROGRAM) == []  # wrong length
    assert L.cases(lookup(L.PC_LOOKUP, "pc", "op", "a"), written, PROGRAM) == []  # pc unknown


def test_bound_reads_the_exact_cases():
    assert L.bound(lookup(L.VARIABLE_RANGE_CHECKER, "x", 8), 0) == 256
    assert L.bound(lookup(L.TUPLE_RANGE_CHECKER, "x", "y"), 1) == 2048
    assert L.bound(lookup(L.BITWISE_LOOKUP, "x", "y", "z", 1), 0) == 256
    assert L.bound(lookup(L.BITWISE_LOOKUP, "x", "y", "z", 1), 2) is None  # z: not exact
    assert L.bound(lookup(L.PC_LOOKUP, 100, "op"), 1) is None


# ------------------------------------------------------------ both sides


def solver(names, premises=(), ranges=()):
    s = PolySolver(VarTable(), declared=names)
    for i, e in enumerate(premises):
        s.add_premise(e, f"p{i}")
    for x, hi in ranges:
        s.add_range(x, 0, hi, f"r:{x}")
    s.propagate()
    return s


def test_semantic_constant_selects_the_case_on_both_sides():
    # y is a column pinned to 0, not a written 0: xor gives z = x.
    s = solver(["x", "y", "z"], premises=["y"])
    L.assume(s, "r", [lookup(L.BITWISE_LOOKUP, "x", "y", "z", 1)])
    assert s.implies(["z", "-", "x"]).__class__.__name__ == "Implied"
    assert s.interval("z")[:2] == (0, 255)  # and the ranges
    # The goal side picks the same case.
    t = solver(["x", "y", "z"], premises=["y", ["z", "-", "x"]], ranges=[("x", 255)])
    proved = L.prove(t, lookup(L.BITWISE_LOOKUP, "x", "y", "z", 1))
    assert proved is not None and proved.case == "xor-y0"


def test_assumed_lookup_proves_itself_renamed():
    # As in the sweep: candidate columns a2, b2, c2 are defined over the reference's.
    ref = [lookup(L.BITWISE_LOOKUP, "a", "b", "c", 1)]
    s = solver(["a", "b", "c"], premises=[["b", "-", 255]])
    L.assume(s, "r", ref)
    defs = s.make_defs({"a2": "a", "b2": "b", "c2": "c"})
    proved = L.prove(s, lookup(L.BITWISE_LOOKUP, "a2", "b2", "c2", 1), defs)
    assert proved is not None and proved.case == "xor-y255"
    # A wrong z is not proved.
    defs = s.make_defs({"a2": "a", "b2": "b", "c2": ["c", "+", 1]})
    assert L.prove(s, lookup(L.BITWISE_LOOKUP, "a2", "b2", "c2", 1), defs) is None


def test_gated_lookup_gives_gated_facts_and_no_ranges():
    s = solver(["x", "z", "m"])
    L.assume(s, "r", [lookup(L.BITWISE_LOOKUP, "x", 0, "z", 1, mult="m")])
    assert s.interval("z") is None and s.interval("x") is None
    assert s.implies(["m", "*", ["z", "-", "x"]]).__class__.__name__ == "Implied"
    assert s.implies(["z", "-", "x"]).__class__.__name__ == "Unknown"


def test_zero_mult_gives_nothing():
    s = solver(["x", "z", "m"], premises=["m"])
    L.assume(s, "r", [lookup(L.BITWISE_LOOKUP, "x", 0, "z", 1, mult="m")])
    assert s.interval("x") is None


def test_program_case_needs_the_program_and_a_known_pc():
    bi = lookup(L.PC_LOOKUP, "pc", "op", "a", mult="m")
    s = solver(["pc", "op", "a", "m"], premises=[["pc", "-", 100], ["m", "-", 1]])
    L.assume(s, "r", [bi])  # no program: nothing
    assert s.implies(["op", "-", 529]).__class__.__name__ == "Unknown"
    L.assume(s, "r", [bi], program=PROGRAM)
    assert s.implies(["op", "-", 529]).__class__.__name__ == "Implied"
    assert s.implies(["a", "-", 7]).__class__.__name__ == "Implied"
    # Goal side: the same lookup is proved from the program row.
    proved = L.prove(s, bi, program=PROGRAM)
    assert proved is not None and proved.case == "pc100"
    assert L.prove(s, bi) is None  # untrusted: no program, no proof


def test_gated_candidate_lookup_is_proved_where_mult_is_nonzero():
    # The reference gives z = x only where m != 0; the candidate's lookup has
    # the same gate, so it holds: m != 0 => (x, 0, z, xor) is a row.
    s = solver(["x", "z", "m"], premises=[["m", "*", ["z", "-", "x"]]], ranges=[("x", 255)])
    bi = lookup(L.BITWISE_LOOKUP, "x", 0, "z", 1, mult="m")
    proved = L.prove(s, bi)
    assert proved is not None and proved.case == "xor-y0-gated"
    # Ungated (mult 1), the same premises do not give a row.
    assert L.prove(s, lookup(L.BITWISE_LOOKUP, "x", 0, "z", 1)) is None


def test_gating_keeps_bounded_goals_unconditional():
    # A range cannot be gated: without x's range the gated case is not proved.
    s = solver(["x", "z", "m"], premises=[["m", "*", ["z", "-", "x"]]])
    assert L.prove(s, lookup(L.BITWISE_LOOKUP, "x", 0, "z", 1, mult="m")) is None


def test_gate_must_match_the_premise():
    # z = x where n != 0 says nothing where m != 0.
    s = solver(["x", "z", "m", "n"], premises=[["n", "*", ["z", "-", "x"]]], ranges=[("x", 255)])
    assert L.prove(s, lookup(L.BITWISE_LOOKUP, "x", 0, "z", 1, mult="m")) is None


def test_mult_implied_zero_proves_any_lookup():
    s = solver(["x", "m"], premises=["m"])
    proved = L.prove(s, lookup(L.VARIABLE_RANGE_CHECKER, "x", 8, mult="m"))
    assert proved is not None and proved.case == "mult-zero"
    # A constant mult is never gated: x has no range, so nothing is proved.
    assert L.prove(s, lookup(L.VARIABLE_RANGE_CHECKER, "x", 8)) is None
