"""M4i: lookup facts as premises, and the table-semantics rung."""

from src.polysolver import BABYBEAR, PolySolver, VarTable
from src.redesign import tables
from src.redesign.check import check_step
from src.redesign.circuit import Circuit

P = BABYBEAR
RANGE, BITWISE = tables.VARIABLE_RANGE_CHECKER, tables.BITWISE_LOOKUP


def circuit(label, constraints=(), buses=()):
    return Circuit.from_machine(
        label,
        {"constraints": list(constraints), "bus_interactions": list(buses), "derived_columns": []},
    )


def lookup(bus, *args, mult=1):
    return {"id": bus, "mult": mult, "args": list(args)}


def one(report, kind="bus"):
    (o,) = [o for o in report.obligations if o.kind == kind]
    return o


# ------------------------------------------------------------ interval


def test_interval_of_affine_forms():
    s = PolySolver(VarTable(), declared=["a", "b", "c"])
    s.add_range("a", 0, 255, "a")
    s.add_range("b", 0, 255, "b")
    assert s.interval("a") == (0, 255, ("a",))
    assert s.interval([255, "-", "a"])[:2] == (0, 255)
    assert s.interval([["a", "+", "b"], "+", 1])[:2] == (1, 511)
    assert s.interval(["a", "-", "b"]) is None  # can be negative: wraps
    assert s.interval("c") is None  # no range
    assert s.interval(["a", "*", "b"]) is None  # not affine
    assert s.interval(7)[:2] == (7, 7)


# ------------------------------------------------------------ facts


def test_xor_facts():
    f = tables.lookup_facts
    assert f(lookup(BITWISE, "b", 255, "a", 1)) == [[["a", "+", "b"], "-", 255]]
    assert f(lookup(BITWISE, "x", 0, "z", 1)) == [["z", "-", "x"]]
    assert f(lookup(BITWISE, "x", "y", 0, 1)) == [["x", "-", "y"]]
    assert f(lookup(BITWISE, "x", "x", "z", 1)) == ["z"]
    assert f(lookup(BITWISE, "x", 7, "z", 1)) == []  # xor 7: not polynomial here
    assert f(lookup(BITWISE, "x", 0, "z", 1, mult="m")) == [["m", "*", ["z", "-", "x"]]]
    assert f(lookup(BITWISE, "x", 0, "z", 1, mult=0)) == []
    assert f(lookup(RANGE, "x", 1)) == [["x", "*", ["x", "-", 1]]]


def test_xor_255_closes_low_degree_bus_completeness():
    # Before: a = b xor 255 by lookup. After: a + b - 255 = 0 and a byte check on b.
    before = circuit("b", buses=[lookup(BITWISE, "b", 255, "a", 1)])
    after = circuit(
        "a", constraints=[[["a", "+", "b"], "-", 255]], buses=[lookup(BITWISE, "b", 0, 0, 0)]
    )
    (cmp,) = check_step(before, after, {}, ("completeness",))
    assert cmp.verified
    (cmp,) = check_step(before, after, {}, ("completeness",), use_lookup_facts=False,
                        use_table_rung=False)
    assert not cmp.verified


def test_xor_255_closes_low_degree_bus_soundness():
    before = circuit("b", buses=[lookup(BITWISE, "b", 255, "a", 1)])
    after = circuit(
        "a", constraints=[[["a", "+", "b"], "-", 255]], buses=[lookup(BITWISE, "b", 0, 0, 0)]
    )
    (snd,) = check_step(before, after, {}, ("soundness",))
    assert one(snd).rung == "table-semantics" and snd.verified


# ------------------------------------------------------------ the rung, negatives


def test_wrong_xor_is_not_discharged():
    # a + b = 254 is not a = b xor 255.
    before = circuit("b", buses=[lookup(BITWISE, "b", 255, "a", 1)])
    after = circuit(
        "a", constraints=[[["a", "+", "b"], "-", 254]], buses=[lookup(BITWISE, "b", 0, 0, 0)]
    )
    (snd,) = check_step(before, after, {}, ("soundness",))
    assert one(snd).rung == "undecided"


def test_byte_check_needs_a_range():
    ref = circuit("r", buses=[lookup(RANGE, "x", 9)])  # x < 512 only
    cand = circuit("c", buses=[lookup(BITWISE, "x", 0, 0, 0)])
    (snd,) = check_step(cand, ref, {}, ("soundness",))
    assert one(snd).rung == "undecided"
    ref = circuit("r", buses=[lookup(RANGE, "x", 8)])
    (snd,) = check_step(cand, ref, {}, ("soundness",))
    assert one(snd).rung == "table-semantics"


def test_range_check_width():
    ref = circuit("r", buses=[lookup(RANGE, "x", 8)])
    wider = circuit("c", buses=[lookup(RANGE, "x", 9)])
    narrower = circuit("c", buses=[lookup(RANGE, "x", 7)])
    assert one(check_step(wider, ref, {}, ("soundness",))[0]).rung == "table-semantics"
    assert one(check_step(narrower, ref, {}, ("soundness",))[0]).rung == "undecided"


def test_gated_reference_lookup_gives_no_range():
    ref = circuit("r", buses=[lookup(RANGE, "x", 8, mult="m")])
    cand = circuit("c", buses=[lookup(RANGE, "x", 8)])
    (snd,) = check_step(cand, ref, {}, ("soundness",))
    assert one(snd).rung == "undecided"


def test_self_xor_is_a_byte_check():
    ref = circuit("r", buses=[lookup(BITWISE, "x", 0, 0, 0)])
    cand = circuit("c", buses=[lookup(BITWISE, "x", "x", 0, 1)])
    (snd,) = check_step(cand, ref, {}, ("soundness",))
    assert one(snd).rung == "table-semantics"
    cand = circuit("c", buses=[lookup(BITWISE, "x", "x", 1, 1)])  # x xor x is 0, not 1
    (snd,) = check_step(cand, ref, {}, ("soundness",))
    assert one(snd).rung == "undecided"


# ------------------------------------------------------------ xor of bits

BOOL = lambda v: [v, "*", [v, "-", 1]]  # noqa: E731
OR = [[["c1", "+", "c2"], "-", ["c1", "*", "c2"]], "-", "a"]  # a = c1 OR c2
# powdr's OR through the xor table: c1 xor c2 = 2a - c1 - c2
OR_LOOKUP = lookup(BITWISE, "c1", "c2", [[[2, "*", "a"], "-", "c1"], "-", "c2"], 1)


def test_bit_xor_fact_needs_bits():
    is_bit = lambda e: e in ("c1", "c2")  # noqa: E731
    xor = ["z", "-", [["c1", "+", "c2"], "-", [2, "*", ["c1", "*", "c2"]]]]
    assert tables.lookup_facts(lookup(BITWISE, "c1", "c2", "z", 1), is_bit=is_bit) == [xor]
    assert tables.lookup_facts(lookup(BITWISE, "c1", "y", "z", 1), is_bit=is_bit) == []
    assert tables.lookup_facts(lookup(BITWISE, "c1", "c2", "z", 1)) == []  # no ranges known


def test_bit_xor_closes_or_both_ways():
    with_lookup = circuit("l", constraints=[BOOL("c1"), BOOL("c2")], buses=[OR_LOOKUP])
    with_or = circuit("o", constraints=[BOOL("c1"), BOOL("c2"), OR])
    (cmp,) = check_step(with_lookup, with_or, {}, ("completeness",))
    assert cmp.verified  # fact: the lookup gives the OR polynomial
    (snd,) = check_step(with_lookup, with_or, {}, ("soundness",))
    assert one(snd).rung == "table-semantics" and snd.verified


def test_bit_xor_needs_bits_and_the_right_z():
    # Without booleanity c1, c2 are not known to be bits: x + y - 2xy is not xor.
    with_or = circuit("o", constraints=[OR])
    (snd,) = check_step(circuit("l", buses=[OR_LOOKUP]), with_or, {}, ("soundness",))
    assert one(snd).rung == "undecided"
    # AND is not xor.
    with_and = circuit("o", constraints=[BOOL("c1"), BOOL("c2"), [["c1", "*", "c2"], "-", "a"]])
    (snd,) = check_step(circuit("l", buses=[OR_LOOKUP]), with_and, {}, ("soundness",))
    assert one(snd).rung == "undecided"


# ------------------------------------------------------------ tuple range checker

TUPLE = tables.TUPLE_RANGE_CHECKER


def test_tuple_rows():
    assert tables.is_row(TUPLE, [255, 2047]) is True
    assert tables.is_row(TUPLE, [256, 0]) is False
    assert tables.is_row(TUPLE, [0, 2048]) is False


def test_tuple_rung_and_ranges():
    ref = circuit("r", buses=[lookup(BITWISE, "x", "y", 0, 0)])  # x, y bytes
    assert one(check_step(circuit("c", buses=[lookup(TUPLE, "x", "y")]), ref, {},
                          ("soundness",))[0]).rung == "table-semantics"
    ref = circuit("r", buses=[lookup(RANGE, "x", 9)])  # x < 512: too wide for slot 0
    assert one(check_step(circuit("c", buses=[lookup(TUPLE, "x", 0)]), ref, {},
                          ("soundness",))[0]).rung == "undecided"
    assert one(check_step(circuit("c", buses=[lookup(TUPLE, 0, "x")]), ref, {},
                          ("soundness",))[0]).rung == "table-semantics"
    # A reference tuple lookup gives its ranges: x < 256, y < 2048.
    ref = circuit("r", buses=[lookup(TUPLE, "x", "y")])
    assert one(check_step(circuit("c", buses=[lookup(RANGE, "y", 11)]), ref, {},
                          ("soundness",))[0]).rung == "table-semantics"
    assert one(check_step(circuit("c", buses=[lookup(RANGE, "y", 10)]), ref, {},
                          ("soundness",))[0]).rung == "undecided"


# ------------------------------------------------------------ range_constraints shapes

E = ["a", "-", [2, "*", "b"]]  # a composite: its interval crosses 0


def test_bit_check_on_composite_from_its_polynomial():
    # range_constraints writes a dropped [E, 1] as E * (E - 1) = 0.
    cand = circuit("c", buses=[lookup(RANGE, E, 1)])
    ref = circuit("r", constraints=[[E, "*", [E, "-", 1]]])
    assert one(check_step(cand, ref, {}, ("soundness",))[0]).rung == "table-semantics"
    ref = circuit("r", constraints=[[E, "*", [E, "-", 2]]])  # E in {0, 2}: not a bit
    assert one(check_step(cand, ref, {}, ("soundness",))[0]).rung == "undecided"


def test_zero_check_on_composite():
    cand = circuit("c", buses=[lookup(RANGE, E, 0)])
    assert one(check_step(cand, circuit("r", constraints=[E]), {},
                          ("soundness",))[0]).rung == "table-semantics"


def test_xor_output_is_a_byte():
    from src.redesign.circuit import lookup_ranges
    ref = circuit("r", buses=[lookup(BITWISE, "x", "y", "z", 1)])
    assert ("z", 0, 255) in lookup_ranges(ref)
    cand = circuit("c", buses=[lookup(BITWISE, "z", 0, 0, 0)])
    assert one(check_step(cand, ref, {}, ("soundness",))[0]).rung == "table-semantics"
    ref = circuit("r", buses=[lookup(BITWISE, "x", "y", "z", 0)])  # op 0: no z range from this lookup
    assert ("z", 0, 255) not in lookup_ranges(ref)
