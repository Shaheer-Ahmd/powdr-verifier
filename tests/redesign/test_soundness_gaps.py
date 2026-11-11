"""Soundness gaps: values for lookup-only columns, opaque recipes, the trusted program."""

from src.polysolver import BABYBEAR, Implied, PolySolver, VarTable
from src.redesign import tables
from src.redesign.check import check, check_step
from src.redesign.circuit import Circuit

P = BABYBEAR
LOW = "rd_aux_cols__base__timestamp_lt_aux__lower_decomp__0_3@122"


def circuit(label, constraints=(), buses=(), derived=()):
    return Circuit.from_machine(
        label,
        {
            "constraints": list(constraints),
            "bus_interactions": list(buses),
            "derived_columns": list(derived),
        },
    )


def lookup(bus, *args, mult=1):
    return {"id": bus, "mult": mult, "args": list(args)}


# ------------------------------------------------------------ lookup-only values


def test_timestamp_gadget_takes_the_root_of_the_tightest_lookup():
    # [low, 17] and [15360*low - 61440, 12]: 0 makes the second argument huge;
    # the root low = 4 is the honest split (low limb = the gap, high limb = 0).
    (snd,) = check("keccak", "2099512", "035", "036", ("soundness",))
    assert snd.verified
    assert snd.mapping.defs[LOW] == 4
    assert snd.mapping.source[LOW] == "lookup-only root"


def test_zero_is_tried_first():
    before = circuit("b", buses=[lookup(3, "x", 8), lookup(3, ["x", "+", 3], 4)])
    (snd,) = check_step(before, circuit("a"), {}, ("soundness",))
    assert snd.verified and snd.mapping.defs["x"] == 0


def test_roots_are_tried_tightest_bound_first():
    # 0 fails [x - 1, 12]. The roots 1 (bound 2^12) and 3 (bound 2^4) both make
    # every lookup a row, and the tighter lookup's root wins.
    wide = lookup(3, ["x", "-", 1], 12)
    tight = lookup(3, [3, "-", "x"], 4)
    (snd,) = check_step(circuit("b", buses=[wide, tight]), circuit("a"), {}, ("soundness",))
    assert snd.mapping.defs["x"] == 3 and snd.verified
    # With the tight lookup gone, the wide one's root is next.
    (snd,) = check_step(circuit("b", buses=[wide]), circuit("a"), {}, ("soundness",))
    assert snd.mapping.defs["x"] == 1 and snd.verified


def test_bitwise_arguments_have_a_bound():
    # diff_val's shape: [x - 1, 0, 0, 0] on the bitwise bus. 0 gives p - 1.
    before = circuit("b", buses=[lookup(6, ["x", "-", 1], 0, 0, 0)])
    (snd,) = check_step(before, circuit("a"), {}, ("soundness",))
    assert snd.verified and snd.mapping.defs["x"] == 1


def test_no_value_fits_stays_unmapped():
    before = circuit("b", buses=[lookup(3, ["x", "-", 1], 4), lookup(3, ["x", "-", 20], 4)])
    (snd,) = check_step(before, circuit("a"), {}, ("soundness",))
    assert not snd.verified
    assert snd.mapping.unmapped_reason == {"x": "lookup-only"}
    assert {o.reason for o in snd.obligations} == {"lookup-only column"}


def test_stateful_use_declines():
    recv = {"id": 1, "mult": P - 1, "args": [1, 0, "x", 0, 0, 0, 5]}
    before = circuit("b", buses=[lookup(3, "x", 8), recv])
    (snd,) = check_step(before, circuit("a"), {}, ("soundness",))
    assert snd.mapping.unmapped == {"x"}


def test_bound_orders_only_the_checked_arguments():
    assert tables.bound(lookup(3, "x", 17), 0) == 2**17
    assert tables.bound(lookup(3, "x", 17), 1) is None
    assert tables.bound(lookup(3, "x", "bits"), 0) is None
    assert tables.bound(lookup(6, "x", "y", "z", 1), 1) == 256
    assert tables.bound(lookup(6, "x", "y", "z", 1), 2) is None
    assert tables.bound(lookup(2, "x"), 0) is None


def test_lookup_holds_needs_a_row_or_mult_zero():
    s = PolySolver(VarTable(), declared=["a"])
    defs = s.make_defs({"x": 300})
    assert tables.lookup_holds(s, lookup(3, "x", 12), defs)
    assert not tables.lookup_holds(s, lookup(3, "x", 8), defs)
    assert tables.lookup_holds(s, lookup(3, "x", 8, mult=0), defs)
    assert not tables.lookup_holds(s, lookup(3, "a", 8), defs)  # not a constant
    assert not tables.lookup_holds(s, lookup(3, "nope", 8), defs)  # no value


def test_linear_root():
    s = PolySolver(VarTable(), declared=["a", "b"])
    s.add_premise(["b", "-", 2], "b")
    defs = s.make_defs({"y": ["a", "-", "a"]})
    assert s.linear_root(["x", "-", 4], "x") == 4
    assert s.linear_root([[15360, "*", "x"], "-", 61440], "x") == 4
    assert s.linear_root([["x", "*", "b"], "+", "y"], "x", defs) == 0  # b = 2, y = 0
    assert s.linear_root(["x", "*", "x"], "x") is None
    assert s.linear_root(["x", "+", "a"], "x") is None  # the rest is not a constant
    assert s.linear_root(["x", "-", "x"], "x") is None
    assert s.linear_root(7, "x") is None


def test_extend_defs_adds_one_definition():
    s = PolySolver(VarTable(), declared=["a"])
    s.add_premise(["a", "-", 1], "a")
    base = s.make_defs({"y": "a"})
    more = s.extend_defs(base, "x", ["a", "+", 1])
    assert isinstance(s.implies(["x", "-", ["y", "+", 1]], more), Implied)
    assert not base.defines(s.table.var("x"))  # the original is untouched
    again = s.extend_defs(more, "x", 5)  # a second value replaces the first
    assert isinstance(s.implies(["x", "-", 5], again), Implied)
