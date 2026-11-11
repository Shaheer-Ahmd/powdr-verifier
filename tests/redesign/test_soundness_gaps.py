"""Soundness gaps: values for lookup-only columns, opaque recipes, the trusted program."""

from src.polysolver import BABYBEAR, Implied, PolySolver, VarTable
from src.redesign import tables
from src.redesign.check import check, check_step
from src.redesign.circuit import Circuit, load_program, lookup_ranges, program_of

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


# ------------------------------------------------------------ opaque recipes


def test_markers_with_an_opaque_recipe_get_zero():
    # remove_disconnected drops m*(m - 1) for diff_marker columns whose recipe
    # is an IfEqZero chain. Soundness skips the recipe; 0 satisfies booleanity.
    cmp, snd = check("keccak", "2104736", "016", "017")
    markers = [c for c in snd.mapping.defs if c.startswith("diff_marker")]
    assert len(markers) == 8
    assert all(snd.mapping.defs[c] == 0 for c in markers)
    assert {snd.mapping.source[c] for c in markers} == {"zero witness"}
    assert not [o for o in snd.obligations if o.reason.startswith("opaque")]


def test_opaque_recipe_is_skipped_only_in_soundness():
    recipe = {"IfEqZero": ["a", {"Constant": 0}, {"Constant": 1}]}
    with_m = circuit("m", [["a", "*", ["a", "-", 1]], ["m", "*", ["m", "-", 1]]],
                     derived=[[False, "m", recipe]])
    without = circuit("n", [["a", "*", ["a", "-", 1]]])
    # Soundness (m is Before-only): the recipe is skipped and m := 0 is kept.
    (snd,) = check_step(with_m, without, {}, ("soundness",))
    assert snd.verified and snd.mapping.defs["m"] == 0
    # Completeness (m is After-only): the recipe is what the prover runs.
    (cmp,) = check_step(without, with_m, {}, ("completeness",))
    assert not cmp.verified
    assert [o.reason for o in cmp.obligations if o.rung == "undecided"] == ["opaque IfEqZero"]


def test_zero_witness_is_kept_only_if_the_constraints_hold():
    before = circuit("b", [["m", "-", 1]], derived=[[False, "m", {"IfEqZero": [0, 0, 1]}]])
    (snd,) = check_step(before, circuit("a"), {}, ("soundness",))
    assert snd.mapping.unmapped == {"m"} and not snd.verified


def test_opaque_lookup_only_column_falls_through_to_a_root():
    # diff_val's shape: 0 is not a row of [x - 1, 0, 0, 0]; the root 1 is.
    recipe = {"IfEqZero": ["a", {"Constant": 1}, {"QuotientOrZero": [["a", "-", 1], 1]}]}
    before = circuit("b", [["a", "*", ["a", "-", 1]]],
                     [lookup(6, ["x", "-", 1], 0, 0, 0)], [[False, "x", recipe]])
    after = circuit("a", [["a", "*", ["a", "-", 1]]])
    (snd,) = check_step(before, after, {}, ("soundness",))
    assert snd.verified and snd.mapping.source["x"] == "lookup-only root"


# ------------------------------------------------------------ the trusted program


def test_program_rows_come_from_the_unopt_block():
    program = load_program("keccak", "2099512")
    assert list(program) == [2099512 + 4 * i for i in range(5)]
    assert program[2099516] == (531, 4, 8, 476, 1, 2, 1, 0)
    assert program_of({"machine": {}}) == {}  # a dump with no block


def test_pc_lookup_is_decided_only_inside_the_block():
    program = {100: (1, 2, 3), 104: (4, 5, 6)}
    assert tables.is_row(2, [100, 1, 2, 3], program) is True
    assert tables.is_row(2, [104, 1, 2, 3], program) is False  # another instruction
    assert tables.is_row(2, [100, 1, 2], program) is False
    assert tables.is_row(2, [108, 1, 2, 3], program) is None  # a pc the block lacks
    assert tables.is_row(2, [100, 1, 2, 3]) is None  # no program: not evaluated
    assert tables.is_row(2, [100, 1, 2, 3], {}) is None


def test_pc_lookup_rungs():
    program = {100: (1, 2, 3)}
    pc_rows = [lookup(2, 100, 1, 2, 3), lookup(2, 100, 1, 2, 4), lookup(2, 104, 1, 2, 3)]
    before, after = circuit("b", buses=pc_rows), circuit("a")
    (snd,) = check_step(before, after, {}, ("soundness",), program=program)
    assert [(o.rung, o.reason) for o in snd.obligations] == [
        ("evaluated-program", ""),
        ("undecided", "bus: constant args not a row"),
        ("undecided", "bus: pc_lookup outside the block"),
    ]
    (snd,) = check_step(before, after, {}, ("soundness",))
    assert {o.reason for o in snd.obligations} == {"bus: pc_lookup not trusted"}
    # Congruence needs no table: a PcLookup the reference has is discharged either way.
    (snd,) = check_step(before, before, {}, ("soundness",))
    assert {o.rung for o in snd.obligations} == {"identical"}


# ------------------------------------------------------------ squared is-zero


def test_squared_is_zero_completeness_needs_lookup_ranges():
    # f * sum (a_i - b_i)^2 - cmp: in the fork for sum = 0, rule S needs a
    # range for every limb. The a_i are memory sends; their only range is
    # their own bitwise lookup [a_i, a_i, 0, 1].
    for block in ("2103472", "2100224"):
        (cmp,) = check("keccak", block, "047", "048", ("completeness",))
        assert cmp.verified and cmp.counts("constraint")["quotient-split"] == 1
        (cmp,) = check("keccak", block, "047", "048", ("completeness",),
                       use_lookup_ranges=False)
        assert [o.reason for o in cmp.obligations if o.rung == "undecided"] == [
            "quotient case not proved"
        ]


def test_lookup_ranges_come_from_ungated_lookups_of_bare_columns():
    c = circuit("c", buses=[
        lookup(3, "x", 17), lookup(3, "x", 12), lookup(3, ["y", "+", 1], 8),
        lookup(3, "g", 8, mult="sel"), lookup(3, "z", 8, mult=0), lookup(3, "w", "bits"),
        lookup(6, "u", "v", 0, 1), lookup(6, "s", "s", 0, 7), lookup(2, "pc", 1),
    ])
    assert sorted(lookup_ranges(c)) == [("u", 0, 255), ("v", 0, 255), ("x", 0, 4095)]
