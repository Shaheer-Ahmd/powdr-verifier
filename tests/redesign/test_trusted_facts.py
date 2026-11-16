"""The APC execution assumption and program facts: trusted premises, each behind a switch."""

from src.polysolver import BABYBEAR, VarTable
from src.redesign import tables
from src.redesign.adapter import reference_solver
from src.redesign.check import check_step
from src.redesign.circuit import Circuit
from src.redesign.execution import EXECUTION_BRIDGE, chain_pairs, execution_facts

P = BABYBEAR
PC = tables.PC_LOOKUP


def circuit(label, constraints=(), buses=()):
    return Circuit.from_machine(
        label,
        {"constraints": list(constraints), "bus_interactions": list(buses), "derived_columns": []},
    )


def ex(mult, pc, ts):
    return {"id": EXECUTION_BRIDGE, "mult": mult, "args": [pc, ts]}


def instruction(i, m):
    """Receive (pc_i, ts_i) with -m, send (pc_i + 4, ts_i + 3) with m."""
    pc, ts = f"pc{i}", f"ts{i}"
    return [ex(["-", m], pc, ts), ex(m, [pc, "+", 4], [ts, "+", 3])]


# ------------------------------------------------------------ execution


def test_chain_pairs_send_with_next_receive():
    c = circuit("b", buses=instruction(0, "v0") + instruction(1, "v1"))
    pairs, first = chain_pairs(c)
    assert first["args"] == ["pc0", "ts0"]
    assert [(s["args"], r["args"]) for s, r in pairs] == [
        ([["pc0", "+", 4], ["ts0", "+", 3]], ["pc1", "ts1"])
    ]


def test_chain_rejects_out_of_order_or_mismatched_mults():
    a, b = instruction(0, "v0"), instruction(1, "v1")
    assert chain_pairs(circuit("b", buses=[a[1], a[0]] + b))[0] == []  # send first
    bad = [a[0], ex("w", ["pc0", "+", 4], ["ts0", "+", 3])] + b  # send mult != receive's
    assert chain_pairs(circuit("b", buses=bad))[0] == []


def test_runs_skips_constant_multiplicities():
    c = circuit("b", buses=[ex(["-", 0], "pc0", "ts0"), ex(0, "x", "y"),
                            {"id": PC, "mult": "v", "args": ["pc0", 1]}])
    names = [n for n, _ in execution_facts(c, None)]
    assert names == ["runs2"]  # only the symbolic one: 0 would contradict "runs"


def test_constant_entry_gives_no_fact():
    # After the solver pass the entry pc is written in; a mismatch must not
    # become a contradictory premise.
    for pc in (100, 104):
        c = circuit("a", buses=[ex(P - 1, pc, "ts0"), ex(1, 108, ["ts0", "+", 6])])
        assert execution_facts(c, 100) == []


def test_exec_bus_timestamps_follow_from_the_chain():
    # exec_bus: the chain becomes ts1 = ts0 + 3 (and pc1 = pc0 + 4).
    before = circuit("b", buses=instruction(0, "v0") + instruction(1, "v1"))
    after = circuit(
        "a",
        constraints=[["ts1", "-", ["ts0", "+", 3]], ["pc1", "-", ["pc0", "+", 4]]],
        buses=[before.bus_interactions[0], before.bus_interactions[3]],
    )
    (cmp,) = check_step(before, after, {}, ("completeness",))
    assert cmp.verified
    (cmp,) = check_step(before, after, {}, ("completeness",), trust_execution=False)
    assert not cmp.verified


# ------------------------------------------------------------ program


def test_program_facts_gated_by_mult():
    bi = {"id": PC, "mult": "m", "args": ["pc", "op", 7]}
    program = {100: (529, 7)}
    assert tables.program_facts(bi, 100, program) == [["m", "*", ["op", "-", 529]]]
    assert tables.program_facts(bi, 100, program, mult_value=1) == [["op", "-", 529]]
    assert tables.program_facts(bi, 100, program, mult_value=0) == []
    assert tables.program_facts(bi, 104, program) == []  # pc not covered
    assert tables.program_facts(bi, 100, {100: (529,)}) == []  # wrong length


def test_program_pins_flags_once_pc_and_mult_are_known():
    # opcode = 528 + f1 with boolean f0, f1 and f0 + f1 = v; the row says 529.
    ref = circuit(
        "b",
        constraints=[["f0", "*", ["f0", "-", 1]], ["f1", "*", ["f1", "-", 1]],
                     [["f0", "+", "f1"], "-", "v"]],
        buses=instruction(0, "v")
        + [{"id": PC, "mult": "v", "args": ["pc0", [528, "+", "f1"]]}],
    )
    s = reference_solver(VarTable(), ref, constants=True, entry_pc=100, program={100: (529,)})
    assert s.normal_form("f1") == (((), 1),)
    assert s.normal_form("f0") == ()
    # Without the execution assumption, neither the pc nor the mult is known.
    s = reference_solver(VarTable(), ref, constants=True, entry_pc=100, program={100: (529,)},
                         trust_execution=False)
    assert s.normal_form("f1") != (((), 1),)
    # Without program facts, the pc is known but the opcode row is not used.
    s = reference_solver(VarTable(), ref, constants=True, entry_pc=100, program={100: (529,)},
                         use_program_facts=False)
    assert s.normal_form("pc0") == (((), 100),)
    assert s.normal_form("f1") != (((), 1),)


def test_apc_is_valid_is_not_assumed_active():
    # The last step gates everything by the APC's is_valid: not assumed to be 1.
    c = circuit("a", buses=[ex(["-", "is_valid@9"], "pc0", "ts0"),
                            {"id": PC, "mult": "is_valid@9", "args": ["pc0", 1]},
                            {"id": PC, "mult": "is_valid_1@3", "args": ["pc1", 1]}])
    assert [e for _, e in execution_facts(c, None)] == [["is_valid_1@3", "-", 1]]
