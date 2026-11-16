"""One circuit dump, reduced to what the per-constraint sweep needs."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from src.lens.loader import load, machine_of
from src.lens.resolve import base_dump_path, group_dir, resolve, substitutions_path
from src.paths import POWDR_DUMPS_DIR
from src.polysolver import BABYBEAR, Expr, variables

from .tables import (
    BITWISE_LOOKUP,
    MAX_BITS,
    TUPLE_RANGE_CHECKER,
    TUPLE_SIZES,
    VARIABLE_RANGE_CHECKER,
)

MEMORY_BUS = 1
PC_STEP = 4  # pcs of consecutive instructions (OpenVM's DEFAULT_PC_STEP)
# Lookups into fixed tables: PcLookup, VariableRangeChecker, BitwiseLookup,
# TupleRangeChecker. Ids as in src/bus_interactions/__init__.py::OpenVMBusInteraction
# (not imported: that module pulls in pysmt). Memory and the execution bridge
# are stateful and belong to Step C.
STATELESS_BUSES = frozenset({2, 3, 6, 7})


@dataclass
class Circuit:
    label: str  # e.g. "008_trivial_simp"
    constraints: list[Expr]
    bus_interactions: list[dict]
    derived: dict[str, list[dict]] = field(default_factory=dict)  # name -> recipes
    columns: frozenset[str] = frozenset()

    @classmethod
    def from_machine(cls, label: str, machine: dict) -> Circuit:
        derived: dict[str, list[dict]] = {}
        for entry in machine.get("derived_columns", []):
            name, recipe = entry[-2], entry[-1]  # [is_new?, name, recipe]
            derived.setdefault(name, []).append(recipe)
        cons = machine.get("constraints", [])
        buses = machine.get("bus_interactions", [])
        # Columns come from constraints and buses only. Derived recipes can
        # mention columns the circuit no longer has.
        cols: set[str] = set()
        for e in cons:
            cols |= variables(e)
        for bi in buses:
            for e in [bi["mult"], *bi["args"]]:
                cols |= variables(e)
        return cls(label, cons, buses, derived, frozenset(cols))

    @property
    def stateless(self) -> list[dict]:
        """Stateless bus interactions: each one is a fact "mult != 0 => args in table"."""
        return [bi for bi in self.bus_interactions if bi["id"] in STATELESS_BUSES]


def load_step(group: str, block: str, step: str, root: Path | None = None) -> Circuit:
    """Load ``apc_candidate_<block>_<step>`` from the group's dump directory."""
    entry = resolve(group, block, step, root or POWDR_DUMPS_DIR)
    return Circuit.from_machine(entry.label, machine_of(load(entry.path)))


def load_substitutions(
    group: str, block: str, root: Path | None = None
) -> dict[str, Expr]:
    """The block's eliminated columns and what replaced them (empty if no file)."""
    path = substitutions_path(group_dir(group, root or POWDR_DUMPS_DIR), block)
    return {name: e for name, e in load(path)} if path else {}


def load_program(
    group: str, block: str, root: Path | None = None, p: int = BABYBEAR
) -> dict[int, tuple[int, ...]]:
    """The block's own instructions, by pc, from its unopt dump (empty if it has none).

    The dump's ``block.blocks[]`` each give a start pc and the instructions
    [opcode, a, ..., g] that follow it. This is powdr's reading of the program,
    the same one it pins every PcLookup to, so evaluating a PcLookup against
    it trusts "block = program" (the sweep reports that under its own rung).
    """
    path = base_dump_path(group_dir(group, root or POWDR_DUMPS_DIR), block)
    return program_of(load(path), p) if path else {}


def load_entry_pc(group: str, block: str, root: Path | None = None) -> int | None:
    """The pc the APC is entered at: its first basic block's start pc (None if unknown)."""
    path = base_dump_path(group_dir(group, root or POWDR_DUMPS_DIR), block)
    return entry_pc_of(load(path)) if path else None


def entry_pc_of(dump: dict) -> int | None:
    block = dump.get("block") if isinstance(dump, dict) else None
    blocks = (block or {}).get("blocks") or []
    return blocks[0]["start_pc"] if blocks else None


def program_of(dump: dict, p: int = BABYBEAR) -> dict[int, tuple[int, ...]]:
    """pc -> instruction (field elements) for every instruction of the dump's block."""
    out: dict[int, tuple[int, ...]] = {}
    block = dump.get("block") if isinstance(dump, dict) else None
    for b in (block or {}).get("blocks", []):
        for i, ins in enumerate(b["instructions"]):
            out[b["start_pc"] + PC_STEP * i] = tuple(x % p for x in ins)
    return out


def substitute(e: Expr, mapping: dict[str, Expr]) -> Expr:
    """``e`` with every mapped variable replaced; ``e`` itself is not modified."""
    if isinstance(e, str):
        return mapping.get(e, e)
    if isinstance(e, list):
        if len(e) == 2:
            return [e[0], substitute(e[1], mapping)]
        return [substitute(e[0], mapping), e[1], substitute(e[2], mapping)]
    return e


def substitute_interaction(bi: dict, mapping: dict[str, Expr]) -> dict:
    """A copy of a bus interaction with ``mapping`` applied to mult and args."""
    return {
        "id": bi["id"],
        "mult": substitute(bi["mult"], mapping),
        "args": [substitute(a, mapping) for a in bi["args"]],
    }


def interaction_columns(bi: dict) -> set[str]:
    """Columns of a bus interaction's mult and args."""
    return set().union(*(variables(e) for e in [bi["mult"], *bi["args"]]))


def byte_ranges(c: Circuit, p: int = BABYBEAR) -> list[tuple[str, int, int]]:
    """Data limbs of memory receives are bytes (the MEMORY_RECV_BYTES consequence).

    Only receives with constant multiplicity -1 and limbs that are bare
    columns count; a gated receive is skipped, which costs completeness only.
    """
    out: dict[str, tuple[str, int, int]] = {}
    for bi in c.bus_interactions:
        # Dumps spell -1 both as p - 1 and as ["-", 1].
        if bi["id"] == MEMORY_BUS and _const_value(bi["mult"], p) == p - 1:
            # args are [address_space, pointer, data..., timestamp]
            for limb in bi["args"][2:-1]:
                if isinstance(limb, str):
                    out[limb] = (limb, 0, 255)
    return list(out.values())


def _const_value(e: Expr, p: int) -> int | None:
    """The value in [0, p) of an expression with no variables, else None."""
    if isinstance(e, bool):
        return None
    if isinstance(e, int):
        return e % p
    if isinstance(e, list) and len(e) == 2 and e[0] == "-":
        v = _const_value(e[1], p)
        return None if v is None else -v % p
    if isinstance(e, list) and len(e) == 3:
        a, b = _const_value(e[0], p), _const_value(e[2], p)
        if a is None or b is None:
            return None
        return {"+": a + b, "-": a - b, "*": a * b}[e[1]] % p
    return None


def lookup_ranges(c: Circuit, p: int = BABYBEAR) -> list[tuple[str, int, int]]:
    """Ranges that the circuit's own table lookups give its bare columns.

    A lookup whose multiplicity is a nonzero constant holds for every
    witness, so its tuple is a row: [x, bits] on the range checker gives
    x < 2^bits, and [x, y, z, op] with op 0 or 1 on the bitwise table gives
    x, y < 256 (and z < 256 for op 1, z = x xor y); [x, y] on the tuple
    range checker gives x, y below TUPLE_SIZES. Gated lookups and expression
    arguments are skipped, which costs completeness only.
    """
    out: dict[str, tuple[str, int, int]] = {}

    def add(x: Expr, hi: int) -> None:
        if isinstance(x, str):
            out[x] = (x, 0, min(hi, out[x][2]) if x in out else hi)

    for bi in c.bus_interactions:
        mult, args = bi["mult"], bi["args"]
        if not _const_value(mult, p):  # gated (symbolic) or 0
            continue
        if bi["id"] == VARIABLE_RANGE_CHECKER and len(args) == 2:
            bits = args[1]
            if isinstance(bits, int) and not isinstance(bits, bool) and 0 <= bits <= MAX_BITS:
                add(args[0], 2**bits - 1)
        elif bi["id"] == BITWISE_LOOKUP and len(args) == 4 and args[3] in (0, 1):
            add(args[0], 255)
            add(args[1], 255)
            if args[3] == 1:  # every xor row has z = x xor y < 256
                add(args[2], 255)
        elif bi["id"] == TUPLE_RANGE_CHECKER and len(args) == 2:
            add(args[0], TUPLE_SIZES[0] - 1)
            add(args[1], TUPLE_SIZES[1] - 1)
    return list(out.values())


def recipe_columns(recipe: Any) -> set[str]:
    """Column names anywhere inside a derived-column recipe."""
    if isinstance(recipe, str):
        return {recipe} if "@" in recipe else set()
    if isinstance(recipe, dict):
        recipe = list(recipe.values())
    if isinstance(recipe, list):
        return set().union(*(recipe_columns(r) for r in recipe)) if recipe else set()
    return set()
