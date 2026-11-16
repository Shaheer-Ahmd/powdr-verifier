"""The APC execution assumption, as polynomial premises (switch: trust_execution).

An APC replaces one basic block. powdr optimizes its circuit as if, whenever
the APC row is active, the block runs from start to end:

  entry   - execution enters at the block's start pc (the APC is only ever
            used there)
  runs    - every instruction executes: its multiplicity on the execution
            bus and on the PcLookup is 1 (powdr's solver pass sets them to 1;
            its last step puts the APC's own is_valid there, which is not
            assumed to be 1: see execution_facts)
  chain   - instruction i's execution-bus send (pc', ts') is consumed by
            instruction i+1's receive (pc, ts): the arguments are equal
            (the exec_bus pass writes these as equalities)

None of this follows from the circuit's constraints: the original circuit is
one chip row per instruction, each with its own is_valid, linked only through
the execution bus, a global multiset. So these are trusted premises, behind
their own switch, and reported as such.

Instruction order is the dump's order of execution-bus interactions. It is
accepted only if the interactions alternate receive, send, receive, send, ...
starting with a receive, each send having its receive's multiplicity; else
no chain fact is given (which costs completeness only).
"""

from __future__ import annotations

from src.polysolver import BABYBEAR, Expr, variables

from .circuit import Circuit, _const_value
from .lookups import PC_LOOKUP

EXECUTION_BRIDGE = 0  # [pc, timestamp]; receive -m (from_state), send m (to_state)
# The APC's own activity column, which powdr's last step puts on every
# interaction ("is_valid@<id>"; an instruction's is "is_valid_<i>@<id>").
APC_VALID = "is_valid"


def _mentions_apc_valid(e: Expr) -> bool:
    return any(v.split("@")[0] == APC_VALID for v in variables(e))


def _receive_mult(mult: Expr, p: int) -> Expr | None:
    """m if ``mult`` reads -m (a receive), else None."""
    if isinstance(mult, list) and len(mult) == 2 and mult[0] == "-":
        return mult[1]
    if _const_value(mult, p) == p - 1:
        return 1
    return None


def _same(a: Expr, b: Expr, p: int) -> bool:
    ca, cb = _const_value(a, p), _const_value(b, p)
    if ca is not None or cb is not None:
        return ca == cb
    return a == b


def chain_pairs(c: Circuit, p: int = BABYBEAR) -> tuple[list[tuple[dict, dict]], dict | None]:
    """(send_i, receive_{i+1}) pairs in dump order, and the entry receive.

    Empty pairs and the first receive (or None) if the interactions do not
    alternate receive / send with matching multiplicities.
    """
    ex = [bi for bi in c.bus_interactions if bi["id"] == EXECUTION_BRIDGE]
    if not ex:
        return [], None
    first = ex[0] if _receive_mult(ex[0]["mult"], p) is not None else None
    if len(ex) % 2:
        return [], first
    for k in range(0, len(ex), 2):
        recv, send = ex[k], ex[k + 1]
        m = _receive_mult(recv["mult"], p)
        if m is None or _receive_mult(send["mult"], p) is not None:
            return [], first
        if not _same(m, send["mult"], p):
            return [], first
        if len(recv["args"]) != len(send["args"]):
            return [], first
    pairs = [(ex[k + 1], ex[k + 2]) for k in range(0, len(ex) - 2, 2)]
    return pairs, first


def execution_facts(
    c: Circuit, entry_pc: int | None, p: int = BABYBEAR
) -> list[tuple[str, Expr]]:
    """(name, e) with e = 0 for every entry, runs and chain fact of ``c``.

    ``entry_pc`` None gives no entry fact. A multiplicity that is a constant
    gives no runs fact: 1 has nothing to say, and anything else would make
    the premises contradictory (and so imply everything). Nor does one that
    mentions the APC's own is_valid: "the instruction runs" holds when the
    APC row is active, and assuming the row is active would skip exactly
    what the last step must get right (inactive rows send nothing).
    """
    out: list[tuple[str, Expr]] = []
    pairs, first = chain_pairs(c, p)
    if first is not None and entry_pc is not None and first["args"]:
        out.append(("entry", [first["args"][0], "-", entry_pc]))
    j = 0
    for bi in c.bus_interactions:
        if bi["id"] == EXECUTION_BRIDGE:
            m = _receive_mult(bi["mult"], p)
            m = bi["mult"] if m is None else m
        elif bi["id"] == PC_LOOKUP:
            m = bi["mult"]
        else:
            continue
        if _const_value(m, p) is None and not _mentions_apc_valid(m):
            out.append((f"runs{j}", [m, "-", 1]))
        j += 1
    for i, (send, recv) in enumerate(pairs):
        for k, (a, b) in enumerate(zip(send["args"], recv["args"])):
            out.append((f"chain{i}.{k}", [a, "-", b]))
    # A constant fact says nothing (0) or contradicts (anything else); drop it
    # either way, so a wrong entry pc cannot make every obligation follow.
    return [(n, e) for n, e in out if _const_value(e, p) is None]
