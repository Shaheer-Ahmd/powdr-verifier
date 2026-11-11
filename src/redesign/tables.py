"""Ground evaluation of lookup tables: is a tuple of constants a row?

This is the only place the sweep uses what a lookup table contains. It is
used for lookups whose arguments are all constants (after the mapping and the
solved equations), so a row check decides them outright. The semantics follow
the SMT encoders in src/bus_interactions/.

PcLookup (bus 2) is deliberately not evaluated: its table is the program, and
the redesign does not trust it (yet). Unknown buses are not evaluated either.
"""

from __future__ import annotations

from src.polysolver import Defs, PolySolver

VARIABLE_RANGE_CHECKER = 3  # [x, bits]: x < 2^bits
BITWISE_LOOKUP = 6  # [x, y, z, op]: op 0 range-checks x, y; op 1 has z = x xor y
# Widest width the range checker is instantiated for
# (openvm_variable_range_checker.py MAX_BITS); wider is not decided here.
MAX_BITS = 25


def is_row(bus: int, args: list[int]) -> bool | None:
    """True or False if ``args`` (integers in [0, p)) is or is not a row; None if not decided."""
    if bus == VARIABLE_RANGE_CHECKER and len(args) == 2:
        x, bits = args
        if bits > MAX_BITS:
            return None
        return x < 2**bits
    if bus == BITWISE_LOOKUP and len(args) == 4:
        x, y, z, op = args
        if op == 0:
            return x < 256 and y < 256 and z == 0
        if op == 1:
            return x < 256 and y < 256 and z == x ^ y
        return False
    return None


def bound(bi: dict, k: int) -> int | None:
    """The exclusive upper bound the table puts on argument ``k`` of ``bi``, if it has one.

    Used only to order candidate values (tightest check first), never to decide.
    """
    args = bi["args"]
    if bi["id"] == VARIABLE_RANGE_CHECKER and len(args) == 2:
        bits = args[1]
        if k == 0 and isinstance(bits, int) and not isinstance(bits, bool) and 0 <= bits <= MAX_BITS:
            return 2**bits
    if bi["id"] == BITWISE_LOOKUP and len(args) == 4 and k in (0, 1):
        return 256
    return None


def normal_key(solver: PolySolver, bi: dict, defs: Defs | None = None) -> tuple | None:
    """(bus, mult, args) in PolySolver's normal form, for the untrusted index."""
    nf = [
        solver.normal_form(e, defs) if defs is not None else solver.normal_form(e)
        for e in [bi["mult"], *bi["args"]]
    ]
    if any(x is None for x in nf):
        return None
    return (bi["id"], nf[0], tuple(nf[1:]))


def constant(nf: tuple) -> int | None:
    """The value of a normal form with no variables, else None."""
    if not nf:
        return 0
    if len(nf) == 1 and nf[0][0] == ():
        return nf[0][1]
    return None


def lookup_holds(solver: PolySolver, bi: dict, defs: Defs | None = None) -> bool:
    """The lookup ``bi`` holds outright under ``defs``: mult 0, or constant args that are a row."""
    key = normal_key(solver, bi, defs)
    if key is None:
        return False
    bus, mult, args = key
    if constant(mult) == 0:
        return True
    values = [constant(a) for a in args]
    return all(v is not None for v in values) and is_row(bus, values) is True
