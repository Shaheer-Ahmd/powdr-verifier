"""Ground evaluation of lookup tables: is a tuple of constants a row?

This is the only place the sweep uses what a lookup table contains. It is
used for lookups whose arguments are all constants (after the mapping and the
solved equations), so a row check decides them outright. The semantics follow
the SMT encoders in src/bus_interactions/.

PcLookup (bus 2) has no fixed table: its table is the program. It is
evaluated only against a ``program`` the caller passes (the block's own
instructions from the unopt dump, circuit.load_program), which is a trust
decision the sweep reports under its own rung. Unknown buses are not evaluated.
"""

from __future__ import annotations

from src.polysolver import Defs, PolySolver

PC_LOOKUP = 2  # [pc, opcode, a, ..., g]: the program's instruction at pc
VARIABLE_RANGE_CHECKER = 3  # [x, bits]: x < 2^bits
BITWISE_LOOKUP = 6  # [x, y, z, op]: op 0 range-checks x, y; op 1 has z = x xor y
TUPLE_RANGE_CHECKER = 7  # [x, y]: x < TUPLE_SIZES[0], y < TUPLE_SIZES[1]
# The rv32im default sizes (openvm default_range_tuple_checker_sizes), as in
# openvm_tuple_range_checker.py. Other extensions (bigint) configure others.
TUPLE_SIZES = (1 << 8, 8 * (1 << 8))
# Widest width the range checker is instantiated for
# (openvm_variable_range_checker.py MAX_BITS); wider is not decided here.
MAX_BITS = 25


def is_row(
    bus: int, args: list[int], program: dict[int, tuple[int, ...]] | None = None
) -> bool | None:
    """True or False if ``args`` (integers in [0, p)) is or is not a row; None if not decided.

    ``program`` maps a pc to its instruction. A PcLookup is decided only for
    the pcs it covers: the rest of the program is not known here.
    """
    if bus == PC_LOOKUP:
        if not program or not args or args[0] not in program:
            return None
        return tuple(args[1:]) == program[args[0]]
    if bus == VARIABLE_RANGE_CHECKER and len(args) == 2:
        x, bits = args
        if bits > MAX_BITS:
            return None
        return x < 2**bits
    if bus == TUPLE_RANGE_CHECKER and len(args) == 2:
        return args[0] < TUPLE_SIZES[0] and args[1] < TUPLE_SIZES[1]
    if bus == BITWISE_LOOKUP and len(args) == 4:
        x, y, z, op = args
        if op == 0:
            return x < 256 and y < 256 and z == 0
        if op == 1:
            return x < 256 and y < 256 and z == x ^ y
        return False
    return None


def _is_const(e, value: int | None = None, p: int = 2013265921) -> bool:
    if isinstance(e, bool) or not isinstance(e, int):
        return False
    return value is None or e % p == value


def lookup_facts(bi: dict, p: int = 2013265921, is_bit=None) -> list:
    """Polynomial facts that a reference lookup gives, as expressions e (e = 0).

    The lookup asserts "mult != 0 => args is a row". For an identity id that
    every row satisfies, mult * id = 0 follows (and id = 0 if mult is a
    nonzero constant). The identities read the tuple as written (M4i):

      bitwise [x, y, z, 1] (z = x xor y, x and y bytes):
        y = 0: z = x;  x = 0: z = y;  y = 255: z = 255 - x;  x = 255: z = 255 - y;
        z = 0: x = y;  x and y the same expression: z = 0
        x and y bits (is_bit, the caller's ranges): z = x + y - 2xy
      bitwise [x, y, z, 0]: z = 0
      range checker [x, 0]: x = 0;  [x, 1]: x * (x - 1) = 0
    """
    mult, args = bi["mult"], bi["args"]
    if _is_const(mult, 0, p):
        return []
    ids = []
    if bi["id"] == BITWISE_LOOKUP and len(args) == 4:
        x, y, z, op = args
        if _is_const(op, 1, p):
            if _is_const(y, 0, p):
                ids.append([z, "-", x])
            elif _is_const(x, 0, p):
                ids.append([z, "-", y])
            elif _is_const(y, 255, p):
                ids.append([[z, "+", x], "-", 255])
            elif _is_const(x, 255, p):
                ids.append([[z, "+", y], "-", 255])
            elif is_bit is not None and is_bit(x) and is_bit(y):
                ids.append([z, "-", [[x, "+", y], "-", [2, "*", [x, "*", y]]]])
            if _is_const(z, 0, p):
                ids.append([x, "-", y])
            elif x == y:
                ids.append(z)
        elif _is_const(op, 0, p) and not _is_const(z, 0, p):
            ids.append(z)
    elif bi["id"] == VARIABLE_RANGE_CHECKER and len(args) == 2:
        x, bits = args
        if _is_const(bits, 0, p):
            ids.append(x)
        elif _is_const(bits, 1, p):
            ids.append([x, "*", [x, "-", 1]])
    ids = [e for e in ids if not isinstance(e, int)]  # constants: nothing to learn
    if isinstance(mult, int) and not isinstance(mult, bool):
        return ids
    return [[mult, "*", e] for e in ids]


def bound(bi: dict, k: int) -> int | None:
    """The exclusive upper bound the table puts on argument ``k`` of ``bi``, if it has one.

    Used only to order candidate values (tightest check first), never to decide.
    """
    args = bi["args"]
    if bi["id"] == VARIABLE_RANGE_CHECKER and len(args) == 2:
        bits = args[1]
        if k == 0 and isinstance(bits, int) and not isinstance(bits, bool) and 0 <= bits <= MAX_BITS:
            return 2**bits
    if bi["id"] == TUPLE_RANGE_CHECKER and len(args) == 2 and k in (0, 1):
        return TUPLE_SIZES[k]
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
