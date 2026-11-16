"""Lookup semantics: what a powdr lookup means, as polynomials and ranges.

A stateless lookup asserts "mult != 0 => args is a row of the table". This
module is the one place that says what a row is, for every table the sweep
knows (PcLookup's table is the program, which the caller passes when it
trusts it). Everything else reads the tables through it:

- ``is_row``: the ground truth, for constant arguments. It is the oracle the
  case lists are tested against, and the sweep's "evaluated" rungs.
- ``cases``: a lookup's meaning as Cases of PolySolver goals (Zero for an
  identity, Bounded for a bound). Under its ``when`` goals, a Case says
  row <=> every ``row`` goal holds  (``exact``), or only row => them (a
  consequence).
- ``assume`` (premise side): the reference's lookups into P and R. For each
  Case whose ``when`` the solver entails, its Zero goals become premises
  (gated by mult unless mult is a known nonzero constant), its Bounded goals
  ranges (only for a bare variable and a known nonzero mult: a range cannot
  be gated). Sound by the => direction.
- ``prove`` (goal side): a candidate lookup holds if the solver entails
  some exact Case's ``when`` and ``row`` goals. Sound by the <= direction.

This module only translates; PolySolver.entails does every proving step,
the same call on both sides, so they recognise the same cases. ``cases``
only proposes: it reads constants to pick cases, and every case states the
conditions it was picked by.

The semantics follow the SMT encoders in src/bus_interactions/.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from src.polysolver import NO_DEFS, Bounded, Defs, Expr, Goal, Implied, PolySolver, Zero

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
BYTE = 255

Program = dict[int, tuple[int, ...]]


# ------------------------------------------------------------ ground truth


def is_row(bus: int, args: list[int], program: Program | None = None) -> bool | None:
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
            return x <= BYTE and y <= BYTE and z == 0
        if op == 1:
            return x <= BYTE and y <= BYTE and z == x ^ y
        return False
    return None


# ------------------------------------------------------------ cases


@dataclass(frozen=True)
class Case:
    """If every goal in ``when`` holds, then
    args is a row  <=>  every goal in ``row`` holds  (``exact``),
    or only  =>  (a consequence, for premises only).

    In ``row``, a Zero goal is an identity and a Bounded goal a bound.
    """

    name: str  # short, used in premise tags: "xor-y0", "range8", "pc100"
    when: tuple[Goal, ...] = ()  # the conditions that select the case
    row: tuple[Goal, ...] = ()  # what a row means under them
    exact: bool = True


def cases(
    bi: dict, value: Callable[[Expr], int | None], program: Program | None = None
) -> list[Case]:
    """The Cases of lookup ``bi``. ``value(e)`` is e's constant value if known.

    ``value`` only picks which cases to propose (op, bits, pc, constant xor
    operands); each case states its picking conditions in ``when``, which the
    caller checks. A PcLookup has cases only with a ``program``.
    """
    bus, args = bi["id"], bi["args"]
    if bus == VARIABLE_RANGE_CHECKER and len(args) == 2:
        return _range_cases(*args, value)
    if bus == TUPLE_RANGE_CHECKER and len(args) == 2:
        x, y = args
        row = (Bounded(x, TUPLE_SIZES[0] - 1), Bounded(y, TUPLE_SIZES[1] - 1))
        return [Case("tuple", row=row)]
    if bus == BITWISE_LOOKUP and len(args) == 4:
        return _bitwise_cases(*args, value)
    if bus == PC_LOOKUP and program and args:
        pc = value(args[0])
        row = program.get(pc) if pc is not None else None
        if row is None or len(row) != len(args) - 1:
            return []
        ids = tuple(Zero([a, "-", r]) for a, r in zip(args[1:], row))
        return [Case(f"pc{pc}", when=(Zero([args[0], "-", pc]),), row=ids)]
    return []


def _range_cases(x: Expr, b: Expr, value) -> list[Case]:
    bits = value(b)
    if bits is None or bits > MAX_BITS:
        return []
    when = (Zero([b, "-", bits]),)
    out = [Case(f"range{bits}", when, (Bounded(x, 2**bits - 1),))]
    # A composite x has no interval, but a narrow check is a polynomial.
    if bits == 0:
        out.append(Case("range0-poly", when, (Zero(x),)))
    elif bits == 1:
        out.append(Case("range1-poly", when, (Zero([x, "*", [x, "-", 1]]),)))
    return out


def _bitwise_cases(x: Expr, y: Expr, z: Expr, o: Expr, value) -> list[Case]:
    op = value(o)
    if op not in (0, 1):
        return []
    sel = (Zero([o, "-", op]),)
    xy = (Bounded(x, BYTE), Bounded(y, BYTE))
    if op == 0:
        return [Case("and0", sel, xy + (Zero(z),))]
    out = []

    def case(name, when, identity):
        out.append(Case(name, sel + tuple(when), xy + (Zero(identity),)))

    cx, cy = value(x), value(y)
    if cx is not None and cy is not None:
        case("xor-const", (Zero([x, "-", cx]), Zero([y, "-", cy])), [z, "-", cx ^ cy])
    for a, ca, other, tag in ((y, cy, x, "y"), (x, cx, y, "x")):
        if ca == 0:  # a = 0: z = the other
            case(f"xor-{tag}0", (Zero(a),), [z, "-", other])
        elif ca == BYTE:  # a = 255: z = 255 - the other, exact on bytes
            case(f"xor-{tag}255", (Zero([a, "-", BYTE]),), [[z, "+", other], "-", BYTE])
    if value(z) == 0:
        case("xor-z0", (Zero(z),), [x, "-", y])  # x xor y = 0 iff x = y
    case("xor-same", (Zero([x, "-", y]),), z)
    case("xor-bits", (Bounded(x, 1), Bounded(y, 1)),
         [z, "-", [[x, "+", y], "-", [2, "*", [x, "*", y]]]])
    # Every xor row has z < 256; not exact (bytes x, y, z are not a row).
    out.append(Case("xor-bytes", sel, xy + (Bounded(z, BYTE),), exact=False))
    return out


def bound(bi: dict, k: int) -> int | None:
    """The exclusive upper bound the table puts on argument ``k``, read from its exact cases.

    Used only to order candidate values (tightest check first), never to decide.
    """
    arg = bi["args"][k] if k < len(bi["args"]) else None
    his = [
        g.hi
        for c in cases(bi, _written_value)
        if c.exact
        for g in c.row
        if isinstance(g, Bounded) and g.e == arg
    ]
    return max(his) + 1 if his else None


def _written_value(e: Expr) -> int | None:
    """A constant as written (no solver): for ``bound``, which only orders."""
    return e if isinstance(e, int) and not isinstance(e, bool) and e >= 0 else None


def _value(s: PolySolver, defs: Defs = NO_DEFS) -> Callable[[Expr], int | None]:
    """``e``'s constant value under the solver, if it has one: for proposing cases."""

    def value(e: Expr) -> int | None:
        nf = s.normal_form(e, defs)
        return None if nf is None else constant(nf)

    return value


# ------------------------------------------------------------ goal side


@dataclass(frozen=True)
class Proved:
    case: str
    verdict: Implied  # the conjunction of the case's conditions and row


def prove(
    s: PolySolver, bi: dict, defs: Defs = NO_DEFS, program: Program | None = None
) -> Proved | None:
    """The candidate lookup ``bi`` holds for every witness: some exact Case is entailed.

    Its conditions and row goals all implied give  args is a row, whatever
    mult is. None if no case is.
    """
    for c in cases(bi, _value(s, defs), program):
        if not c.exact:
            continue
        v = s.entails(c.when + c.row, defs)
        if isinstance(v, Implied):
            return Proved(c.name, v)
    return None


# ------------------------------------------------------------ premise side


def assume(
    s: PolySolver,
    label: str,
    lookups: list[dict],
    *,
    ranges: bool = True,
    facts: bool = True,
    program: Program | None = None,
) -> None:
    """Add what the reference's ``lookups`` give to ``s``: premises and ranges.

    For each case whose conditions ``s`` entails (each case once), its row
    goals become facts: with ``facts``, a Zero goal e as the premise e, or
    mult * e unless mult is a known nonzero constant; with ``ranges``, a
    Bounded goal as a range, only when mult is a known nonzero constant and
    the bounded expression is a bare variable. PcLookup cases need
    ``program`` (the trusted table; its identities are added whatever
    ``facts`` is). A lookup with mult = 0 implied gives nothing. An identity
    that is a constant says nothing usable (0) or would be a contradiction;
    it is skipped.

    A fact can make another lookup's pc, op or operands known, so this
    repeats, with propagation, until a round adds nothing.
    """
    value = _value(s)
    done: set[tuple[int, str]] = set()
    while True:
        added = False
        for j, bi in enumerate(lookups):
            if bi["id"] == PC_LOOKUP and program is None:
                continue
            mult = bi["mult"]
            if isinstance(s.implies(mult), Implied):
                continue
            known = value(mult) is not None  # and nonzero, as mult = 0 is not implied
            identities = facts or bi["id"] == PC_LOOKUP
            for c in cases(bi, value, program):
                if (j, c.name) in done or not isinstance(s.entails(c.when), Implied):
                    continue
                done.add((j, c.name))
                ids = [g.e for g in c.row if isinstance(g, Zero)]
                for k, e in enumerate(ids if identities else ()):
                    if value(e) is not None:
                        continue
                    s.add_premise(e if known else [mult, "*", e],
                                  tag=f"{label}:b{j}:{c.name}:{k}")
                    added = True
                for g in c.row if ranges and known else ():
                    x = _bare_variable(s, g.e) if isinstance(g, Bounded) else None
                    if x is not None:
                        s.add_range(x, 0, g.hi, tag=f"{label}:lookup:{x}")
                        added = True
        if not added:
            return
        s.propagate()


def _bare_variable(s: PolySolver, e: Expr) -> str | None:
    """The declared variable ``e`` is (under the solved equations), if it is one."""
    if isinstance(e, str):
        return e
    nf = s.normal_form(e)
    if nf is None or len(nf) != 1:
        return None
    ((mono, coeff),) = nf
    if coeff != 1 or len(mono) != 1 or mono[0][1] != 1:
        return None
    return s.table.name(mono[0][0])


# ------------------------------------------------------------ index helpers


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


__all__ = [
    "BITWISE_LOOKUP",
    "MAX_BITS",
    "PC_LOOKUP",
    "TUPLE_RANGE_CHECKER",
    "TUPLE_SIZES",
    "VARIABLE_RANGE_CHECKER",
    "Case",
    "Proved",
    "assume",
    "bound",
    "cases",
    "constant",
    "is_row",
    "lookup_holds",
    "normal_key",
    "prove",
]
