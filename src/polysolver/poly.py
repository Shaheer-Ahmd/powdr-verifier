"""Polynomials over F_p and the zero key.

A polynomial is a dict ``{monomial: coeff}``. A monomial is a tuple of
``(Var, exponent)`` pairs sorted by Var; ``()`` is the constant monomial.
Coefficients live in ``[1, p)``; zero terms are dropped.

The zero key makes a polynomial monic, so two polynomials with the same key
differ by a nonzero constant factor and have the same zeros.

Division: an inverse atom is an ordinary Var I that stands for the inverse
of a polynomial d: ``inverse_of`` maps I to d. That is a definition, not a
claim: I * d = 1 holds only where d != 0, so nothing cancels on its own; add,
mul and substitute treat I like any variable. ``clear_denominators`` is told
explicitly which polynomials are nonzero, and clears only those atoms:
there it multiplies a by d, which keeps a's zeros. Each atom may occur with
power at most 1.
"""

from __future__ import annotations

from collections.abc import Callable, Collection

from .expr import OPS, Expr, UnsupportedExpr

Mono = tuple  # tuple[(Var, exp), ...], e.g. x*x*y is ((x, 2), (y, 1))
Poly = dict  # dict[Mono, int], e.g. 3*x + 1 is {((x, 1),): 3, (): 1}
Key = tuple  # tuple[(Mono, coeff), ...], a Poly in a fixed order, made monic

ZERO: Key = ()  # the key of the zero polynomial
# Full expansion can blow up (a product of n sums has up to |a|*|b|*... terms),
# so we give up past this many terms instead of hanging.
MAX_TERMS = 4096


class ExpansionLimit(Exception):
    """An intermediate polynomial grew past the term budget."""


def const(k: int, p: int) -> Poly:
    """The constant ``k``; reducing mod p turns p-1 and -1 into the same value."""
    k %= p
    return {(): k} if k else {}


def var_poly(v: int) -> Poly:
    """The polynomial ``v`` (one term, coefficient 1)."""
    return {((v, 1),): 1}


def add(a: Poly, b: Poly, p: int, sign: int = 1) -> Poly:
    """``a + sign * b``."""
    out = dict(a)
    for m, c in b.items():
        s = (out.get(m, 0) + sign * c) % p
        # Keep only nonzero terms, so x - x really is the empty polynomial.
        if s:
            out[m] = s
        else:
            out.pop(m, None)
    return out


def scale(a: Poly, k: int, p: int) -> Poly:
    """``k * a``; scaling by 0 gives the zero polynomial."""
    k %= p
    return {m: c * k % p for m, c in a.items()} if k else {}


def mul(a: Poly, b: Poly, p: int, limit: int = MAX_TERMS) -> Poly:
    """Fully distributed product: every term of ``a`` times every term of ``b``."""
    out: Poly = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = _mono_mul(ma, mb)
            # Terms that land on the same monomial are summed; they may cancel.
            s = (out.get(m, 0) + ca * cb) % p
            if s:
                out[m] = s
            else:
                out.pop(m, None)
        # Check once per row, so a runaway product stops early.
        if len(out) > limit:
            raise ExpansionLimit
    return out


def _mono_mul(a: Mono, b: Mono) -> Mono:
    """Multiply two monomials by adding exponents: (x^2 y) * (x z) = x^3 y z."""
    if not a:  # the constant monomial is the identity
        return b
    if not b:
        return a
    exps = dict(a)
    for v, e in b:
        exps[v] = exps.get(v, 0) + e
    # Sorting by Var gives each monomial exactly one spelling: x*y == y*x.
    return tuple(sorted(exps.items()))


def expand(
    e: Expr, lookup: Callable[[str], Poly], p: int, limit: int = MAX_TERMS
) -> Poly:
    """Expand an expression into one fully distributed polynomial.

    Walks the JSON tree bottom-up: leaves become polynomials, operators combine
    them. ``lookup`` decides what a name means: usually just that variable,
    but a defined variable expands to its definition, which is how
    definitions are substituted without rewriting the expression.
    """
    if isinstance(e, bool):  # bool is an int in Python; never valid here
        raise UnsupportedExpr(f"not an expression: {e!r}")
    if isinstance(e, int):
        return const(e, p)
    if isinstance(e, str):
        return lookup(e)
    if isinstance(e, list):
        if len(e) == 2 and e[0] == "-":
            return scale(expand(e[1], lookup, p, limit), -1, p)
        if len(e) == 3 and e[1] in OPS:
            a = expand(e[0], lookup, p, limit)
            b = expand(e[2], lookup, p, limit)
            if e[1] == "*":
                return mul(a, b, p, limit)
            # "+" and "-" share one code path; "-" just flips the sign of b.
            out = add(a, b, p, 1 if e[1] == "+" else -1)
            if len(out) > limit:
                raise ExpansionLimit
            return out
    raise UnsupportedExpr(f"not an expression: {e!r}")


def substitute(
    a: Poly, sub: Callable[[int], Poly | None], p: int, limit: int = MAX_TERMS
) -> Poly:
    """``a`` with each variable v replaced by ``sub(v)`` (kept as is if None)."""
    out: Poly = {}
    for m, c in a.items():
        term: Poly = {(): c}
        for v, e in m:
            f = sub(v)
            if f is None:
                term = mul(term, {((v, e),): 1}, p, limit)
                continue
            for _ in range(e):
                term = mul(term, f, p, limit)
        out = add(out, term, p)
        if len(out) > limit:
            raise ExpansionLimit
    return out


def split_linear(a: Poly, v: int) -> tuple[Poly, Poly] | None:
    """``(a1, a0)`` with ``a = a1 * v + a0`` and v in neither; None if v occurs squared."""
    a1: Poly = {}
    a0: Poly = {}
    for m, c in a.items():
        e = next((e for x, e in m if x == v), 0)
        if e == 0:
            a0[m] = c
        elif e == 1:
            a1[tuple(xe for xe in m if xe[0] != v)] = c
        else:
            return None
    return a1, a0


def variables_of(a: Poly) -> set[int]:
    """The variables that occur in a polynomial."""
    return {v for m in a for v, _ in m}


def degree(m: Mono) -> int:
    """Total degree: x^2 y has degree 3, a constant has degree 0."""
    return sum(e for _, e in m)


def _order(m: Mono) -> tuple:
    # Highest degree first, then by monomial; the first term is the leading one.
    return (-degree(m), m)


def lead_coeff(a: Poly) -> int:
    """The coefficient of the leading term (the one zkey makes 1); a is nonzero."""
    return a[min(a, key=_order)]


def clear_denominators(
    a: Poly,
    inverse_of: dict[int, Poly],
    nonzero: Collection[Key],
    p: int,
    limit: int = MAX_TERMS,
) -> tuple[Poly, set[Key]] | None:
    """``a`` times d for each atom I = inverse_of d in it whose d is in ``nonzero``.

    ``nonzero`` holds the zero keys of the polynomials known to be nonzero;
    an atom whose d is not among them is left as it is, so with no nonzero
    facts nothing changes. For a cleared atom, writing a = a1 * I + a0,
    d * a is a1 + a0 * d (I * d = 1 as d != 0), and has the same zeros as a.
    The polynomials never mention atoms, so the atoms are cleared one at a
    time. Returns the result and the keys of the nonzero facts it used; None
    if an atom to clear occurs squared.
    """
    used: set[Key] = set()
    for i in sorted(variables_of(a) & inverse_of.keys()):
        d = inverse_of[i]
        k = zkey(d, p)
        if k == ZERO or k not in nonzero:
            continue  # not known nonzero: I * d = 1 may fail, keep I
        split = split_linear(a, i)
        if split is None:
            return None
        a1, a0 = split
        a = add(a1, mul(a0, d, p, limit), p)
        if len(a) > limit:
            raise ExpansionLimit
        used.add(k)
    return a, used


def zkey(a: Poly, p: int) -> Key:
    """Monic key of ``a = 0``: divide by the leading coefficient.

    ``c = 0``, ``-c = 0`` and ``3c = 0`` have the same zeros, so they should
    get the same key. Dividing every coefficient by the leading one makes
    the leading coefficient 1 and erases that difference.
    """
    if not a:
        return ZERO
    monos = sorted(a, key=_order)  # a fixed order, so equal polys give equal keys
    inv = pow(a[monos[0]], p - 2, p)  # inverse by Fermat: c^(p-2) = 1/c mod p
    return tuple((m, a[m] * inv % p) for m in monos)


def key_vars(k: Key) -> set[int]:
    """The variables that occur in a key."""
    return {v for m, _ in k for v, _ in m}


def is_constant(k: Key) -> bool:
    """True if the key has no variables (only the constant term, or nothing)."""
    return all(m == () for m, _ in k)
