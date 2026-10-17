"""Search for witnesses for undefined variables.

Clients of ``PolySolver.implies``, not part of it. Any witness they return is
correct, because each candidate is checked with ``implies``; the search only
decides what to try.

- find_witness: one term per missing column inv_i (f or f * x_i), read off a
  premise f * (x_1' + ... + x_n') + c. Used first.
- find_uniform_witness: one shared term for all of them, tried column by column
  from a shortlist. The fallback, e.g. for a renamed column.
"""

from __future__ import annotations

from collections.abc import Iterable

from . import poly as P
from .defs import InvalidDefs, Opaque
from .expr import Expr, product_factors, sum_terms, variables
from .solver import Implied, PolySolver


def find_witness(
    solver: PolySolver,
    base_w: dict[str, Expr | Opaque],
    unknowns: Iterable[str],
    cand_constraints: Iterable[Expr],
    shortlist: Iterable[str],
) -> dict[str, Expr] | None:
    """A term for each missing column inv_i, read off a premise, or None.

    The candidate (Before) constraint looks like
        x_1*inv_1 + ... + x_n*inv_n + c
    and a premise (After) for some f in ``shortlist`` looks like
        f * (x_1' + ... + x_n') + c
    where each x_i' is x_i (powdr did not square it) or x_i*x_i (it did).
    We set inv_i := f in the first case and inv_i := f * x_i in the second.
    Plugging these in turns the candidate into exactly the premise.

    Example (2103472):  Before  (a_0 - b_0)*inv_0 + ... - cmp
                        After   f * ((a_0 - b_0)^2 + ...) - cmp
                        so      inv_0 := f * (a_0 - b_0), ...
    """
    unknowns = set(unknowns)
    # Every candidate constraint that mentions an inv_i has to hold in the end.
    targets = [c for c in cand_constraints if variables(c) & unknowns]
    # The witness is read off the one that mentions all of them.
    target = next((t for t in targets if unknowns <= variables(t)), None)
    if target is None:
        return None
    # Columns mapped earlier (e.g. by substitution) are written into the target.
    try:
        base = solver.make_defs(base_w)
    except InvalidDefs:
        return None
    split = _linear_in(solver, target, base, unknowns)
    if split is None:
        return None
    x_of, c = split  # x_of[inv_i] = x_i
    for f in shortlist:
        for prem in solver.premises_mentioning(f):
            w = _read_off(solver, prem, f, x_of, c)
            if w is None:
                continue  # this premise does not have the f * (...) + c shape
            try:
                defs = solver.make_defs({**base_w, **w})
            except InvalidDefs:
                continue
            # The shape match is only a guess; implies has the final say.
            if all(isinstance(solver.implies(t, defs), Implied) for t in targets):
                return w
    return None


def _linear_in(solver, t, defs, unknowns) -> tuple[dict, dict] | None:
    """Split t = x_1*inv_1 + ... + x_n*inv_n + c into ({inv_i: x_i}, c).

    None if t is not linear in the inv_i (e.g. inv_1*inv_2, or inv_1^2).
    """
    # Expand t; the inv_i have no value, so they stay as plain variables.
    nf = solver.normal_form(t, defs, free=unknowns)
    if nf is None:
        return None
    ids = {solver.table.var(u): u for u in unknowns}
    x_of: dict[str, P.Poly] = {u: {} for u in unknowns}
    c: P.Poly = {}
    # Sort each term (monomial m with coefficient k) by the inv_i it contains.
    for m, k in nf:
        inv = [(v, e) for v, e in m if v in ids]
        if not inv:
            c[m] = k  # no inv_i: part of c
        elif len(inv) == 1 and inv[0][1] == 1:
            # exactly one inv_i, to the power 1: the rest of the term goes to x_i
            rest = tuple(ve for ve in m if ve[0] not in ids)
            x_of[ids[inv[0][0]]][rest] = k
        else:
            return None  # inv_i * inv_j or inv_i^2
    if not all(x_of.values()):
        return None  # some inv_i cancelled out, so it has no x_i
    return x_of, c


def _read_off(solver, prem, f, x_of, c) -> dict[str, Expr] | None:
    """inv_i := f or f * x_i, if prem is written as  f * (x_1' + ... + x_n') + c.

    Constant factors are allowed anywhere (e.g. cmp - f * (...), or powdr's
    coefficients 2*x_1*inv_1 vs f * (2*x_1^2 + ...)); they end up in the witness.
    """
    p = solver.p

    # 1. Find the  f * (x_1' + ... + x_n')  part of prem. Exactly one summand
    #    of prem may mention f, and it must be  f * sum  (times constants).
    with_f = [(s, e) for s, e in sum_terms(prem) if f in variables(e)]
    if len(with_f) != 1:
        return None
    sign, term = with_f[0]
    factors = product_factors(term)
    others = [x for x in factors if x != f and not isinstance(x, int)]
    if factors.count(f) != 1 or len(others) != 1 or f in variables(others[0]):
        return None
    sum_expr = others[0]  # x_1' + ... + x_n'
    # The constant in front of f * sum: the summand's sign times any number factors.
    f_coeff = sign
    for x in factors:
        if isinstance(x, int):
            f_coeff = f_coeff * x % p

    # 2. The rest of prem (prem minus f_coeff * f * sum) must be c, up to a constant.
    prem_nf, f_sum_nf = solver.normal_form(prem), solver.normal_form([f, "*", sum_expr])
    if prem_nf is None or f_sum_nf is None:
        return None
    prem_rest = P.add(dict(prem_nf), P.scale(dict(f_sum_nf), f_coeff, p), p, -1)
    # After plugging in, the candidate is  f_scale * f * sum + c. We want it to be
    # a constant multiple of prem = f_coeff * f * sum + prem_rest, so that rule N
    # proves it: c = scale * prem_rest, and then f_scale = scale * f_coeff.
    # Usually everything is 1; it is -1 when prem is written  cmp - f * (...).
    if not c and not prem_rest:
        f_scale = 1
    else:
        scale = _ratio(c, prem_rest, p)
        if scale is None:
            return None  # the rest of prem is not c: wrong premise
        f_scale = scale * f_coeff % p

    # 3. Expand each summand x' of the sum (with its sign) so they can be compared.
    unused = []
    for s, t in sum_terms(sum_expr):
        nf = solver.normal_form(t)
        if nf is None:
            return None
        unused.append(P.scale(dict(nf), s, p))

    # 4. Give each inv_i the summand that belongs to it, and use each summand once.
    #    Comparing expanded forms means (b - a)^2 matches x_i = a - b too.
    w = {}
    for inv in sorted(x_of):
        x = x_of[inv]
        for j, xp in enumerate(unused):
            k = _ratio(xp, x, p)
            if k is not None:  # x' = k * x_i: not squared, so inv_i := f
                w[inv] = _term(f_scale * k % p, f, None, solver.table)
                break
            k = _ratio(xp, P.mul(x, x, p), p)
            if k is not None:  # x' = k * x_i^2: squared, so inv_i := f * x_i
                w[inv] = _term(f_scale * k % p, f, x, solver.table)
                break
        else:
            return None  # no summand belongs to this inv_i
        unused.pop(j)
    return w


def _ratio(a: P.Poly, b: P.Poly, p: int) -> int | None:
    """The constant k with a = k * b, or None if there is none (or either is 0)."""
    # Same zero key means the same polynomial up to a constant factor.
    if not a or not b or P.zkey(a, p) != P.zkey(b, p):
        return None
    m = next(iter(b))
    return a[m] * pow(b[m], p - 2, p) % p  # a[m] / b[m] in F_p


def _term(k: int, f: str, x: P.Poly | None, table) -> Expr:
    """The witness k * f, or k * f * x_i, as an expression (k = 1 is left out)."""
    e = f if k == 1 else [k, "*", f]
    return e if x is None else [e, "*", _expr(x, table)]


def _expr(a: P.Poly, table) -> Expr:
    """A polynomial written back as an expression, e.g. {a: 1, b: -1} -> a + (-1)*b."""
    # Order by column name, constant last. Var ids depend on the order names were
    # first seen, which varies between runs (set order), so they would not do.
    named = [(sorted(table.name(v) for v, e in m for _ in range(e)), k) for m, k in a.items()]
    terms = []
    for names, k in sorted(named, key=lambda nk: (not nk[0], nk[0])):
        if not names:
            terms.append(k)  # the constant term
            continue
        t = _chain(names, "*")  # x^2 -> x * x
        terms.append(t if k == 1 else [k, "*", t])
    return _chain(terms, "+") if terms else 0


def _chain(es: list[Expr], op: str) -> Expr:
    """[e1, e2, e3] -> ((e1 op e2) op e3)."""
    out = es[0]
    for e in es[1:]:
        out = [out, op, e]
    return out


def find_uniform_witness(
    solver: PolySolver,
    base_w: dict[str, Expr | Opaque],
    unknowns: Iterable[str],
    cand_constraints: Iterable[Expr],
    shortlist: Iterable[Expr],
) -> Expr | None:
    """The first ``r`` in ``shortlist`` such that setting every unknown to ``r``
    makes all constraints that mention an unknown implied, or None."""
    unknowns = set(unknowns)
    targets = [c for c in cand_constraints if variables(c) & unknowns]
    for r in shortlist:
        try:
            defs = solver.make_defs({**base_w, **{u: r for u in unknowns}})
        except InvalidDefs:
            continue  # r is not usable as a definition (e.g. not declared)
        if all(isinstance(solver.implies(c, defs), Implied) for c in targets):
            return r
    return None
