"""Which variables take one value in every solution of a small polynomial system.

Stdlib only, and standalone: polynomials and finite domains, nothing else.

fixed_values(polys, domains, p, max_nodes). Let S be the assignments a in
the product of the domains with q(a) = 0 mod p for every q in polys.

- Sound: Fixed(values) and GaveUp(values) map x to v only if a(x) = v for
  every a in S. NoSolution only if S is empty.
- Complete, relative to its input: Fixed(values) maps every x that takes one
  value across all of S. GaveUp means the search tried more than max_nodes
  values; what it proved before that is kept.

Every variable of polys must have a domain, a tuple of field values. A
variable with a domain but in no polynomial is free.

The search: depth first, the variables in the most polynomials first (ties in
the caller's order), so polynomials are complete, and checked, early. It stops
at the second solution. Where two solutions disagree on x, x is not fixed. For
each x they agree on, another search looks for a solution with another value
of x; if there is none, x is fixed. A solution found that way joins the
comparison for the variables after x.
"""

from __future__ import annotations

from collections.abc import Hashable, Iterable, Mapping, Sequence
from dataclasses import dataclass


@dataclass(frozen=True)
class Fixed:
    """Every variable with one value across all solutions, and that value."""

    values: dict[Hashable, int]
    nodes: int  # values tried


@dataclass(frozen=True)
class GaveUp:
    """The budget ran out: values proved fixed before then, perhaps not all."""

    values: dict[Hashable, int]
    nodes: int


@dataclass(frozen=True)
class NoSolution:
    """No assignment over the domains is a zero of every polynomial."""

    nodes: int


Result = Fixed | GaveUp | NoSolution


class _OverBudget(Exception):
    """The search tried more than max_nodes values."""


def fixed_values(
    polys: Iterable[Iterable[tuple[tuple, int]]],
    domains: Mapping[Hashable, Sequence[int]],
    p: int,
    max_nodes: int,
) -> Result:
    """The variables every solution agrees on; see the module docstring.

    A polynomial is (monomial, coeff) pairs, a monomial ((var, exp), ...)
    with any hashable variables; the constant monomial is ().
    """
    polys = [tuple(q) for q in polys]
    qvars = [{x for m, _ in q for x, _ in m} for q in polys]
    for vs in qvars:
        if not vs <= domains.keys():
            raise ValueError(f"no domain for {vs - domains.keys()}")
    # A polynomial without variables holds everywhere if it is 0, else nowhere.
    if any(not vs and sum(c for _, c in q) % p for q, vs in zip(polys, qvars)):
        return NoSolution(0)

    order = sorted(domains, key=lambda x: -sum(x in vs for vs in qvars))
    pos = {x: n for n, x in enumerate(order)}
    # Each polynomial is checked once its last variable has a value, the
    # shortest first, as (coeff, ((position, exp), ...)) terms.
    checks: list[list] = [[] for _ in order]
    for q, vs in sorted(zip(polys, qvars), key=lambda qv: len(qv[0])):
        if vs:
            terms = [(c, tuple((pos[x], e) for x, e in m)) for m, c in q]
            checks[max(pos[x] for x in vs)].append(terms)

    n = len(order)
    vals = [0] * n
    nodes = 0

    def fits(terms) -> bool:
        total = 0
        for c, mono in terms:
            for at, e in mono:
                c = c * pow(vals[at], e, p) % p
            total += c
        return total % p == 0

    def search(choices: list, want: int) -> list[tuple[int, ...]]:
        """Up to ``want`` assignments from ``choices`` that fit, without recursion."""
        nonlocal nodes
        found: list[tuple[int, ...]] = []
        nxt = [0] * n  # per level, the next choice to try
        level = 0
        while level >= 0 and len(found) < want:
            if level == n:
                found.append(tuple(vals))
                level -= 1
            elif nxt[level] == len(choices[level]):
                nxt[level] = 0
                level -= 1
            else:
                vals[level] = choices[level][nxt[level]]
                nxt[level] += 1
                nodes += 1
                if nodes > max_nodes:
                    raise _OverBudget
                if all(fits(t) for t in checks[level]):
                    level += 1
        return found

    choices = [list(domains[x]) for x in order]
    known: dict[int, int] = {}  # position -> its value in every solution
    try:
        fit = search(choices, 2)
        if not fit:
            return NoSolution(nodes)
        if len(fit) == 1:
            known = dict(enumerate(fit[0]))
        for j in range(n if len(fit) == 2 else 0):
            v = fit[0][j]
            if any(f[j] != v for f in fit):
                continue  # two solutions give it different values
            others = [u for u in choices[j] if u != v]
            found = search(choices[:j] + [others] + choices[j + 1 :], 1)
            if found:
                fit += found  # may show other positions vary too
            else:
                known[j] = v
    except _OverBudget:
        return GaveUp({order[j]: v for j, v in known.items()}, nodes)
    return Fixed({order[j]: v for j, v in known.items()}, nodes)
