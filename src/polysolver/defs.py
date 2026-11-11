"""Definitions ``x := t`` for variables that are not declared.

A ``Defs`` is built and validated by ``PolySolver.make_defs`` (checks D1-D3).
A right-hand side is a polynomial, a ``Quotient`` of two, or ``Opaque``.
It caches the expansion of each right-hand side.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


class InvalidDefs(ValueError):
    """A definition breaks D1 (fresh) or D2 (flat)."""


@dataclass(frozen=True)
class Opaque:
    """A right-hand side we never look inside, e.g. a QuotientOrZero recipe."""

    content: Any


@dataclass(frozen=True)
class Quotient:
    """``n / d`` if ``d != 0``, else 0: powdr's QuotientOrZero. Rule Q reads it.

    ``n`` and ``d`` are expressions over declared variables, like any other
    right-hand side.
    """

    n: Any
    d: Any


@dataclass(frozen=True)
class Defs:
    """Validated definitions; only valid with the solver that made them."""

    polys: dict = field(default_factory=dict)  # Var -> Poly, or None if too big
    opaque: frozenset = frozenset()  # Vars defined as Opaque
    owner: int = 0  # id() of the solver's VarTable
    # Var -> (n, d) as Polys for a Quotient, or None if either is too big
    quotients: dict = field(default_factory=dict)

    def defines(self, v: int) -> bool:
        return v in self.polys or v in self.opaque or v in self.quotients


NO_DEFS = Defs()
