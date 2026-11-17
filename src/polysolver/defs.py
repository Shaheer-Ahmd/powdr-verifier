"""Definitions ``x := t`` for variables that are not declared.

A ``Defs`` is built and validated by ``PolySolver.make_defs`` (checks D1-D3).
A right-hand side is a polynomial, a ``Quotient`` of two, a ``Cond``, or
``Opaque``. A ``Quotient`` whose denominator is a nonzero constant is a
polynomial, and is stored as one. It caches the expansion of each
right-hand side.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


class InvalidDefs(ValueError):
    """A definition breaks D1 (fresh) or D2 (flat)."""


@dataclass(frozen=True)
class Opaque:
    """A right-hand side we never look inside, e.g. a function no rule can read."""

    content: Any


@dataclass(frozen=True)
class Quotient:
    """``n / d`` if ``d != 0``, else 0. Rule Q reads it.

    ``n`` and ``d`` are expressions over declared variables, like any other
    right-hand side.
    """

    n: Any
    d: Any


@dataclass(frozen=True)
class Cond:
    """``z`` if ``g = 0``, else ``nz``. Rule I reads it.

    ``g`` is an expression over declared variables. ``z`` and ``nz`` are
    right-hand sides themselves: an expression, a ``Quotient`` or a ``Cond``.
    """

    g: Any
    z: Any
    nz: Any


@dataclass(frozen=True)
class Defs:
    """Validated definitions; only valid with the solver that made them."""

    polys: dict = field(default_factory=dict)  # Var -> Poly, or None if too big
    opaque: frozenset = frozenset()  # Vars defined as Opaque
    owner: int = 0  # id() of the solver's VarTable
    # Var -> (n, d) as Polys for a Quotient, or None if either is too big
    quotients: dict = field(default_factory=dict)
    # Var -> (g as a Poly, or None if too big; z; nz) for a Cond. The branches
    # stay as written, so rule I can define the variable as either one.
    conds: dict = field(default_factory=dict)

    def defines(self, v: int) -> bool:
        return v in self.polys or v in self.opaque or v in self.quotients or v in self.conds


NO_DEFS = Defs()
