"""PolySolver: solver-free entailment checks for polynomial identities over F_p.

Standalone on purpose: it imports nothing from the verifier, and knows only
variables, polynomials, ranges and definitions. See ``solver.py``.
"""

from .defs import NO_DEFS, Cond, Defs, InvalidDefs, Opaque, Quotient
from .expr import Expr, UnsupportedExpr, product_factors, sum_terms, variables
from .solver import (
    BABYBEAR,
    COND_CAP,
    AnyOf,
    Bounded,
    Goal,
    Implied,
    PolySolver,
    UndefinedVariable,
    Unknown,
    Verdict,
    Zero,
)
from .table import Var, VarTable
from .witness import find_uniform_witness, find_witness

__all__ = [
    "BABYBEAR",
    "COND_CAP",
    "AnyOf",
    "Bounded",
    "Cond",
    "NO_DEFS",
    "Defs",
    "Expr",
    "Goal",
    "Implied",
    "InvalidDefs",
    "Opaque",
    "PolySolver",
    "Quotient",
    "UndefinedVariable",
    "Unknown",
    "UnsupportedExpr",
    "Var",
    "VarTable",
    "Verdict",
    "Zero",
    "find_uniform_witness",
    "find_witness",
    "product_factors",
    "sum_terms",
    "variables",
]
