"""PolySolver: solver-free entailment checks for polynomial identities over F_p.

Standalone on purpose: it imports nothing from the verifier, and knows only
variables, polynomials, ranges and definitions. See ``solver.py``.
"""

from .defs import NO_DEFS, Defs, InvalidDefs, Opaque
from .expr import Expr, UnsupportedExpr, product_factors, sum_terms, variables
from .solver import BABYBEAR, Implied, PolySolver, UndefinedVariable, Unknown, Verdict
from .table import Var, VarTable
from .witness import find_uniform_witness, find_witness

__all__ = [
    "BABYBEAR",
    "NO_DEFS",
    "Defs",
    "Expr",
    "Implied",
    "InvalidDefs",
    "Opaque",
    "PolySolver",
    "UndefinedVariable",
    "Unknown",
    "UnsupportedExpr",
    "Var",
    "VarTable",
    "Verdict",
    "find_uniform_witness",
    "find_witness",
    "product_factors",
    "sum_terms",
    "variables",
]
