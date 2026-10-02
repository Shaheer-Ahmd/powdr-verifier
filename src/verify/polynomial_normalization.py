"""Bounded sparse-polynomial normalization, without solver or circuit semantics.

Keys are sorted tuples of (monomial, coefficient); a monomial is a sorted tuple
of column names, () denotes a constant, and an empty key denotes zero.
Coefficients are canonical field residues. Expression keys preserve scale;
``zero_equation_key`` additionally identifies nonzero scalar multiples and
must NEVER be used to compare values such as bus payloads.

Only BabyBear is supported in this extraction. Recipes, witness discovery,
bus semantics, and proof discharge belong to callers. The optional explicit
substitution map is a legacy one-pass adapter: RHS expressions are already in
the reference vocabulary and are never recursively substituted again.
"""

from typing import Any

FIELD_PRIME = 2013265921
MAX_TERMS = 2048
PolynomialKey = tuple[tuple[tuple[str, ...], int], ...]


class UnsupportedPolynomial(ValueError):
    """The expression cannot be normalized; this is not a proof result."""


class PolynomialBudgetExceeded(UnsupportedPolynomial):
    """Normalization exceeded its bound; existing conservative catches apply."""


def _check_field(field_prime):
    if type(field_prime) is not int or field_prime != FIELD_PRIME:
        raise ValueError("Only the BabyBear field is supported")


def polynomial_key(
    expr: Any, substitutions=None, *, field_prime=FIELD_PRIME, max_terms=None
) -> PolynomialKey:
    """Normalize an expression, preserving the historical expansion order.

``max_terms`` bounds intermediate term dictionaries AND the Cartesian product
before multiplication (even if cancellation could later shrink it). It is not
a general wall-time, AST-size, recursion-depth, or memory limit. None selects
MAX_TERMS. Unsupported syntax and budget exhaustion raise distinct exceptions.
No cache or process-global recipe environment is maintained here.
"""
    _check_field(field_prime)
    limit = MAX_TERMS if max_terms is None else max_terms
    if type(limit) is not int or limit < 1:
        raise ValueError("max_terms must be a positive integer")
    substitutions = substitutions or {}

    def add(a, b, scale=1):
        out = dict(a)
        for term, coefficient in b.items():
            value = (out.get(term, 0) + scale * coefficient) % field_prime
            if value:
                out[term] = value
            else:
                out.pop(term, None)
        if len(out) > limit:
            raise PolynomialBudgetExceeded('Polynomial exceeds term budget')
        return out

    def multiply(a, b):
        if len(a) * len(b) > limit:
            raise PolynomialBudgetExceeded('Polynomial expansion exceeds budget')
        out = {}
        for lhs, lc in a.items():
            for rhs, rc in b.items():
                term = tuple(sorted(lhs + rhs))
                out = add(out, {term: lc * rc})
        return out

    def visit(node, use_substitutions=True):
        if type(node) is int:
            value = node % field_prime
            return {(): value} if value else {}
        if isinstance(node, str) and '@' in node:
            if use_substitutions and node in substitutions:
                return visit(substitutions[node], False)
            return {(node,): 1}
        if isinstance(node, list):
            if len(node) == 2 and node[0] == '-':
                return add({}, visit(node[1], use_substitutions), -1)
            if node and len(node) % 2 == 1:
                value = visit(node[0], use_substitutions)
                for i in range(1, len(node), 2):
                    rhs = visit(node[i + 1], use_substitutions)
                    if node[i] == '+':
                        value = add(value, rhs)
                    elif node[i] == '-':
                        value = add(value, rhs, -1)
                    elif node[i] == '*':
                        value = multiply(value, rhs)
                    else:
                        raise UnsupportedPolynomial('Unsupported operator')
                return value
        raise UnsupportedPolynomial('Not a supported polynomial expression')

    return tuple(sorted(visit(expr).items()))


def zero_equation_key(key: PolynomialKey, *, field_prime=FIELD_PRIME) -> PolynomialKey:
    """Normalize a polynomial_key result as an equation ``polynomial = 0``.

The input must be a canonical key from polynomial_key for the same field.
Zero remains zero. Otherwise divide by the first nonzero coefficient. This
does not preserve expression values, only the zero set of the equation.
"""
    _check_field(field_prime)
    if not key:
        return key
    inverse = pow(key[0][1], -1, field_prime)
    return tuple((term, coefficient * inverse % field_prime) for term, coefficient in key)
