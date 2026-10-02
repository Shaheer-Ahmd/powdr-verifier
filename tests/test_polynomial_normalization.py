"""Arithmetic and migration contracts; no solver calls."""

from copy import deepcopy
from itertools import product

import pytest

from src.verify import collapsed_witness, zero_check
from src.verify.polynomial_normalization import (
    FIELD_PRIME as P,
    MAX_TERMS,
    PolynomialBudgetExceeded,
    UnsupportedPolynomial,
    polynomial_key,
    zero_equation_key,
)


def test_expansion_collection_order_and_field_residues():
    factored = ['x@0', '*', ['y@1', '+', 'z@2']]
    expanded = [['z@2', '*', 'x@0'], '+', ['x@0', '*', 'y@1']]
    assert polynomial_key(factored) == polynomial_key(expanded)
    assert polynomial_key([factored, '-', expanded]) == ()
    assert polynomial_key(['-', 'x@0']) == polynomial_key([P-1, '*', 'x@0'])
    assert polynomial_key([P+7, '+', -7]) == ()
    assert polynomial_key(['x@0', '+', 'x@0']) == ((('x@0',), 2),)


def test_equation_scale_is_not_expression_equality():
    x, twice_x = polynomial_key('x@0'), polynomial_key([2, '*', 'x@0'])
    assert x != twice_x  # Especially important for bus values!
    assert zero_equation_key(x) == zero_equation_key(twice_x)
    assert zero_equation_key(polynomial_key(0)) == ()
    assert zero_equation_key(polynomial_key(7)) == (((), 1),)
    assert zero_equation_key(polynomial_key(['x@0', '+', 1])) != zero_equation_key(x)


def test_one_pass_substitution_and_no_mutation():
    expr = ['x@0', '+', 'y@1']
    subs = {'x@0': ['y@1', '+', 1], 'y@1': 7}
    original = deepcopy((expr, subs))
    assert polynomial_key(expr, subs) == polynomial_key(['y@1', '+', 8])
    assert (expr, subs) == original
    assert polynomial_key('x@0', {'x@0': 'x@0'}) == polynomial_key('x@0')


@pytest.mark.parametrize('expr', [True, None, 1.5, 'not_a_column', [],
                                 ['x@0', '+'], ['x@0', '/', 2],
                                 {'Constant': 3},
                                 {'QuotientOrZero': ['x@0', 2]},
                                 {'IfEqZero': ['x@0', 0, 1]}])
def test_core_rejects_recipes_and_unsupported_syntax(expr):
    with pytest.raises(UnsupportedPolynomial) as error:
        polynomial_key(expr)
    assert not isinstance(error.value, PolynomialBudgetExceeded)


def test_term_and_expansion_budgets_are_distinct_from_unsupported_syntax():
    two_terms = ['x@0', '+', 'y@1']
    assert polynomial_key(two_terms, max_terms=2)
    with pytest.raises(PolynomialBudgetExceeded, match='term budget'):
        polynomial_key(two_terms, max_terms=1)
    # Four term products, even though the resulting polynomial has only three.
    with pytest.raises(PolynomialBudgetExceeded, match='expansion'):
        polynomial_key([two_terms, '*', two_terms], max_terms=3)
    assert polynomial_key([two_terms, '*', two_terms], max_terms=4)
    assert issubclass(PolynomialBudgetExceeded, UnsupportedPolynomial)
    assert MAX_TERMS == 2048


@pytest.mark.parametrize('limit', [0, -1, True, 2.5, '2'])
def test_bad_budget_rejected(limit):
    with pytest.raises(ValueError, match='positive integer'):
        polynomial_key('x@0', max_terms=limit)


@pytest.mark.parametrize('prime', [7, P+2, True, float(P)])
def test_other_fields_are_explicitly_out_of_scope(prime):
    with pytest.raises(ValueError, match='BabyBear'):
        polynomial_key(0, field_prime=prime)
    with pytest.raises(ValueError, match='BabyBear'):
        zero_equation_key((), field_prime=prime)


def test_call_configuration_does_not_leak():
    expr = ['x@0', '+', 'y@1']
    expected = polynomial_key(expr, field_prime=P, max_terms=2)
    with pytest.raises(PolynomialBudgetExceeded):
        polynomial_key(expr, max_terms=1)
    assert polynomial_key(expr) == expected


def test_legacy_import_and_zero_checker_use_shared_engine():
    assert collapsed_witness.polynomial_key is polynomial_key
    assert collapsed_witness.UnsupportedPolynomial is UnsupportedPolynomial
    assert zero_check.polynomial_key is polynomial_key


def test_keys_agree_with_independent_numeric_evaluation():
    expressions = [
        ['x@0', '*', ['y@1', '+', -7]],
        [['x@0', '+', 1], '*', ['x@0', '-', 1]],
        [[P+2, '*', 'y@1'], '-', ['x@0', '*', 'y@1']],
        ['-', [['x@0', '-', 'y@1'], '*', ['y@1', '+', 3]]],
    ]

    def evaluate(expr, values):
        if type(expr) is int:
            return expr % P
        if isinstance(expr, str):
            return values[expr]
        if len(expr) == 2:
            return -evaluate(expr[1], values) % P
        left, op, right = expr
        a, b = evaluate(left, values), evaluate(right, values)
        return {'+': lambda: a+b, '-': lambda: a-b, '*': lambda: a*b}[op]() % P

    for expr in expressions:
        key = polynomial_key(expr)
        for x, y in product((0, 1, 7, P-1), repeat=2):
            values = {'x@0': x, 'y@1': y}
            total = 0
            for term, coefficient in key:
                value = coefficient
                for variable in term:
                    value *= values[variable]
                total += value
            assert total % P == evaluate(expr, values)
