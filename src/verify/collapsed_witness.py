"""Conservative uniform-collapse witness proposals, not proof discharge.

For a candidate equation containing at least two unmapped variables, try
mapping all of them to one reference column. Accept a proposal only when
the substituted equation has the same polynomial as a reference equation.
All candidate equations and IO obligations still require subsequent proof.
"""
from dataclasses import replace
from typing import Any

from ..lens.loader import machine_of
from .witness_mapping import MappingResult, expression_columns

FIELD_PRIME = 2013265921
MAX_TERMS = 2048


class UnsupportedPolynomial(ValueError):
    pass


def polynomial_key(expr: Any, substitutions=None):
    """Bounded sparse-polynomial key over BabyBear; no division recipes.

Substitution RHSs are already reference-side expressions, so they are not
recursively substituted through candidate names again.
"""
    substitutions = substitutions or {}

    def add(a, b, scale=1):
        out = dict(a)
        for term, coefficient in b.items():
            value = (out.get(term, 0) + scale * coefficient) % FIELD_PRIME
            if value:
                out[term] = value
            else:
                out.pop(term, None)
        if len(out) > MAX_TERMS:
            raise UnsupportedPolynomial('Polynomial exceeds term budget')
        return out

    def multiply(a, b):
        if len(a) * len(b) > MAX_TERMS:
            raise UnsupportedPolynomial('Polynomial expansion exceeds budget')
        out = {}
        for lhs, lc in a.items():
            for rhs, rc in b.items():
                term = tuple(sorted(lhs + rhs))
                out = add(out, {term: lc * rc})
        return out

    def visit(node, use_substitutions=True):
        if type(node) is int:
            value = node % FIELD_PRIME
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


def add_collapsed_witnesses(reference, candidate, base: MappingResult):
    """Return a new mapping and proposal provenance; do not mutate base.

Only handles the narrow case of two or more unknowns appearing linearly,
each multiplied by one variable. Other missing recipes remain unresolved.
"""
    witnesses = dict(base.witnesses)
    sources = dict(base.sources)
    unresolved = dict(base.unresolved)
    reference_equations = {}
    for index, expr in enumerate(machine_of(reference)['constraints']):
        try:
            key = polynomial_key(expr)
        except UnsupportedPolynomial:
            continue
        if key:  # Ignore tautologies as pattern evidence.
            reference_equations.setdefault(key, index)

    proposals = []
    for candidate_index, expr in enumerate(machine_of(candidate)['constraints']):
        missing = expression_columns(expr) & unresolved.keys()
        if len(missing) < 2:
            continue
        try:
            raw = polynomial_key(expr)
        except UnsupportedPolynomial:
            continue
        # Each missing variable must occur in exactly one quadratic monomial
        # whose other factor is not another missing variable.
        eligible = True
        for variable in missing:
            terms = [term for term, _ in raw if variable in term]
            if len(terms) != 1:
                eligible = False
                break
            term = terms[0]
            if len(term) != 2 or term.count(variable) != 1 or sum(v in missing for v in term) != 1:
                eligible = False
                break
        if not eligible:
            continue

        for reference_column in sorted(base.reference_columns):
            trial = witnesses | {name: reference_column for name in missing}
            try:
                key = polynomial_key(expr, trial)
            except UnsupportedPolynomial:
                continue
            if key not in reference_equations:
                continue
            for name in sorted(missing):
                witnesses[name] = reference_column
                sources[name] = 'collapsed-witness'
                unresolved.pop(name)
            proposals.append({
                'candidate_constraint': candidate_index,
                'reference_constraint': reference_equations[key],
                'variables': sorted(missing),
                'witness': reference_column,
            })
            break

    for expr in witnesses.values():
        if not expression_columns(expr) <= base.reference_columns:
            raise ValueError('Witness contains non-reference columns')
    return replace(base, witnesses=witnesses, sources=sources, unresolved=unresolved), proposals
