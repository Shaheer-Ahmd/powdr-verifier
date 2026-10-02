"""Conservative uniform-collapse witness proposals, not proof discharge.

For a candidate equation containing at least two unmapped variables, try
mapping all of them to one reference column. Accept a proposal only when
the substituted equation has the same polynomial as a reference equation.
All candidate equations and IO obligations still require subsequent proof.
"""
from dataclasses import replace

from ..lens.loader import machine_of
from .witness_mapping import MappingResult, expression_columns
# Compatibility re-exports for earlier M2 scripts. New callers import the
# arithmetic module directly; this module only discovers witness proposals.
from .polynomial_normalization import (
    FIELD_PRIME as FIELD_PRIME,
    MAX_TERMS as MAX_TERMS,
    UnsupportedPolynomial as UnsupportedPolynomial,
    polynomial_key as polynomial_key,
)


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
