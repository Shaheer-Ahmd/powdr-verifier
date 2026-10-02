"""Bounded polynomial discharge for M3, with replayable local evidence.

No SMT, affine combinations, table evaluation, Boolean/range assumptions, or
stateful IO rules. Recipe lowering is separate from the arithmetic engine.
"""
from dataclasses import replace
import json

from .circuit_partition import partition_circuit
from .polynomial_normalization import (
    FIELD_PRIME, MAX_TERMS, UnsupportedPolynomial, polynomial_key, zero_equation_key,
)
from .witness_mapping import expression_columns, live_columns

POLYNOMIAL_REASONS = (
    'polynomial-zero', 'polynomial-reference-match', 'nonzero-scale-reference-match',
    'stateless-polynomial-reference-match', 'stateless-polynomial-inactive',
)
SCHEMA = 'polynomial-match-v1'


def constant(key):
    if not key:
        return 0
    return key[0][1] if len(key) == 1 and key[0][0] == () else None


class RecipePolynomials:
    """Per-direction adapter: fold constant recipes, intern other recipes opaquely.

Only syntactically identical symbolic recipes share atoms. Atoms cannot collide
with any reserved circuit/witness column. All expressions compared must use the
same adapter. No symbolic division cancellation is performed.
"""
    def __init__(self, reserved, *, max_terms=MAX_TERMS):
        polynomial_key(0, max_terms=max_terms)  # Validate even for an empty sweep.
        self.max_terms = max_terms
        self.reserved = set(reserved)
        self.atoms, self.atom_definitions, self.cache = {}, {}, {}

    def lower(self, expr):
        if isinstance(expr, dict):
            if set(expr) == {'Constant'}:
                return expr['Constant']
            kind, args = next(iter(expr.items()))
            if kind == 'QuotientOrZero':
                denominator = constant(self.key(args[1]))
                if denominator is not None:
                    return (0 if denominator == 0 else
                            [self.lower(args[0]), '*', pow(denominator, -1, FIELD_PRIME)])
            if kind == 'IfEqZero':
                condition = constant(self.key(args[0]))
                if condition is not None:
                    return self.lower(args[1] if condition == 0 else args[2])
            raw = json.dumps(expr, sort_keys=True)
            if raw not in self.atoms:
                name = f'classification_recipe@{len(self.atoms)}'
                while name in self.reserved:
                    name += '_'
                self.reserved.add(name)
                self.atoms[raw] = name
                self.atom_definitions[name] = expr
            return self.atoms[raw]
        if isinstance(expr, list):
            if len(expr) == 2 and expr[0] == '-':
                return ['-', self.lower(expr[1])]
            return [self.lower(x) if i % 2 == 0 else x for i, x in enumerate(expr)]
        return expr

    def key(self, expr):
        raw = json.dumps(expr, sort_keys=True)
        if raw not in self.cache:
            expression_columns(expr)
            self.cache[raw] = polynomial_key(self.lower(expr), max_terms=self.max_terms)
        return self.cache[raw]

    def bus(self, bus):
        return (bus['id'], self.key(bus['mult']), tuple(self.key(a) for a in bus['args']))


class PolynomialMatcher:
    """Reference-only indexes. No candidate equation is ever used as a premise."""
    def __init__(self, reference, mapping, *, max_terms=MAX_TERMS):
        self.reference = partition_circuit(reference)
        self.poly = RecipePolynomials(mapping.reference_columns | mapping.candidate_columns,
                                      max_terms=max_terms)
        self.exact, self.scaled, self.buses = None, None, None

    def algebraic_index(self):
        if self.exact is not None:
            return
        self.exact, self.scaled = {}, {}
        for index, expr in enumerate(self.reference.algebraic):
            try:
                key = self.poly.key(expr)
            except (UnsupportedPolynomial, RecursionError):
                continue
            self.exact.setdefault(key, index)
            if key:
                self.scaled.setdefault(zero_equation_key(key), (index, key[0][1]))

    def bus_index(self):
        if self.buses is not None:
            return
        self.buses = {}
        for item in self.reference.stateless:
            try:
                key = self.poly.bus(item.interaction)
            except (UnsupportedPolynomial, RecursionError):
                continue
            self.buses.setdefault(key, item.index)

    def match(self, goal):
        if goal.kind not in ('algebraic', 'stateless') or goal.status != 'residual':
            return None
        rule, reference_index, scale = None, None, None
        try:
            if goal.kind == 'algebraic':
                key = self.poly.key(goal.mapped)
                if not key:
                    rule = 'polynomial-zero'
                else:
                    self.algebraic_index()
                    if key in self.exact:
                        rule, reference_index = 'polynomial-reference-match', self.exact[key]
                    elif zero_equation_key(key) in self.scaled:
                        reference_index, coefficient = self.scaled[zero_equation_key(key)]
                        scale = key[0][1] * pow(coefficient, -1, FIELD_PRIME) % FIELD_PRIME
                        rule = 'nonzero-scale-reference-match'
            elif not self.poly.key(goal.mapped['mult']):
                rule = 'stateless-polynomial-inactive'
            else:
                self.bus_index()
                key = self.poly.bus(goal.mapped)
                if key in self.buses:
                    rule, reference_index = 'stateless-polynomial-reference-match', self.buses[key]
        except (UnsupportedPolynomial, RecursionError):
            return None  # Unavailable arithmetic is never a proof.
        if rule is None:
            return None
        return {'schema': SCHEMA, 'field': FIELD_PRIME, 'max_terms': self.poly.max_terms,
                'kind': goal.kind, 'index': goal.index, 'rule': rule,
                'reference_index': reference_index, 'scale': scale, 'assumptions': []}


def discharge_polynomial_matches(reference, mapping, obligations, *, max_terms=MAX_TERMS):
    """Internal adapter over validated cheap_sweep obligations; preserves all goals."""
    matcher = None
    out = []
    for goal in obligations:
        proof = None
        if goal.status == 'residual' and goal.kind in ('algebraic', 'stateless'):
            if matcher is None:
                matcher = PolynomialMatcher(reference, mapping, max_terms=max_terms)
            proof = matcher.match(goal)
        out.append(replace(goal, status='discharged', reason=proof['rule'], proof=proof)
                   if proof else goal)
    return out


def check_polynomial_proof(reference, candidate, mapping, proof):
    """Replay a single record; see check_polynomial_proofs for batch replay."""
    return check_polynomial_proofs(reference, candidate, mapping, [proof])


def check_polynomial_proofs(reference, candidate, mapping, proofs):
    """Replay evidence from original circuits and mapping, without the matcher.

Caller binds inputs/mapping to the saved sweep's hashes. Metadata cannot grant
assumptions. Invalid claims raise ValueError; unavailable arithmetic also fails.
"""
    from .cheap_obligations import substitute_expression

    def require(condition):
        if not condition:
            raise ValueError('Invalid polynomial proof')

    require(mapping.total and mapping.reference_columns == live_columns(reference)
            and mapping.candidate_columns == live_columns(candidate))
    require(all(expression_columns(e) <= mapping.reference_columns for e in mapping.witnesses.values()))
    ref, cand = partition_circuit(reference), partition_circuit(candidate)
    adapters = {}
    candidate_buses = {item.index: item.interaction for item in cand.stateless}
    reference_buses = {item.index: item.interaction for item in ref.stateless}
    for proof in proofs:
        require(set(proof) == {'schema', 'field', 'max_terms', 'kind', 'index', 'rule',
                               'reference_index', 'scale', 'assumptions'})
        require(proof['schema'] == SCHEMA and proof['field'] == FIELD_PRIME and proof['assumptions'] == [])
        limit = proof['max_terms']
        require(type(limit) is int and 0 < limit <= MAX_TERMS)
        if limit not in adapters:
            adapters[limit] = RecipePolynomials(mapping.reference_columns | mapping.candidate_columns,
                                               max_terms=limit)
        poly = adapters[limit]
        index, ri, rule = proof['index'], proof['reference_index'], proof['rule']
        require(type(index) is int and index >= 0)
        if proof['kind'] == 'algebraic':
            require(index < len(cand.algebraic))
            goal = poly.key(substitute_expression(cand.algebraic[index], mapping.witnesses))
            if rule == 'polynomial-zero':
                require(not goal and ri is None and proof['scale'] is None)
            else:
                require(type(ri) is int and 0 <= ri < len(ref.algebraic))
                source = poly.key(ref.algebraic[ri])
                if rule == 'polynomial-reference-match':
                    require(goal == source and proof['scale'] is None)
                else:
                    scale = proof['scale']
                    require(rule == 'nonzero-scale-reference-match' and type(scale) is int
                            and 0 < scale < FIELD_PRIME and bool(source))
                    require(goal == tuple((term, coeff*scale % FIELD_PRIME) for term, coeff in source))
        else:
            require(proof['kind'] == 'stateless' and proof['scale'] is None)
            require(index in candidate_buses)
            bus = candidate_buses[index]
            mapped = dict(bus, mult=substitute_expression(bus['mult'], mapping.witnesses),
                          args=[substitute_expression(a, mapping.witnesses) for a in bus['args']])
            if rule == 'stateless-polynomial-inactive':
                require(ri is None and not poly.key(mapped['mult']))
            else:
                require(rule == 'stateless-polynomial-reference-match' and type(ri) is int
                        and ri in reference_buses)
                require(poly.bus(mapped) == poly.bus(reference_buses[ri]))
    return True
