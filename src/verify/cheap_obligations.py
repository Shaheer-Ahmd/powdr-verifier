"""M3 cheap discharge for algebraic and stateless obligations only.

No SMT, no stateful IO proof, and no whole-direction equivalence verdict.
QuotientOrZero is retained as an opaque, structurally interned term rather
than passed to lens's unsupported-node fallback. Caches are local to a sweep.
"""
from dataclasses import dataclass
from typing import Any

from ..lens.diff import canon_constraint
from .circuit_partition import partition_circuit
from .witness_mapping import expression_columns, live_columns, MappingResult


@dataclass
class Obligation:
    kind: str
    index: int
    original: Any
    mapped: Any
    status: str
    reason: str


def substitute_expression(expr, witnesses):
    """Simultaneous substitution: RHSs already refer to reference columns."""
    expression_columns(expr)
    if type(expr) is int:
        return expr
    if isinstance(expr, str):
        if expr not in witnesses:
            raise ValueError(f'Missing witness for {expr}')
        return witnesses[expr]
    if isinstance(expr, dict):
        return {'QuotientOrZero': [substitute_expression(x, witnesses)
                                   for x in expr['QuotientOrZero']]}
    if len(expr) == 2 and expr[0] == '-':
        return ['-', substitute_expression(expr[1], witnesses)]
    return [substitute_expression(x, witnesses) if i % 2 == 0 else x
            for i, x in enumerate(expr)]


class _Keys:
    def __init__(self):
        self.recipes = {}

    def expression(self, expr):
        expression_columns(expr)  # Reject malformed/unsupported ASTs first.
        return canon_constraint(self._lower(expr))

    def _lower(self, expr):
        if type(expr) is int or isinstance(expr, str):
            return expr
        if isinstance(expr, dict):
            num, den = expr['QuotientOrZero']
            recipe = ('QuotientOrZero', self.expression(num), self.expression(den))
            if recipe not in self.recipes:
                # Input column names must contain @; these internal names do
                # not, so they cannot collide with validated input columns.
                self.recipes[recipe] = f'__m3_opaque_qoz_{len(self.recipes)}'
            return self.recipes[recipe]
        if len(expr) == 2 and expr[0] == '-':
            return ['-', self._lower(expr[1])]
        return [self._lower(x) if i % 2 == 0 else x for i, x in enumerate(expr)]

    def bus(self, bus):
        return ('stateless', bus['id'], self.expression(bus['mult']),
                tuple(self.expression(expr) for expr in bus['args']))


def cheap_sweep(reference, candidate, mapping: MappingResult):
    """Return all local obligations, including undischargeable residuals.

Reference constraints are used as premises, never candidate constraints.
Derived metadata is not automatically asserted or turned into obligations.
Stateful interface and definition-policy handling belong to later stages.
"""
    if not mapping.total:
        raise ValueError('Cannot sweep with an incomplete mapping')
    if mapping.reference_columns != live_columns(reference) or mapping.candidate_columns != live_columns(candidate):
        raise ValueError('Mapping column sets do not match this pair')
    for expr in mapping.witnesses.values():
        if not expression_columns(expr) <= mapping.reference_columns:
            raise ValueError('Witness mentions non-reference columns')

    ref, cand = partition_circuit(reference), partition_circuit(candidate)
    keys = _Keys()
    reference_keys = {('algebraic', keys.expression(expr)) for expr in ref.algebraic}
    reference_keys.update(keys.bus(item.interaction) for item in ref.stateless)
    discharged = set()
    obligations = []

    def add(kind, index, original, mapped, key, trivial):
        if key in discharged:
            status, reason = 'discharged', 'cache'
        elif trivial:
            status, reason = 'discharged', 'trivial'
        elif key in reference_keys:
            status, reason = 'discharged', 'canonical-match'
        else:
            status, reason = 'residual', 'requires-proof'
        if status == 'discharged':
            discharged.add(key)
        obligations.append(Obligation(kind, index, original, mapped, status, reason))

    for index, expr in enumerate(cand.algebraic):
        mapped = substitute_expression(expr, mapping.witnesses)
        key = keys.expression(mapped)
        add('algebraic', index, expr, mapped, ('algebraic', key), key == ('c', 0))

    for item in cand.stateless:
        bus = item.interaction
        mapped = dict(bus)
        mapped['mult'] = substitute_expression(bus['mult'], mapping.witnesses)
        mapped['args'] = [substitute_expression(expr, mapping.witnesses) for expr in bus['args']]
        add('stateless', item.index, bus, mapped, keys.bus(mapped),
            keys.expression(mapped['mult']) == ('c', 0))
    return obligations
