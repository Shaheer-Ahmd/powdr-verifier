"""M3 cheap discharge for algebraic and stateless obligations only.

No SMT, no stateful IO proof, and no whole-direction equivalence verdict.
QuotientOrZero is retained as an opaque, structurally interned term rather
than passed to lens's unsupported-node fallback. Caches are local to a sweep.
"""
from dataclasses import dataclass
from typing import Any

from ..lens.diff import canon_constraint
from .circuit_partition import partition_circuit
from .witness_mapping import expression_columns, live_columns, MappingResult, transform_expression


@dataclass
class Obligation:
    kind: str
    index: int
    original: Any
    mapped: Any
    status: str
    reason: str
    proof: dict | None = None  # Gadget certificate/claim or polynomial-match evidence.


def substitute_expression(expr, witnesses):
    """Simultaneous substitution: RHSs already refer to reference columns."""
    def column(name):
        if name not in witnesses:
            raise ValueError(f'Missing witness for {name}')
        return witnesses[name]
    return transform_expression(expr, column)


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
            if 'Constant' in expr:
                return expr['Constant']
            kind, args = next(iter(expr.items()))
            recipe = (kind, *(self.expression(arg) for arg in args))
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


def cheap_sweep(reference, candidate, mapping: MappingResult, *, definition_goals=(),
                zero_check_direction=None, reference_recv_bytes=False, polynomial_matching=False):
    """Return all local obligations, including undischargeable residuals.

Reference constraints are used as premises, never candidate constraints.
Derived metadata is never asserted. Explicit definition_goals supplied by the
definition audit use the same algebraic canonical rules. Stateful IO is separate.
Set zero_check_direction to completeness/soundness to enable the specialized
gadget rules with this exact mapping. reference_recv_bytes explicitly grants
the receive-byte contract; it is never enabled by default. Certificate evidence
and any assumptions are retained in each newly discharged obligation's proof.
polynomial_matching enables bounded reference-only matching after canonical
checks and before gadget checks. It does not discharge definition_goals.
"""
    if zero_check_direction not in (None, 'completeness', 'soundness'):
        raise ValueError('Unknown zero-check direction')
    if reference_recv_bytes and zero_check_direction is None:
        raise ValueError('Receive-byte contract requires zero_check_direction')
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
    for index, original, mapped in definition_goals:
        if not expression_columns(mapped) <= mapping.reference_columns:
            raise ValueError('Definition obligation mentions non-reference columns')
        key = keys.expression(mapped)
        same_sides = (isinstance(mapped, list) and len(mapped) == 3 and mapped[1] == '-'
                      and keys.expression(mapped[0]) == keys.expression(mapped[2]))
        add('derived-definition', index, original, mapped,
            ('algebraic', key), key == ('c', 0) or same_sides)
    if polynomial_matching:
        from .polynomial_matching import discharge_polynomial_matches
        obligations = discharge_polynomial_matches(reference, mapping, obligations)
    if zero_check_direction is not None:
        # Lazy import avoids a cycle: zero_check also offers an M2/M3 wrapper.
        from .zero_check import discharge_zero_checks
        before, after = ((reference, candidate) if zero_check_direction == 'completeness'
                         else (candidate, reference))
        obligations, _evidence = discharge_zero_checks(
            before, after, mapping, zero_check_direction, obligations,
            allow_recv_bytes=reference_recv_bytes)
    return obligations
