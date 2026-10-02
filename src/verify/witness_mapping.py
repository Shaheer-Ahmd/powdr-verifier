"""Explicit structural witnesses; no SMT or equivalence verdicts.

Supported recipes: Constant, QuotientOrZero, and IfEqZero, plus arithmetic
expressions. Unknown recipe forms fail closed.
"""
from dataclasses import dataclass, replace
from typing import Any

from ..lens.loader import machine_of
from .circuit_partition import partition_circuit


def expression_columns(node: Any) -> set[str]:
    if type(node) is int:
        return set()
    if isinstance(node, str) and '@' in node:
        return {node}
    if isinstance(node, dict) and set(node) == {'Constant'}:
        if type(node['Constant']) is not int:
            raise ValueError('Constant requires an integer')
        return set()
    if isinstance(node, dict) and set(node) == {'IfEqZero'}:
        args = node['IfEqZero']
        if not isinstance(args, list) or len(args) != 3:
            raise ValueError('IfEqZero requires three arguments')
        return set().union(*(expression_columns(x) for x in args))
    if isinstance(node, dict) and set(node) == {'QuotientOrZero'}:
        args = node['QuotientOrZero']
        if not isinstance(args, list) or len(args) != 2:
            raise ValueError('QuotientOrZero requires two arguments')
        return expression_columns(args[0]) | expression_columns(args[1])
    if isinstance(node, list):
        if len(node) == 2 and node[0] == '-':
            return expression_columns(node[1])
        if node and len(node) % 2 == 1:
            if any(op not in ('+', '-', '*') for op in node[1::2]):
                raise ValueError(f'Unsupported arithmetic operator: {node!r}')
            return set().union(*(expression_columns(x) for x in node[::2]))
    raise ValueError(f'Unsupported expression: {node!r}')


def live_columns(data: Any) -> set[str]:
    partition = partition_circuit(data)
    names = set()
    for expr in partition.algebraic:
        names.update(expression_columns(expr))
    for item in partition.stateful + partition.stateless:
        bus = item.interaction
        if 'mult' not in bus or 'args' not in bus:
            raise ValueError(f'Incomplete bus record at index {item.index}')
        names.update(expression_columns(bus['mult']))
        for expr in bus['args']:
            names.update(expression_columns(expr))
    return names


@dataclass
class MappingResult:
    reference_columns: set[str]
    candidate_columns: set[str]
    witnesses: dict[str, Any]
    sources: dict[str, str]
    unresolved: dict[str, str]
    # Preserve every candidate definition, including inactive helpers and
    # alternatives. Later stages must decide its proper semantic treatment.
    derived_records: tuple[Any, ...]
    substitution_records: tuple[Any, ...] = ()

    @property
    def total(self) -> bool:
        return not self.unresolved and self.witnesses.keys() == self.candidate_columns


def transform_expression(expr, column):
    """Validate and replace column leaves, without recursing into replacements."""
    expression_columns(expr)
    if type(expr) is int:
        return expr
    if isinstance(expr, str):
        return column(expr)
    if isinstance(expr, dict):
        if 'Constant' in expr:
            return expr['Constant']
        kind, args = next(iter(expr.items()))
        return {kind: [transform_expression(x, column) for x in args]}
    if len(expr) == 2 and expr[0] == '-':
        return ['-', transform_expression(expr[1], column)]
    return [transform_expression(x, column) if i % 2 == 0 else x for i, x in enumerate(expr)]


def collect_definitions(records):
    definitions: dict[str, list[Any]] = {}
    for record in records:
        if not isinstance(record, list) or len(record) != 3 or type(record[0]) is not bool:
            raise ValueError(f'Unsupported derived record: {record!r}')
        _, name, definition = record
        if not isinstance(name, str) or '@' not in name:
            raise ValueError(f'Invalid derived column name: {name!r}')
        definitions.setdefault(name, []).append(definition)
    return definitions


class CandidateResolver:
    """First-recipe resolution shared by mapping and the definition audit.

    ``fixed`` freezes an already chosen live-column map. Audit-only helper
    columns can be resolved without changing that map or its totality domain.
    """
    def __init__(self, reference_columns, records, substitutions=(), *, fixed=None, sources=None):
        self.reference_columns = reference_columns
        self.definitions = collect_definitions(records)
        self.subs = {}
        for record in substitutions:
            if not isinstance(record, list) or len(record) != 2:
                raise ValueError(f'Unsupported substitution record: {record!r}')
            name, definition = record
            if not isinstance(name, str) or '@' not in name:
                raise ValueError(f'Invalid substitution column name: {name!r}')
            self.subs.setdefault(name, []).append(definition)
        self.memo = dict(fixed or {})
        self.origins = dict(sources or {})
        self.active = []
        self.used = set()
        self.discovered = []

    def expand(self, expr):
        return transform_expression(expr, self.resolve)

    def resolve(self, name):
        if name not in self.used:
            self.used.add(name)
            self.discovered.append(name)
        if name in self.memo:
            return self.memo[name]
        # Reference variables are terminal leaves, even if metadata also
        # supplies a recipe for a same-name candidate variable.
        if name in self.reference_columns:
            self.origins[name] = 'same-name'
            return name
        if name in self.active:
            raise ValueError('Definition cycle: ' + ' -> '.join(self.active + [name]))
        choices = self.definitions.get(name)
        source = 'derived'
        if not choices:
            choices = self.subs.get(name)
            source = 'substitution'
        if not choices:
            raise ValueError(f'No witness source for {name}')
        # Deterministic first-definition policy. Other records are preserved;
        # no alternate-definition search in this initial implementation.
        self.active.append(name)
        try:
            witness = self.expand(choices[0])
        finally:
            self.active.pop()
        if not expression_columns(witness) <= self.reference_columns:
            raise ValueError(f'Non-reference dependencies remain for {name}')
        self.memo[name] = witness
        self.origins[name] = source
        return witness


def build_mapping(reference: Any, candidate: Any, substitutions=()) -> MappingResult:
    ref_names = live_columns(reference)
    cand_names = live_columns(candidate)
    records = tuple(machine_of(candidate).get('derived_columns', []))
    substitutions = tuple(substitutions)
    resolver = CandidateResolver(ref_names, records, substitutions)
    witnesses, sources, unresolved = {}, {}, {}
    for name in sorted(cand_names):
        try:
            witnesses[name] = resolver.resolve(name)
            sources[name] = resolver.origins[name]
        except ValueError as error:
            unresolved[name] = str(error)
    return MappingResult(ref_names, cand_names, witnesses, sources, unresolved, records, substitutions)


def add_exported_hint_witnesses(reference, base: MappingResult):
    """Use reference-side non-new recipes as candidate witness proposals.

    Optimizer equal-zero rewrites retain Boolean marker columns, so identity
    can be total yet be the wrong reverse witness. Exported [False, v, recipe]
    hints can propose another value for the candidate copy. They are NEVER
    asserted as reference facts: every affected candidate constraint and IO
    must subsequently be checked under this changed map. Identity remains the
    default in build_mapping; callers explicitly request this source.
    """
    records = machine_of(reference).get('derived_columns', [])
    definitions = collect_definitions(records)
    witnesses, sources, unresolved = dict(base.witnesses), dict(base.sources), dict(base.unresolved)
    proposals = []
    for index, (is_new, name, recipe) in enumerate(records):
        if is_new or name not in base.candidate_columns or len(definitions[name]) != 1:
            continue
        deps = expression_columns(recipe)
        if name in deps or not deps <= base.reference_columns:
            continue
        witnesses[name] = transform_expression(recipe, lambda v: v)
        sources[name] = 'exported-reference-hint'
        unresolved.pop(name, None)
        proposals.append({'reference_derived_index': index, 'column': name,
                          'witness': witnesses[name]})
    return replace(base, witnesses=witnesses, sources=sources, unresolved=unresolved), proposals
