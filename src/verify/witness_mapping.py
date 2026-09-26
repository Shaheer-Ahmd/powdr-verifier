"""Explicit structural witnesses; no SMT or equivalence verdicts.

Supported recipe syntax in this first increment: integer constants, column
names, arithmetic expression lists, and QuotientOrZero definitions.
Unknown recipe forms fail closed. Pattern-based reconstruction is pending.
"""
from dataclasses import dataclass
from typing import Any

from ..lens.loader import machine_of
from .circuit_partition import partition_circuit


def expression_columns(node: Any) -> set[str]:
    if type(node) is int:
        return set()
    if isinstance(node, str) and '@' in node:
        return {node}
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

    @property
    def total(self) -> bool:
        return not self.unresolved and self.witnesses.keys() == self.candidate_columns


def build_mapping(reference: Any, candidate: Any, substitutions=()) -> MappingResult:
    ref_names = live_columns(reference)
    cand_names = live_columns(candidate)
    records = tuple(machine_of(candidate).get('derived_columns', []))
    definitions: dict[str, list[Any]] = {}
    for record in records:
        if not isinstance(record, list) or len(record) != 3:
            raise ValueError(f'Unsupported derived record: {record!r}')
        _, name, definition = record
        if not isinstance(name, str) or '@' not in name:
            raise ValueError(f'Invalid derived column name: {name!r}')
        definitions.setdefault(name, []).append(definition)

    subs: dict[str, list[Any]] = {}
    for record in substitutions:
        if not isinstance(record, list) or len(record) != 2:
            raise ValueError(f'Unsupported substitution record: {record!r}')
        name, definition = record
        if not isinstance(name, str) or '@' not in name:
            raise ValueError(f'Invalid substitution column name: {name!r}')
        subs.setdefault(name, []).append(definition)

    memo: dict[str, Any] = {}
    origins: dict[str, str] = {}
    active: list[str] = []

    def expand(expr):
        expression_columns(expr)  # Validate before traversing.
        if type(expr) is int:
            return expr
        if isinstance(expr, str):
            return resolve(expr)
        if isinstance(expr, dict):
            return {'QuotientOrZero': [expand(x) for x in expr['QuotientOrZero']]}
        if len(expr) == 2 and expr[0] == '-':
            return ['-', expand(expr[1])]
        return [expand(x) if i % 2 == 0 else x for i, x in enumerate(expr)]

    def resolve(name):
        # Reference variables are terminal leaves, even if metadata also
        # supplies a recipe for a same-name candidate variable.
        if name in ref_names:
            origins[name] = 'same-name'
            return name
        if name in memo:
            return memo[name]
        if name in active:
            raise ValueError('Definition cycle: ' + ' -> '.join(active + [name]))
        choices = definitions.get(name)
        source = 'derived'
        if not choices:
            choices = subs.get(name)
            source = 'substitution'
        if not choices:
            raise ValueError(f'No witness source for {name}')
        # Deterministic first-definition policy. Other records are preserved;
        # no alternate-definition search in this initial implementation.
        active.append(name)
        try:
            witness = expand(choices[0])
        finally:
            active.pop()
        if not expression_columns(witness) <= ref_names:
            raise ValueError(f'Non-reference dependencies remain for {name}')
        memo[name] = witness
        origins[name] = source
        return witness

    witnesses, sources, unresolved = {}, {}, {}
    for name in sorted(cand_names):
        try:
            witnesses[name] = resolve(name)
            sources[name] = origins[name]
        except ValueError as error:
            unresolved[name] = str(error)
    return MappingResult(ref_names, cand_names, witnesses, sources, unresolved, records)
