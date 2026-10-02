"""M3 polynomial discharge, negative controls, and evidence replay. No SMT."""
from copy import deepcopy
import json

import pytest

from src.verify.cheap_obligations import cheap_sweep
from src.verify.witness_mapping import build_mapping
from src.verify.polynomial_matching import (
    RecipePolynomials, check_polynomial_proof, check_polynomial_proofs, discharge_polynomial_matches,
)
from src.verify import m3_sweep


def circuit(cs=(), buses=(), derived=()):
    return dict(constraints=list(cs), bus_interactions=list(buses), derived_columns=list(derived))


def run(ref, cand):
    mapping = build_mapping(ref, cand)
    assert mapping.total
    before = deepcopy((ref, cand, mapping.witnesses))
    base = cheap_sweep(ref, cand, mapping)
    goals = cheap_sweep(ref, cand, mapping, polynomial_matching=True)
    assert (ref, cand, mapping.witnesses) == before
    for goal in goals:
        if goal.proof:
            assert check_polynomial_proof(ref, cand, mapping, json.loads(json.dumps(goal.proof)))
    return mapping, base, goals


EXPANDED = [['x@0', '*', 'y@1'], '+', ['x@0', '*', 'z@2']]
FACTORED = ['x@0', '*', ['y@1', '+', 'z@2']]


def test_exact_expansion_and_no_candidate_premises():
    ref = circuit([EXPANDED])
    cand = circuit([FACTORED, [FACTORED, '+', 1]])
    _, base, goals = run(ref, cand)
    assert [g.status for g in base] == ['residual', 'residual']
    assert [g.reason for g in goals] == ['polynomial-reference-match', 'requires-proof']
    assert goals[0].proof['reference_index'] == 0
    # Duplicate unsupported goals may not justify each other.
    _, _, goals = run(ref, circuit([[FACTORED, '+', 1], [FACTORED, '+', 1]]))
    assert all(g.status == 'residual' for g in goals)


def test_zero_and_scalar_equations():
    ref = circuit([EXPANDED])
    cand = circuit([[FACTORED, '-', EXPANDED], [-2, '*', FACTORED]])
    mapping, _, goals = run(ref, cand)
    assert [g.reason for g in goals] == ['polynomial-zero', 'nonzero-scale-reference-match']
    assert goals[1].proof['scale'] == 2013265919
    assert check_polynomial_proofs(ref, cand, mapping, [g.proof for g in goals])
    broken = [goals[0].proof, goals[1].proof | {'scale': 1}]
    with pytest.raises(ValueError):
        check_polynomial_proofs(ref, cand, mapping, broken)


def test_bus_matching_requires_id_payload_and_exact_multiplicity():
    bus = dict(id=3, mult=1, args=[EXPANDED, 8])
    rows = [dict(bus, args=[FACTORED, 8]),
            dict(bus, mult=2, args=[FACTORED, 8]),
            dict(bus, args=[[2, '*', FACTORED], 8]),
            dict(bus, id=7, args=[FACTORED, 8]),
            dict(bus, mult=[FACTORED, '-', EXPANDED], args=[FACTORED, 8])]
    _, _, goals = run(circuit(buses=[bus]), circuit(buses=rows))
    assert [g.reason for g in goals] == ['stateless-polynomial-reference-match',
                                       'requires-proof', 'requires-proof', 'requires-proof',
                                       'stateless-polynomial-inactive']


def test_recipes_constant_folding_and_symbolic_quotient_not_cancelled():
    ref = circuit(['x@0', 'd@1'])  # Both columns live; polynomial matching uses one premise, not combinations.
    definition = [[True, 'f@2', {'QuotientOrZero': ['x@0', 'd@1']}]]
    _, _, goals = run(ref, circuit([[['f@2', '*', 'd@1'], '-', 'x@0']], derived=definition))
    assert goals[0].status == 'residual'
    poly = RecipePolynomials({'x@0', 'd@1', 'classification_recipe@0'})
    recipe = {'QuotientOrZero': ['x@0', 'd@1']}
    assert poly.key(recipe) != poly.key('classification_recipe@0')
    assert poly.key([recipe, '-', recipe]) == ()
    assert poly.key({'QuotientOrZero': ['x@0', 0]}) == ()
    assert poly.key({'QuotientOrZero': ['x@0', 1]}) == poly.key('x@0')
    assert poly.key({'IfEqZero': [0, {'Constant': 3}, {'Constant': 4}]}) == poly.key(3)
    assert poly.key({'QuotientOrZero': ['x@0', 'd@1']}) != poly.key({'QuotientOrZero': ['d@1', 'x@0']})


def test_budget_exhaustion_preserves_residuals():
    ref, cand = circuit([EXPANDED]), circuit([FACTORED])
    mapping = build_mapping(ref, cand)
    base = cheap_sweep(ref, cand, mapping)
    limited = discharge_polynomial_matches(ref, mapping, base, max_terms=1)
    assert limited == base and limited[0].status == 'residual'


def test_stateful_and_definition_obligations_are_not_discharged():
    ref, cand = circuit([EXPANDED]), circuit([EXPANDED], [dict(id=1, mult=1, args=['x@0'])])
    mapping = build_mapping(ref, cand)
    goals = cheap_sweep(ref, cand, mapping, polynomial_matching=True,
                        definition_goals=[(99, FACTORED, FACTORED)])
    assert [(g.kind, g.status) for g in goals] == [('algebraic', 'discharged'),
                                                 ('derived-definition', 'residual')]


def test_constant_recipe_witness_integration_and_evidence():
    ref = circuit(['x@0'])
    cand = circuit(['f@1'], derived=[[True, 'f@1', {'QuotientOrZero': ['x@0', 1]}]])
    _, base, goals = run(ref, cand)
    assert base[0].status == 'residual'
    assert goals[0].reason == 'polynomial-reference-match'


def test_disabled_mapping_does_not_change_library_default():
    ref, cand = circuit([EXPANDED]), circuit([FACTORED])
    mapping = build_mapping(ref, cand)
    goals = cheap_sweep(ref, cand, mapping)
    assert goals[0].status == 'residual' and goals[0].proof is None


def test_opaque_symbol_allocator_is_local_to_each_direction():
    first = RecipePolynomials({'classification_recipe@0', 'x@0'})
    second = RecipePolynomials({'x@0'})
    recipe = {'QuotientOrZero': [1, 'x@0']}
    assert first.key(recipe) != first.key('classification_recipe@0')
    assert first.key(recipe) != second.key(recipe)
    assert second.key([recipe, '-', recipe]) == ()


@pytest.mark.parametrize('change', [dict(reference_index=99), dict(index=-1), dict(scale=0),
                                   dict(rule='polynomial-zero'), dict(field=7),
                                   dict(assumptions=['assume anything']), dict(kind='stateful')])
def test_tampered_proof_rejected(change):
    ref, cand = circuit([EXPANDED]), circuit([[-2, '*', FACTORED]])
    mapping, _, goals = run(ref, cand)
    with pytest.raises(ValueError):
        check_polynomial_proof(ref, cand, mapping, goals[0].proof | change)


def test_changed_bus_evidence_and_inputs_rejected():
    bus = dict(id=3, mult=1, args=[EXPANDED, 8])
    ref, cand = circuit(buses=[bus]), circuit(buses=[dict(bus, args=[FACTORED, 8])])
    mapping, _, goals = run(ref, cand)
    changed = deepcopy(cand)
    changed['bus_interactions'][0]['mult'] = 2
    with pytest.raises(ValueError):
        check_polynomial_proof(ref, changed, mapping, goals[0].proof)
    with pytest.raises(ValueError):
        check_polynomial_proof(ref, cand, mapping, goals[0].proof | {'reference_index': -1})


@pytest.mark.parametrize('enabled', [True, False])
def test_cli_default_optout_persistence_and_replay(tmp_path, enabled):
    root = tmp_path/'guest-demo'
    root.mkdir()
    ref, cand = circuit([EXPANDED]), circuit([FACTORED])
    for step, data in enumerate((ref, cand)):
        (root/f'apc_candidate_12_{step:03d}_test.json').write_text(json.dumps(data))
    out = tmp_path/'report'
    args = [] if enabled else ['--no-polynomial-matching']
    assert m3_sweep.main(['demo', '--root', str(tmp_path), '--output', str(out), *args]) == 0
    summary = json.loads((out/'summary.json').read_text())
    assert summary['residual_totals']['total'] == (0 if enabled else 2)
    assert summary['polynomial_discharged'] == (2 if enabled else 0)
    assert summary['zero_check_discharged'] == 0
    manifest = json.loads((out/'manifest.json').read_text())
    assert manifest['polynomial_matching_enabled'] == enabled
    assert 'src/verify/polynomial_matching.py' in manifest['sources_sha256']
    for row in map(json.loads, (out/'results.jsonl').read_text().splitlines()):
        a, b = (ref, cand) if row['direction'] == 'completeness' else (cand, ref)
        mapping = build_mapping(a, b)
        for proof in row['polynomial_proofs']:
            assert row['mapping']['witnesses'] == mapping.witnesses
            assert check_polynomial_proof(a, b, mapping, proof)
