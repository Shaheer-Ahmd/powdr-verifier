"""Solver-free gadget regression and certificate rejection tests."""

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import subprocess
import sys

import pytest

from src.lens.loader import load
from src.verify.cheap_obligations import cheap_sweep
from src.verify.collapsed_witness import add_collapsed_witnesses
from src.verify.witness_mapping import build_mapping
from src.verify.zero_check import (
    CONTRACT,
    FIELD_PRIME as P,
    InvalidCertificate,
    _sum,
    _zero,
    _weighted,
    check_certificate,
    fingerprint,
    propose_certificates,
    syntactic_sweep,
)


def fixture_pair(*, ranges=True, recv=False, n=4, bits=8):
    limbs = [f"limb@{i}" for i in range(n)]
    markers = [f"aux@{i + n}" for i in range(n)]
    cmp, f = f"flag@{2 * n}", f"quotient@{2 * n + 1}"
    buses = []
    if ranges:
        buses += [dict(id=3, mult=1, args=[a, bits]) for a in limbs]
    if recv:
        assert n == 4
        buses.append(dict(id=1, mult=-1, args=[1, 52, *limbs, 0]))
    before = dict(
        constraints=[_zero(cmp, a) for a in limbs] + [_weighted(limbs, markers, cmp)],
        bus_interactions=deepcopy(buses),
        derived_columns=[],
    )
    after = dict(
        constraints=[_zero(cmp, _sum(limbs)), [[f, "*", _sum(limbs)], "-", cmp]],
        bus_interactions=deepcopy(buses),
        derived_columns=[[True, f, {"QuotientOrZero": [cmp, _sum(limbs)]}]],
    )
    return before, after


def mapping_for(before, after, direction):
    ref, cand = (before, after) if direction == "completeness" else (after, before)
    return add_collapsed_witnesses(ref, cand, build_mapping(ref, cand))[0]


@pytest.mark.parametrize("direction", ["completeness", "soundness"])
def test_range_supported_no_contract(direction):
    before, after = fixture_pair()
    report = syntactic_sweep(before, after, direction)
    assert report["status"] == "local-closed"
    assert report["residuals"] == []
    assert not report["assumptions"]
    assert len(report["obligations"]) == (6 if direction == "completeness" else 9)
    assert report["certificates"][0]["checked"]["no_cancellation"]
    assert report["certificates"][0]["checked"]["upper_sum"] == 1020


@pytest.mark.parametrize("direction,remaining", [("completeness", 1), ("soundness", 4)])
def test_missing_bounds_leave_residuals(direction, remaining):
    before, after = fixture_pair(ranges=False)
    report = syntactic_sweep(before, after, direction)
    assert len(report["residuals"]) == remaining
    assert report["status"] == "residual"
    assert len(report["proof_uses"]) == 1


@pytest.mark.parametrize("direction", ["completeness", "soundness"])
def test_explicit_receive_contract_and_no_mutation(direction):
    before, after = fixture_pair(ranges=False, recv=True)
    saved = deepcopy((before, after))
    without = syntactic_sweep(before, after, direction)
    assert without["residuals"]
    report = syntactic_sweep(before, after, direction, allow_recv_bytes=True)
    assert report["status"] == "conditional-local-closed"
    assert report["residuals"] == []
    assert len(report["assumptions"]) == 4
    assert all(b["rule"] == CONTRACT for b in report["assumptions"])
    assert (before, after) == saved
    cert = report["certificates"][0]["certificate"]
    with pytest.raises(InvalidCertificate, match="not authorized"):
        check_certificate(before, after, mapping_for(before, after, direction), cert)


@pytest.mark.parametrize("mult", [0, "enable@100"])
@pytest.mark.parametrize("recv", [False, True])
def test_inactive_or_symbolic_guards_do_not_supply_bounds(mult, recv):
    before, after = fixture_pair(ranges=not recv, recv=recv)
    for data in (before, after):
        for bus in data["bus_interactions"]:
            bus["mult"] = mult
    for direction in ("completeness", "soundness"):
        report = syntactic_sweep(before, after, direction, allow_recv_bytes=True)
        assert report["residuals"]


def test_upper_sum_wraparound_not_accepted():
    before, after = fixture_pair(n=64, bits=25)
    report = syntactic_sweep(before, after, "completeness")
    checked = report["certificates"][0]["checked"]
    assert checked["upper_sum"] >= P and not checked["no_cancellation"]
    assert report["residuals"] == [("algebraic", 1)]


@pytest.mark.parametrize(
    "mutation", ["constant", "sign", "numerator", "denominator", "multiple-definitions"]
)
def test_mutants_not_closed(mutation):
    before, after = fixture_pair()
    if mutation == "constant":
        after["constraints"][1] = [after["constraints"][1], "+", 1]
    elif mutation == "sign":
        after["constraints"][1][1] = "+"
    elif mutation == "numerator":
        after["derived_columns"][0][2]["QuotientOrZero"][0] = 0
    elif mutation == "denominator":
        after["derived_columns"][0][2]["QuotientOrZero"][1] = "limb@0"
    else:
        extra = deepcopy(after["derived_columns"][0])
        extra[2]["QuotientOrZero"][0] = 0
        after["derived_columns"].append(extra)
    assert syntactic_sweep(before, after, "completeness")["residuals"]


def test_additional_marker_use_not_silently_dropped():
    before, after = fixture_pair()
    before["constraints"].append(["aux@4", "-", 1])
    report = syntactic_sweep(before, after, "soundness")
    # Existing mapper may decline the mapping; either way, never local-closed.
    assert report["status"] in ("residual", "unmapped")


def test_extra_stateless_and_algebraic_obligations_are_preserved():
    before, after = fixture_pair()
    after["constraints"].append(1)
    after["bus_interactions"].append(dict(id=3, mult=1, args=["limb@0", 1]))
    report = syntactic_sweep(before, after, "completeness")
    assert report["residuals"] == [("algebraic", 2), ("stateless", 4)]


@pytest.mark.parametrize("direction", ["completeness", "soundness"])
def test_renaming_reordering_and_negative_residue(direction):
    before, after = fixture_pair()

    def rewrite(node):
        if isinstance(node, str) and "@" in node:
            return "renamed_" + node
        if isinstance(node, list):
            result = [rewrite(x) for x in node]
            if len(result) == 3 and result[1] in ("+", "*"):
                result = [result[2], result[1], result[0]]
            if len(result) == 3 and result[1] == "-":
                result = [result[0], "+", [P - 1, "*", result[2]]]
            return result
        if isinstance(node, dict):
            return {k: rewrite(v) for k, v in node.items()}
        return node

    before, after = rewrite(before), rewrite(after)
    before["constraints"].reverse()
    after["constraints"].reverse()
    assert syntactic_sweep(before, after, direction)["residuals"] == []


@pytest.mark.parametrize(
    "field,value",
    [
        ("field", 7),
        ("old_weighted", 0),
        ("new_weighted", 0),
        ("old_zero", [0, 0, 0, 0]),
        ("before", "fake"),
        ("mapping", "fake"),
        ("markers", ["aux@4"] * 4),
        ("definition", -1),
        ("new_zero", True),
    ],
)
def test_tampered_certificate_rejected(field, value):
    before, after = fixture_pair()
    mapping = mapping_for(before, after, "completeness")
    cert = propose_certificates(before, after, mapping, "completeness")[0]
    cert[field] = value
    with pytest.raises(InvalidCertificate):
        check_certificate(before, after, mapping, cert)


@pytest.mark.parametrize(
    "field,value",
    [
        ("upper", 0),
        ("bus", 3),
        ("argument", 1),
        ("column", "other@99"),
        ("assumption", CONTRACT),
    ],
)
def test_tampered_bound_rejected(field, value):
    before, after = fixture_pair()
    mapping = mapping_for(before, after, "completeness")
    cert = propose_certificates(before, after, mapping, "completeness")[0]
    cert["bounds"][0][field] = value
    with pytest.raises(InvalidCertificate):
        check_certificate(before, after, mapping, cert)


@pytest.mark.parametrize("direction", ["completeness", "soundness"])
def test_mapping_change_rejected_even_with_updated_hash(direction):
    before, after = fixture_pair()
    mapping = mapping_for(before, after, direction)
    cert = propose_certificates(before, after, mapping, direction)[0]
    target = "quotient@9" if direction == "completeness" else "aux@4"
    mapping.witnesses[target] = 0
    cert["mapping"] = fingerprint(mapping.witnesses)
    with pytest.raises(InvalidCertificate):
        check_certificate(before, after, mapping, cert)


def test_new_input_equations_rechecked_even_with_updated_hash():
    before, after = fixture_pair()
    mapping = mapping_for(before, after, "completeness")
    cert = propose_certificates(before, after, mapping, "completeness")[0]
    before["constraints"][-1] = [before["constraints"][-1], "+", 1]
    cert["before"] = fingerprint(before)
    with pytest.raises(InvalidCertificate, match="Equation mismatch"):
        check_certificate(before, after, mapping, cert)


@pytest.mark.parametrize("p", [3, 5, 7])
def test_theorem_schemas_exhaustively_in_small_fields(p):
    # Independent arithmetic enumeration, not SMT and not a general formal proof.
    upper = (p - 1) // 2
    for a, b, c in product(range(upper + 1), range(upper + 1), range(p)):
        s = (a + b) % p
        q = c * pow(s, -1, p) % p if s else 0
        for u, v in product(range(p), repeat=2):
            before = (
                (1 - c) * a % p == 0
                and (1 - c) * b % p == 0
                and (a * u + b * v - c) % p == 0
            )
            if before:
                assert (1 - c) * s % p == 0 and (q * s - c) % p == 0
        for f in range(p):
            if (1 - c) * s % p == 0 and (f * s - c) % p == 0:
                assert (1 - c) * a % p == 0 and (1 - c) * b % p == 0
                assert (a * f + b * f - c) % p == 0


def test_cancellation_counterexamples_without_bounds():
    a, b = 1, P - 1
    # Before with c=1, u=1, v=0; the QOZ witness cannot satisfy After.
    assert (a * 1 + b * 0 - 1) % P == 0
    assert (0 * ((a + b) % P) - 1) % P != 0
    # After with c=0, f=0; Before's individual zero constraints fail.
    assert ((1 - 0) * (a + b)) % P == 0
    assert (1 - 0) * a % P != 0


def test_candidate_bounds_cannot_justify_reference_obligations():
    before, after = fixture_pair()
    before["bus_interactions"] = []
    report = syntactic_sweep(before, after, "completeness")
    assert ("algebraic", 1) in report["residuals"]
    assert not report["certificates"][0]["checked"]["no_cancellation"]


def test_polynomial_budget_is_not_a_proof(monkeypatch):
    from src.verify import polynomial_normalization

    before, after = fixture_pair()
    mapping = mapping_for(before, after, "completeness")
    cert = propose_certificates(before, after, mapping, "completeness")[0]
    monkeypatch.setattr(polynomial_normalization, "MAX_TERMS", 1)
    with pytest.raises(polynomial_normalization.PolynomialBudgetExceeded):
        check_certificate(before, after, mapping, cert)


def test_bounds_from_send_payload_are_not_receive_bounds():
    before, after = fixture_pair(ranges=False, recv=True)
    for data in (before, after):
        data["bus_interactions"][0]["mult"] = 1
    report = syntactic_sweep(before, after, "completeness", allow_recv_bytes=True)
    assert report["residuals"] == [("algebraic", 1)]
    assert not report["assumptions"]


def test_real_gadget_acceptance_and_serialized_certificate_replay(tmp_path):
    root = Path(__file__).resolve().parents[1]
    dumps = root / "powdr-dumps/guest-keccak"
    bp = dumps / "apc_candidate_2106332_008_trivial_simp.json"
    ap = dumps / "apc_candidate_2106332_009_rule_based.json"
    if not bp.exists() or not ap.exists():
        pytest.skip("Keccak dumps not installed")
    before, after = load(bp), load(ap)
    for direction, indices in [
        ("completeness", [14, 15]),
        ("soundness", [9, 10, 11, 12, 13]),
    ]:
        report = syntactic_sweep(before, after, direction, allow_recv_bytes=True)
        assert report["initial_residuals"] == [("algebraic", i) for i in indices]
        assert (
            report["residuals"] == [] and report["status"] == "conditional-local-closed"
        )
        assert report["omitted_stateful"] == {"reference": 18, "candidate": 18}
        assert len(report["obligations"]) == (38 if direction == "completeness" else 41)
        assert {b["bus"] for b in report["assumptions"]} == {33}
        for entry in json.loads(json.dumps(report))["certificates"]:
            checked = check_certificate(
                before,
                after,
                mapping_for(before, after, direction),
                entry["certificate"],
                allow_recv_bytes=True,
            )
            assert checked == entry["checked"]
    output = tmp_path / "report.json"
    run = subprocess.run(
        [
            sys.executable,
            "zero-check.py",
            "--reference-recv-bytes",
            "--output",
            str(output),
        ],
        cwd=root,
        capture_output=True,
        text=True,
    )
    assert run.returncode == 0, run.stderr
    assert run.stdout.count("residual=0") == 2
    again = subprocess.run(
        [sys.executable, "zero-check.py", "--output", str(output)],
        cwd=root,
        capture_output=True,
        text=True,
    )
    assert again.returncode != 0 and "already exists" in again.stderr
    example = subprocess.run(
        [sys.executable, "m3-example.py"], cwd=root, capture_output=True, text=True
    )
    assert example.returncode == 0, example.stderr
    assert "completeness [('algebraic', 15)]" in example.stdout
    assert "soundness [('algebraic', 9), ('algebraic', 10), ('algebraic', 11), ('algebraic', 12)]" in example.stdout
    assert "ASSUMED reference-recv-bytes-v1" not in example.stdout


def test_no_solver_entrypoints(monkeypatch):
    # Fail if this path tries to import solver APIs or spawn a solver process.
    import builtins

    original = builtins.__import__

    def guarded(name, *args, **kwargs):
        if name == "z3" or name.startswith(
            ("z3.", "pysmt.solvers", "pysmt.shortcuts", "src.smt")
        ):
            raise AssertionError(f"Solver import attempted: {name}")
        return original(name, *args, **kwargs)

    def forbidden(*args, **kwargs):
        raise AssertionError("Subprocess attempted")

    monkeypatch.setattr(builtins, "__import__", guarded)
    monkeypatch.setattr(subprocess, "Popen", forbidden)
    before, after = fixture_pair()
    assert syntactic_sweep(before, after, "completeness")["residuals"] == []
    assert syntactic_sweep(before, after, "soundness")["residuals"] == []


@pytest.mark.parametrize(
    "direction,initial,without_bounds",
    [
        ("completeness", 2, 1),
        ("soundness", 5, 4),
    ],
)
def test_cheap_sweep_integrates_checker_with_explicit_contract(
    direction, initial, without_bounds
):
    before, after = fixture_pair(ranges=False, recv=True)
    ref, cand = (before, after) if direction == "completeness" else (after, before)
    mapping = mapping_for(before, after, direction)
    baseline = cheap_sweep(ref, cand, mapping)
    assert sum(o.status == "residual" for o in baseline) == initial
    unconditional = cheap_sweep(ref, cand, mapping, zero_check_direction=direction)
    assert sum(o.status == "residual" for o in unconditional) == without_bounds
    goals = cheap_sweep(
        ref, cand, mapping, zero_check_direction=direction, reference_recv_bytes=True
    )
    assert len(goals) == len(baseline)
    assert all(o.status == "discharged" for o in goals)
    assert sum(o.proof is not None for o in goals) == initial
    for o in goals:
        if o.proof:
            result = check_certificate(
                before, after, mapping, o.proof["certificate"], allow_recv_bytes=True
            )
            assert o.proof["claim"] in result["claims"]
    assert (
        sum(bool(o.proof and o.proof["claim"]["assumptions"]) for o in goals)
        == without_bounds
    )
    # Explicit definition audit goals are preserved, not mistaken for gadget equations.
    extra = cheap_sweep(
        ref,
        cand,
        mapping,
        zero_check_direction=direction,
        reference_recv_bytes=True,
        definition_goals=[(0, "audit", 1)],
    )
    assert extra[-1].kind == "derived-definition" and extra[-1].status == "residual"


def test_cheap_sweep_rejects_contract_without_direction():
    before, after = fixture_pair()
    mapping = mapping_for(before, after, "completeness")
    with pytest.raises(ValueError, match="requires zero_check_direction"):
        cheap_sweep(before, after, mapping, reference_recv_bytes=True)
    with pytest.raises(ValueError, match="Unknown zero-check direction"):
        cheap_sweep(before, after, mapping, zero_check_direction="invalid")


def test_cheap_sweep_uses_callers_mapping_without_rebuilding():
    before, after = fixture_pair()
    mapping = mapping_for(before, after, "soundness")
    mapping.witnesses["aux@4"] = 0
    goals = cheap_sweep(after, before, mapping, zero_check_direction="soundness")
    assert any(o.status == "residual" for o in goals)
    assert mapping.witnesses["aux@4"] == 0


def test_no_polynomial_scan_when_no_quotient_column_is_introduced(monkeypatch):
    from src.verify import zero_check

    _, after = fixture_pair()
    mapping = build_mapping(after, after)

    def forbidden(*args):
        raise AssertionError("Unnecessary polynomial scan")

    monkeypatch.setattr(zero_check, "_keys", forbidden)
    assert propose_certificates(after, after, mapping, "completeness") == []


def test_no_gadget_scan_when_no_algebraic_residuals(monkeypatch):
    from src.verify import zero_check

    _, after = fixture_pair()
    mapping = build_mapping(after, after)

    def forbidden(*args, **kwargs):
        raise AssertionError("Unnecessary gadget scan")

    monkeypatch.setattr(zero_check, "propose_certificates", forbidden)
    goals = cheap_sweep(after, after, mapping, zero_check_direction="completeness")
    assert all(g.status == "discharged" for g in goals)
