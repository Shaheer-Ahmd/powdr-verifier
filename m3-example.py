"""Minimal M2–M3 API example: mapping and cheap checks, not equivalence.

Run from verifier/: uv run python m3-example.py
Requires the Keccak 2106332 snapshots; no solver checks are performed.
Enables the zero checker without assuming reference memory payloads are bytes.
Use zero-check.py --reference-recv-bytes for the conditional closed example.
"""

from pathlib import Path

from src.lens.loader import load
from src.verify.cheap_obligations import cheap_sweep
from src.verify.collapsed_witness import add_collapsed_witnesses
from src.verify.witness_mapping import build_mapping


def main():
    root = Path(__file__).resolve().parent / "powdr-dumps/guest-keccak"
    before = load(root / "apc_candidate_2106332_008_trivial_simp.json")
    after = load(root / "apc_candidate_2106332_009_rule_based.json")
    subs = load(root / "apc_candidate_2106332_substitutions.json")

    for direction, ref, cand in [
        ("completeness", before, after),
        ("soundness", after, before),
    ]:
        mapping, _proposals = add_collapsed_witnesses(
            ref, cand, build_mapping(ref, cand, subs)
        )
        if not mapping.total:
            raise ValueError(f"{direction}: incomplete mapping: {mapping.unresolved}")
        goals = cheap_sweep(
            ref,
            cand,
            mapping,
            zero_check_direction=direction,
            reference_recv_bytes=False,
        )
        residuals = [(g.kind, g.index) for g in goals if g.status == "residual"]
        print(direction, residuals)
        assumptions = {
            (b["rule"], b["bus"])
            for g in goals
            if g.proof
            for b in g.proof["claim"]["assumptions"]
        }
        for contract, row in sorted(assumptions):
            print(
                f"  ASSUMED {contract}: reference memory row {row} payloads are bytes"
            )

    print(
        "No SMT. No receive-byte contract is assumed; remaining obligations need proof. "
        "IO and general definition audit are unchecked."
    )


if __name__ == "__main__":
    main()
