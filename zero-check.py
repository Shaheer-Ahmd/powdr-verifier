"""Run the solver-free gadget checker. No whole-circuit equivalence verdict."""

import argparse
import json
from pathlib import Path

from src.lens.loader import load
from src.verify.zero_check import syntactic_sweep


def main():
    root = Path(__file__).resolve().parent / "powdr-dumps/guest-keccak"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--before",
        type=Path,
        default=root / "apc_candidate_2106332_008_trivial_simp.json",
    )
    parser.add_argument(
        "--after", type=Path, default=root / "apc_candidate_2106332_009_rule_based.json"
    )
    parser.add_argument(
        "--substitutions",
        type=Path,
        help="Optional substitution metadata; not needed for the default gadget",
    )
    parser.add_argument(
        "--reference-recv-bytes",
        action="store_true",
        help="Explicitly grant byte-valued payloads for constant-active reference memory receives",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Write full JSON evidence to a NEW file (never overwrite)",
    )
    args = parser.parse_args()
    if args.output and args.output.exists():
        parser.error(f"Output already exists: {args.output}")
    before, after = load(args.before), load(args.after)
    substitutions = load(args.substitutions) if args.substitutions else []
    results = {}
    for direction in ("completeness", "soundness"):
        result = syntactic_sweep(
            before,
            after,
            direction,
            substitutions,
            allow_recv_bytes=args.reference_recv_bytes,
        )
        results[direction] = result
        initial, residual = result["initial_residuals"], result["residuals"]
        print(
            f"{direction}: initial={len(initial) if initial is not None else 'unknown'}, "
            f"residual={len(residual) if residual is not None else 'unknown'}, status={result['status']}"
        )
        for bound in result.get("assumptions", []):
            print(
                f"  ASSUMED {bound['rule']}: reference bus[{bound['bus']}] "
                f"arg[{bound['argument']}] bounds {bound['column']} <= {bound['upper']}"
            )
        if residual:
            print(f"  Remaining: {residual}")
    report = {
        "schema": "zero-check-report-v1",
        "paths": {
            "before": str(args.before.resolve()),
            "after": str(args.after.resolve()),
            "substitutions": str(args.substitutions.resolve())
            if args.substitutions
            else None,
        },
        "results": results,
    }
    if args.output:
        with args.output.open("x") as stream:
            json.dump(report, stream, indent=2)
            stream.write("\n")
        print(f"Evidence: {args.output}")
    print(
        "No SMT solving. Local obligations only; IO and general derived-definition audit are unchecked."
    )
    return 0 if all(r["residuals"] == [] for r in results.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
