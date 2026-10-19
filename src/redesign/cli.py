"""``redesign check keccak 2106332 008 009`` - per-constraint check of one step.

``redesign sweep keccak`` runs every adjacent step of every block (or the given
blocks) and prints a report; ``redesign report FILE`` re-displays a saved sweep."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from rich.console import Console

from src.lens.resolve import ResolveError

from .check import DIRECTIONS, check
from .corpus import run_sweep
from .display import render
from .mapping import MissingDefinition
from .sweep import Report


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="redesign", description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    c = sub.add_parser("check", help="map and sweep one Before -> After step")
    c.add_argument("group", help="dump group, e.g. keccak")
    c.add_argument("block", help="candidate id, e.g. 2106332")
    c.add_argument("step_from", help="Before step (NNN or pass name)")
    c.add_argument("step_to", help="After step (NNN or pass name)")
    c.add_argument("--direction", choices=("both",) + DIRECTIONS, default="both")
    c.add_argument(
        "--no-ranges", action="store_true", help="drop the byte-range premises"
    )
    c.add_argument(
        "--no-hints", action="store_true", help="ignore powdr's substitutions as hints"
    )
    c.add_argument(
        "--no-constants",
        action="store_true",
        help="do not solve premises that pin a variable to a constant",
    )
    c.add_argument(
        "--no-one-hot",
        action="store_true",
        help="leave out PolySolver's rule O (one-hot flags)",
    )
    c.add_argument("--root", type=Path, help="dump root (default: powdr-dumps)")
    c.add_argument("--json", action="store_true", help="machine-readable output")
    c.add_argument("-v", "--verbose", action="store_true", help="list every obligation")

    s = sub.add_parser("sweep", help="check every adjacent step across blocks")
    s.add_argument("group", help="dump group, e.g. keccak")
    s.add_argument("blocks", nargs="*", help="candidate ids (default: all)")
    s.add_argument("--direction", choices=("both",) + DIRECTIONS, default="both")
    s.add_argument(
        "--no-ranges", action="store_true", help="drop the byte-range premises"
    )
    s.add_argument(
        "--no-hints", action="store_true", help="ignore powdr's substitutions as hints"
    )
    s.add_argument(
        "--no-constants",
        action="store_true",
        help="do not solve premises that pin a variable to a constant",
    )
    s.add_argument(
        "--no-one-hot",
        action="store_true",
        help="leave out PolySolver's rule O (one-hot flags)",
    )
    s.add_argument("--root", type=Path, help="dump root (default: powdr-dumps)")
    s.add_argument("--save", type=Path, help="also write the results as JSON")
    s.add_argument("--json", action="store_true", help="one JSON line per step")
    _add_display_args(s)

    r = sub.add_parser("report", help="display a sweep saved with --save")
    r.add_argument("file", type=Path)
    _add_display_args(r)
    return p


def _add_display_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("--no-legend", action="store_true", help="hide 'How to read this'")
    p.add_argument("--top", type=int, default=15, help="recurring problem rows shown")
    p.add_argument("--by-block", action="store_true", help="add a per-block table")
    p.add_argument(
        "--examples",
        type=int,
        default=0,
        metavar="N",
        help="show N example undecided obligations per reason",
    )


def _display(args, data: dict) -> None:
    render(
        data,
        legend=not args.no_legend,
        top=args.top,
        by_block=args.by_block,
        examples=args.examples,
    )


def _as_dict(r: Report) -> dict:
    return {
        "direction": r.direction,
        "verified": r.verified,
        "counts": {kind: dict(r.counts(kind)) for kind in ("constraint", "bus")},
        "premises_expanded": r.premises_expanded,
        "premises_split": r.premises_split,
        "hints_accepted": r.hints_accepted,
        "hints_rejected": r.hints_rejected,
        "constants_solved": r.constants_solved,
        "witnesses": [
            {"columns": cols, "witness": w} for cols, w in r.mapping.witnesses
        ],
        "unmapped": sorted(r.mapping.unmapped),
        "unmapped_reasons": dict(sorted(r.mapping.unmapped_reason.items())),
        "obligations": [vars(o) for o in r.obligations],
    }


def _print(r: Report, verbose: bool) -> None:
    status = "verified" if r.verified else "NOT verified"
    # One group of rung counts per kind: constraints, then stateless lookups.
    counts = "; ".join(
        f"{label}: " + ", ".join(f"{k} {v}" for k, v in sorted(c.items()))
        for label, c in (
            ("constraints", r.counts("constraint")),
            ("bus", r.counts("bus")),
        )
        if c
    )
    print(
        f"{r.direction}: {status}  ({counts}; {r.premises_expanded} premises expanded, {r.premises_split} split"
        f"; hints {r.hints_accepted} used, {r.hints_rejected} rejected"
        f"; {r.constants_solved} constants solved)"
    )
    for cols, w in r.mapping.witnesses:
        print(f"  witness  {', '.join(cols)} := {json.dumps(w)}")
    # Unmapped columns, grouped by why: a failed witness search or lookup-only.
    by_reason: dict[str, list[str]] = {}
    for col in sorted(r.mapping.unmapped):
        why = r.mapping.unmapped_reason.get(col, "witness search failed")
        by_reason.setdefault(why, []).append(col)
    for why, cols in by_reason.items():
        print(f"  unmapped ({why}) {', '.join(cols)}")
    for o in r.obligations:
        if verbose or o.rung == "undecided":
            print(f"  {o.rung:<12} {o.name}  {o.detail}")


def _sweep(args, directions) -> int:
    err = Console(stderr=True)
    with err.status("sweeping...") as status:

        def progress(block: str, records: list[dict]) -> None:
            status.update(f"swept {block}")
            if args.json:
                for rec in records:
                    print(json.dumps(rec))

        data = run_sweep(
            args.group,
            args.blocks,
            directions,
            not args.no_ranges,
            args.root,
            on_block=progress,
            use_hints=not args.no_hints,
            use_constants=not args.no_constants,
            use_one_hot=not args.no_one_hot,
        )
    if args.save:
        args.save.write_text(json.dumps(data))
        err.print(f"saved {len(data['steps'])} records to {args.save}")
    if not args.json:
        _display(args, data)
    return 0 if all(s["verified"] for s in data["steps"]) else 1


def _report(args) -> int:
    data = json.loads(args.file.read_text())
    _display(args, data)
    return 0


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    if args.command == "report":
        return _report(args)
    directions = DIRECTIONS if args.direction == "both" else (args.direction,)
    if args.command == "sweep":
        try:
            return _sweep(args, directions)
        except (ResolveError, FileNotFoundError) as exc:
            print(f"redesign: {type(exc).__name__}: {exc}", file=sys.stderr)
            return 2
    try:
        reports = check(
            args.group,
            args.block,
            args.step_from,
            args.step_to,
            directions,
            not args.no_ranges,
            args.root,
            not args.no_hints,
            not args.no_constants,
            not args.no_one_hot,
        )
    except (ResolveError, FileNotFoundError, MissingDefinition) as exc:
        print(f"redesign: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps([_as_dict(r) for r in reports], indent=2))
    else:
        for r in reports:
            _print(r, args.verbose)
    return 0 if all(r.verified for r in reports) else 1


if __name__ == "__main__":
    sys.exit(main())
