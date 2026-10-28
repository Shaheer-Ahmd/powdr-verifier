"""Run the check on every adjacent step pair of many blocks, as plain records.

One record per (block, step pair, direction). Records are JSON-friendly, so a
sweep can be saved once and displayed many times (``redesign report``).
"""

from __future__ import annotations

import subprocess
import time
from collections import Counter
from collections.abc import Callable, Iterable
from datetime import datetime
from pathlib import Path

from src.lens.loader import load, machine_of
from src.lens.resolve import ResolveError, group_dir, index_block, list_blocks
from src.paths import POWDR_DUMPS_DIR, VERIFIER_DIR

from .check import DIRECTIONS, check_step
from .circuit import Circuit, load_substitutions
from .mapping import MissingDefinition
from .sweep import Report

FORMAT = 2  # 2: obligations have a kind (constraint / bus)
EXAMPLES_PER_REASON = 2  # undecided obligations kept per step and reason


def run_sweep(
    group: str,
    blocks: Iterable[str] = (),
    directions=DIRECTIONS,
    use_ranges: bool = True,
    root: Path | None = None,
    on_block: Callable[[str, list[dict]], None] | None = None,
    use_hints: bool = True,
    use_constants: bool = True,
    use_one_hot: bool = True,
    passes: Iterable[str] = (),
    on_pair: Callable[[list[dict], list[Report | None], Circuit, Circuit], None]
    | None = None,
) -> dict:
    """Sweep the blocks (default: all) and return ``{"meta": ..., "steps": [...]}``.

    ``passes`` keeps only the step pairs whose After dump comes from one of
    these passes ("final" for the last dump). ``on_pair`` gets each pair's
    records, the reports behind them (None for a mapping error) and the two
    circuits.
    """
    directory = group_dir(group, root or POWDR_DUMPS_DIR)
    blocks = list(blocks) or list_blocks(directory)
    passes = set(passes)
    start = time.monotonic()
    indexed = {block: index_block(directory, block) for block in blocks}
    if passes:
        seen = {e.pass_name or "final" for es in indexed.values() for e in es[1:]}
        if passes - seen:
            missing = ", ".join(sorted(passes - seen))
            raise ResolveError(
                f"no step from pass {missing} (have: {', '.join(sorted(seen))})"
            )
    steps: list[dict] = []
    for block, entries in indexed.items():
        subs = load_substitutions(group, block, root)
        circuits: dict[int, Circuit] = {}  # loaded on first use
        records = []
        for i in range(len(entries) - 1):
            e0, e1 = entries[i], entries[i + 1]
            base = {
                "block": block,
                "pair": f"{e0.nnn:03d}->{e1.nnn:03d}",
                "before": e0.label,
                "after": e1.label,
                "pass": e1.pass_name or "final",
            }
            if passes and base["pass"] not in passes:
                continue
            for j in (i, i + 1):
                if j not in circuits:
                    e = entries[j]
                    circuits[j] = Circuit.from_machine(e.label, machine_of(load(e.path)))
            before, after = circuits[i], circuits[i + 1]
            try:
                reports = check_step(
                    before,
                    after,
                    subs,
                    directions,
                    use_ranges,
                    use_hints,
                    use_constants,
                    use_one_hot,
                )
            except MissingDefinition as exc:
                # Only completeness raises; still record soundness separately.
                reports = [None]
                if "soundness" in directions:
                    reports += check_step(
                        before,
                        after,
                        subs,
                        ("soundness",),
                        use_ranges,
                        use_hints,
                        use_constants,
                        use_one_hot,
                    )
                pair = [_error(base, "completeness", str(exc))]
                pair += [_record(base, r) for r in reports[1:]]
            else:
                pair = [_record(base, r) for r in reports]
            records += pair
            if on_pair:
                on_pair(pair, reports, before, after)
        steps += records
        if on_block:
            on_block(block, records)
    meta = {
        "format": FORMAT,
        "group": group,
        "blocks": len(blocks),
        "passes": sorted(passes),
        "directions": list(directions),
        "byte_ranges": use_ranges,
        "hints": use_hints,
        "constants": use_constants,
        "one_hot": use_one_hot,
        "seconds": round(time.monotonic() - start, 1),
        "created": datetime.now().astimezone().isoformat(timespec="seconds"),
        "verifier_commit": _commit(),
    }
    return {"meta": meta, "steps": steps}


def _record(base: dict, r: Report) -> dict:
    examples, seen = [], Counter()
    for o in r.obligations:
        if o.rung == "undecided" and seen[(o.kind, o.reason)] < EXAMPLES_PER_REASON:
            seen[(o.kind, o.reason)] += 1
            examples.append(
                {
                    "kind": o.kind,
                    "reason": o.reason,
                    "obligation": o.name,
                    "detail": o.detail[:300],
                }
            )
    return {
        **base,
        "direction": r.direction,
        "verified": r.verified,
        "error": None,
        "obligations": len(r.obligations),
        "obligations_by_kind": dict(Counter(o.kind for o in r.obligations)),
        # "kind|rung|subcategory" -> count; JSON keys must be strings.
        "categories": {"|".join(k): n for k, n in r.categories().items()},
        "cached": sum(o.cached for o in r.obligations),
        "cached_by_kind": dict(Counter(o.kind for o in r.obligations if o.cached)),
        "premises_expanded": r.premises_expanded,
        "premises_split": r.premises_split,
        "hints_accepted": r.hints_accepted,
        "hints_agreed": r.hints_agreed,
        "hints_rejected": r.hints_rejected,
        "constants_solved": r.constants_solved,
        "pinned": r.pinned,
        "witnesses": [[cols, w] for cols, w in r.mapping.witnesses],
        "unmapped": sorted(r.mapping.unmapped),
        "unmapped_reasons": dict(sorted(r.mapping.unmapped_reason.items())),
        "examples": examples,
    }


def _error(base: dict, direction: str, msg: str) -> dict:
    return {
        **base,
        "direction": direction,
        "verified": False,
        "error": msg,
        "obligations": 0,
        "obligations_by_kind": {},
        "categories": {},
        "cached": 0,
        "cached_by_kind": {},
        "premises_expanded": 0,
        "premises_split": 0,
        "hints_accepted": 0,
        "hints_agreed": 0,
        "hints_rejected": 0,
        "constants_solved": 0,
        "pinned": 0,
        "witnesses": [],
        "unmapped": [],
        "unmapped_reasons": {},
        "examples": [],
    }


def _commit() -> str | None:
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=VERIFIER_DIR,
            capture_output=True,
            text=True,
            check=True,
        )
        dirty = subprocess.run(
            ["git", "status", "--porcelain", "--", "src"],
            cwd=VERIFIER_DIR,
            capture_output=True,
            text=True,
            check=False,
        ).stdout.strip()
        return out.stdout.strip() + ("+dirty" if dirty else "")
    except (OSError, subprocess.CalledProcessError):
        return None
