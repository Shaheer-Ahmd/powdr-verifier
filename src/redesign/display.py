"""Render sweep records (from ``corpus.run_sweep``) as readable terminal tables.

Sections: what the words mean, step outcomes, where the obligations went
(with subcategories), which passes leave work for SMT, recurring problem
steps across blocks, and the mapping. Every number is counted from the
records; nothing is estimated. Reads format 1 files (constraints only) too.
"""

from __future__ import annotations

from collections import Counter, defaultdict

from rich import box
from rich.console import Console
from rich.panel import Panel
from rich.table import Table
from rich.text import Text

from .sweep import REASONS

DIRS = ("completeness", "soundness")

KINDS = {
    "constraint": "algebraic constraints",
    "bus": "stateless bus interactions (lookups)",
}

# Display order and meaning of every (rung, subcategory) the sweep produces.
DISCHARGED_ROWS = [
    ("trivial", "", "c[w] is identically zero"),
    (
        "identical",
        "direct",
        "the pass kept it: same canonical form as a reference constraint",
    ),
    (
        "identical",
        "via mapping",
        "same canonical form once mapped columns are substituted",
    ),
    (
        "normalize",
        "direct",
        "a reference constraint times a nonzero constant (fully expanded)",
    ),
    (
        "normalize",
        "via mapping",
        "same, after substituting mapped columns (e.g. a witness)",
    ),
    (
        "nowrap-split",
        "direct",
        "split of a reference sum constraint, using byte ranges",
    ),
    ("nowrap-split", "via mapping", "same, after substituting mapped columns"),
    (
        "one-hot",
        "direct",
        "a flag is 0 or 1: boolean flags summing to 1, and selectors",
    ),
    ("one-hot", "via mapping", "same, after substituting mapped columns"),
]
RUNG_NOTE = {
    "trivial": "rung 1",
    "identical": "rung 2, lens canon_zero",
    "normalize": "PolySolver rule N",
    "nowrap-split": "PolySolver rule S",
    "one-hot": "PolySolver rule O",
}
# The same for stateless bus interactions.
BUS_ROWS = [
    ("trivial", "", "multiplicity is 0: the lookup asserts nothing"),
    ("identical", "direct", "the reference has the same lookup (bus, mult, args)"),
    ("identical", "via mapping", "same, once mapped columns are substituted"),
    ("evaluated", "direct", "constant arguments that form a table row"),
    ("evaluated", "via mapping", "same, once mapped columns are substituted"),
    ("congruence", "direct", "PolySolver proves mult and args equal to a reference lookup's"),
    ("congruence", "via mapping", "same, with mapped columns substituted"),
]
BUS_RUNG_NOTE = {
    "trivial": "rung 1, canon mult = 0",
    "identical": "rung 2, lens _bus_exact_key",
    "evaluated": "rung 3, table row (not PcLookup)",
    "congruence": "rung 4, PolySolver implies_equal",
}

LEGEND = """\
[b]Step pair[/b]  two consecutive dumps of one block: Before -> After, one optimizer pass.
[b]Direction[/b]  [b]completeness[/b]: every Before run maps to an After run, so each After
           constraint is checked against Before. [b]soundness[/b]: the reverse.
[b]Obligation[/b] one candidate constraint c, or one candidate stateless lookup, with
           candidate-only columns replaced by their mapping w. It must follow from
           the reference side's constraints, lookups and byte ranges.
[b]Discharged[/b] proved without SMT: by a canonical match, or (constraints only) PolySolver.
[b]Undecided[/b]  no rule applied. Not a bug: it is what later rungs (SMT, PolySolver for
           lookups) would get. A step is [b]discharged[/b] only if all its obligations are.
[b]Scope[/b]      constraints and stateless lookups. Stateful buses (memory, execution
           bridge) are not checked yet, so "discharged" is not "equivalent"."""


def _pct(n: int, total: int) -> str:
    return f"{100 * n / total:.1f}%" if total else "-"


def _cell(n: int, total: int) -> Text:
    if not n:
        return Text("-", style="dim")
    return Text(f"{n:,}") + Text(f"  {_pct(n, total)}", style="dim")


def _split(steps: list[dict]) -> dict[str, list[dict]]:
    out = {d: [] for d in DIRS}
    for s in steps:
        out[s["direction"]].append(s)
    return out


def _key(k: str) -> tuple[str, str, str]:
    """(kind, rung, sub) from a record key; format 1 keys have no kind."""
    parts = k.split("|")
    return ("constraint", *parts) if len(parts) == 2 else tuple(parts)


def _categories(records: list[dict], kind: str) -> Counter:
    """(rung, sub) counts for one kind of obligation."""
    total = Counter()
    for s in records:
        for k, n in s["categories"].items():
            kd, rung, sub = _key(k)
            if kd == kind:
                total[(rung, sub)] += n
    return total


def _undecided(s: dict, kind: str | None = None) -> int:
    return sum(
        n
        for k, n in s["categories"].items()
        if _key(k)[1] == "undecided" and kind in (None, _key(k)[0])
    )


def _label(kind: str, reason: str) -> str:
    # Shared reasons (e.g. "unmapped column") get a prefix when they are about a lookup.
    if kind == "bus" and not reason.startswith("bus:"):
        return f"bus: {reason}"
    return reason


def _reasons(records: list[dict]) -> Counter:
    out = Counter()
    for s in records:
        for k, n in s["categories"].items():
            kind, rung, sub = _key(k)
            if rung == "undecided":
                out[_label(kind, sub)] += n
        if s["error"]:
            out["mapping error"] += 1
    return out


def _witness_failed(s: dict) -> bool:
    """Some column is unmapped because the witness search failed (not lookup-only)."""
    reasons = s.get("unmapped_reasons")
    if reasons is None:  # format 1: every unmapped column was a search failure
        return bool(s["unmapped"])
    return any(r != "lookup-only" for r in reasons.values())


def _has_kind(steps: list[dict], kind: str) -> bool:
    return any(_key(k)[0] == kind for s in steps for k in s["categories"])


def _top(c: Counter, n: int = 2) -> str:
    return "; ".join(f"{r} ({k:,})" for r, k in c.most_common(n))


# ---------------------------------------------------------------- sections


def _header(meta: dict, steps: list[dict]) -> Panel:
    pairs = len({(s["block"], s["pair"]) for s in steps})
    ranges = "on" if meta.get("byte_ranges", True) else "[yellow]off[/yellow]"
    text = (
        f"[b]{meta.get('group', '?')}[/b]: {meta.get('blocks', '?')} blocks, "
        f"{pairs:,} step pairs, directions: {', '.join(meta.get('directions', DIRS))}\n"
        f"byte ranges {ranges} · {meta.get('seconds', '?')} s · "
        f"verifier {meta.get('verifier_commit') or '?'} · {meta.get('created', '')}"
    )
    return Panel(text, title="Redesign sweep", title_align="left", box=box.ROUNDED)


def _outcomes(by_dir: dict[str, list[dict]]) -> Table:
    t = Table(title="Step pairs", title_justify="left", box=box.SIMPLE_HEAD)
    t.add_column("Outcome")
    for d in DIRS:
        if by_dir[d]:
            t.add_column(d, justify="right")
    t.add_column("Meaning", style="dim")
    rows = [
        (
            "all discharged",
            lambda s: s["verified"],
            "green",
            "every obligation proved without SMT",
        ),
        (
            "undecided left",
            lambda s: not s["verified"] and not s["error"] and not _witness_failed(s),
            "yellow",
            "some obligations need a later rung",
        ),
        (
            "  …only lookups undecided",
            lambda s: (
                not s["verified"]
                and not s["error"]
                and not _witness_failed(s)
                and _undecided(s, "constraint") == 0
            ),
            "dim",
            "(part of the row above) every constraint discharged; only lookups left",
        ),
        (
            "witness search failed",
            _witness_failed,
            "red",
            "a merged column got no witness (soundness), so its constraints are stuck",
        ),
        (
            "mapping error",
            lambda s: bool(s["error"]),
            "red",
            "a new After column has no definition (completeness)",
        ),
    ]
    for label, pred, style, meaning in rows:
        cells = [
            _cell(sum(map(pred, by_dir[d])), len(by_dir[d])) for d in DIRS if by_dir[d]
        ]
        t.add_row(Text(label, style=style), *cells, meaning)
    t.add_row(
        "total", *[f"{len(by_dir[d]):,}" for d in DIRS if by_dir[d]], "", style="bold"
    )
    return t


def _obligations(by_dir: dict[str, list[dict]], kind: str) -> Table:
    dirs = [d for d in DIRS if by_dir[d]]
    cats = {d: _categories(by_dir[d], kind) for d in dirs}
    totals = {d: sum(cats[d].values()) for d in dirs}
    bus = kind == "bus"
    rows, notes = (BUS_ROWS, BUS_RUNG_NOTE) if bus else (DISCHARGED_ROWS, RUNG_NOTE)
    t = Table(
        title=f"Obligations, {KINDS[kind]}: where each one was decided",
        title_justify="left",
        box=box.SIMPLE_HEAD,
    )
    t.add_column("Rung")
    t.add_column("Subcategory")
    for d in dirs:
        t.add_column(d, justify="right")
    t.add_column("Meaning", style="dim")

    def rung_total(rung: str) -> list[Text]:
        return [
            _cell(sum(n for (r, _), n in cats[d].items() if r == rung), totals[d])
            for d in dirs
        ]

    last = None
    for rung, sub, meaning in rows:
        if rung != last:
            if last is not None:
                t.add_section()
            t.add_row(
                Text(rung, style="green bold"),
                Text(notes[rung], style="dim"),
                *rung_total(rung),
                "" if sub else meaning,  # a rung with no subcategories explains itself
            )
            last = rung
        if sub:
            t.add_row(
                "",
                f"  {sub}",
                *[_cell(cats[d][(rung, sub)], totals[d]) for d in dirs],
                meaning,
            )
    t.add_section()
    t.add_row(
        Text("undecided", style="yellow bold"),
        Text("left for later rungs", style="dim"),
        *rung_total("undecided"),
        "",
    )
    reasons = Counter()
    for d in dirs:
        for (r, sub), n in cats[d].items():
            if r == "undecided":
                reasons[sub] += n
    for sub, _ in reasons.most_common():
        t.add_row(
            "",
            f"  {sub}",
            *[_cell(cats[d][("undecided", sub)], totals[d]) for d in dirs],
            REASONS.get(sub, ""),
        )
    t.add_section()
    t.add_row("total", "", *[f"{totals[d]:,}" for d in dirs], "", style="bold")
    cached = [sum(_cached(s, kind) for s in by_dir[d]) for d in dirs]
    t.add_row(
        Text("of which cache hits", style="dim"),
        "",
        *[Text(f"{c:,}", style="dim") for c in cached],
        "repeats of an obligation already decided in the same step",
    )
    return t


def _cached(s: dict, kind: str) -> int:
    by_kind = s.get("cached_by_kind")
    if by_kind is None:  # format 1: all obligations were constraints
        return s["cached"] if kind == "constraint" else 0
    return by_kind.get(kind, 0)


def _by_pass(by_dir: dict[str, list[dict]]) -> Table | None:
    first: dict[str, int] = {}
    groups: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for d in DIRS:
        for s in by_dir[d]:
            groups[(s["pass"], d)].append(s)
            n = int(s["pair"].split("->")[1])
            first[s["pass"]] = min(first.get(s["pass"], n), n)
    noisy = sorted(
        {p for (p, d), rs in groups.items() if any(not s["verified"] for s in rs)},
        key=lambda p: first[p],
    )
    if not noisy:
        return None
    t = Table(
        title="Passes that leave obligations undecided (pipeline order)",
        title_justify="left",
        box=box.SIMPLE_HEAD,
    )
    t.add_column("Pass")
    for d in DIRS:
        if by_dir[d]:
            t.add_column(f"{d}\nsteps not discharged", justify="right")
            t.add_column("undecided", justify="right")
            t.add_column("main reasons", style="dim")
    for p in noisy:
        cells = []
        for d in DIRS:
            if not by_dir[d]:
                continue
            rs = groups.get((p, d), [])
            bad = [s for s in rs if not s["verified"]]
            cells += [
                _cell(len(bad), len(rs)) if rs else Text("-", style="dim"),
                f"{sum(map(_undecided, rs)):,}" if bad else Text("-", style="dim"),
                _top(_reasons(rs)) if bad else "",
            ]
        t.add_row(p, *cells)
    return t


def _recurring(steps: list[dict], group: str, limit: int) -> Table | None:
    groups: dict[tuple, list[dict]] = defaultdict(list)
    for s in steps:
        groups[(s["pair"], s["pass"], s["direction"])].append(s)
    bad = [(k, rs) for k, rs in groups.items() if any(not s["verified"] for s in rs)]
    if not bad:
        return None
    bad.sort(key=lambda kr: (-sum(not s["verified"] for s in kr[1]), kr[0]))
    t = Table(
        title="Recurring problem steps (same step pair across blocks)",
        title_justify="left",
        box=box.SIMPLE_HEAD,
    )
    t.add_column("Steps")
    t.add_column("Pass")
    t.add_column("Direction")
    t.add_column("Blocks", justify="right")
    t.add_column("Undecided", justify="right")
    t.add_column("Main reasons", style="dim")
    t.add_column("Look at one")
    for (pair, p, d), rs in bad[:limit]:
        failing = [s for s in rs if not s["verified"]]
        ex = min(failing, key=_undecided)  # the smallest case is easiest to read
        a, b = pair.split("->")
        t.add_row(
            pair,
            p,
            d,
            f"{len(failing)}/{len(rs)}",
            f"{sum(map(_undecided, failing)):,}",
            _top(_reasons(failing)),
            Text(
                f"redesign check {group} {ex['block']} {a} {b} --direction {d}",
                style="cyan",
            ),
        )
    if len(bad) > limit:
        t.caption = f"{len(bad) - limit} more step pairs not shown (use --top)"
    return t


def _mapping(steps: list[dict]) -> Table | None:
    wit = [s for s in steps if s["witnesses"]]
    unm = [s for s in steps if _witness_failed(s)]
    look = [s for s in steps if "lookup-only" in s.get("unmapped_reasons", {}).values()]
    err = [s for s in steps if s["error"]]
    if not (wit or unm or look or err):
        return None
    t = Table(title="Mapping (Step A)", title_justify="left", box=box.SIMPLE_HEAD)
    t.add_column("What")
    t.add_column("Steps", justify="right")
    t.add_column("Columns", justify="right")
    t.add_column("Where", style="dim")
    cols = sum(len(c) for s in wit for c, _ in s["witnesses"])
    t.add_row(
        Text("uniform witness found", style="green"),
        str(len(wit)),
        str(cols),
        _where(wit),
    )
    t.add_row(
        Text("unmapped (witness search failed)", style="red"),
        str(len(unm)),
        str(sum(_n_unmapped(s, lookup_only=False) for s in unm)),
        _where(unm),
    )
    t.add_row(
        Text("unmapped (lookup-only, no definition)", style="yellow"),
        str(len(look)),
        str(sum(_n_unmapped(s, lookup_only=True) for s in look)),
        _where(look),
    )
    t.add_row(Text("missing definition", style="red"), str(len(err)), "-", _where(err))
    return t


def _n_unmapped(s: dict, lookup_only: bool) -> int:
    reasons = s.get("unmapped_reasons")
    if reasons is None:  # format 1
        return 0 if lookup_only else len(s["unmapped"])
    return sum((r == "lookup-only") == lookup_only for r in reasons.values())


def _where(rs: list[dict], n: int = 4) -> str:
    places = [f"{s['block']} {s['pair']} {s['direction'][:5]}" for s in rs[:n]]
    return "; ".join(places) + (f"; +{len(rs) - n} more" if len(rs) > n else "")


def _blocks(steps: list[dict]) -> Table:
    t = Table(title="Per block", title_justify="left", box=box.SIMPLE_HEAD)
    t.add_column("Block")
    t.add_column("Pairs", justify="right")
    t.add_column("Not discharged")
    by_block: dict[str, list[dict]] = defaultdict(list)
    for s in steps:
        by_block[s["block"]].append(s)
    for block, rs in by_block.items():
        bad = [f"{s['pair']} {s['direction'][:5]}" for s in rs if not s["verified"]]
        t.add_row(
            block,
            str(len({s["pair"] for s in rs})),
            Text(", ".join(bad) or "none", style="yellow" if bad else "green"),
        )
    return t


def _examples(steps: list[dict], per_reason: int) -> Table | None:
    seen: dict[str, list] = defaultdict(list)
    for s in steps:
        for e in s["examples"]:
            label = _label(e.get("kind", "constraint"), e["reason"])
            if len(seen[label]) < per_reason:
                seen[label].append((s, e))
    if not seen:
        return None
    t = Table(
        title="Example undecided obligations", title_justify="left", box=box.SIMPLE_HEAD
    )
    t.add_column("Reason")
    t.add_column("Where")
    t.add_column("Detail", style="dim", overflow="fold")
    for reason, items in sorted(seen.items()):
        for s, e in items:
            t.add_row(
                reason,
                f"{s['block']} {s['pair']} {s['direction']}\n{e['obligation']}",
                e["detail"],
            )
    return t


def render(
    data: dict,
    console: Console | None = None,
    *,
    legend: bool = True,
    top: int = 15,
    by_block: bool = False,
    examples: int = 0,
) -> None:
    """Print the whole report for a sweep result."""
    console = console or Console()
    meta, steps = data["meta"], data["steps"]
    by_dir = _split(steps)
    console.print(_header(meta, steps))
    if legend:
        console.print(
            Panel(
                LEGEND,
                title="How to read this",
                title_align="left",
                box=box.ROUNDED,
                style="dim",
            )
        )
    kinds = [k for k in KINDS if _has_kind(steps, k)]
    parts = [
        _outcomes(by_dir),
        *[_obligations(by_dir, k) for k in kinds],
        _by_pass(by_dir),
        _recurring(steps, meta.get("group", "<group>"), top),
        _mapping(steps),
    ]
    if by_block:
        parts.append(_blocks(steps))
    if examples:
        parts.append(_examples(steps, examples))
    for p in parts:
        if p is not None:
            console.print(p)
            console.print()
