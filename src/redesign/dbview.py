"""Render recorded sweeps (``db.SweepDB``) as terminal tables: ``redesign db``.

``show`` picks a view from the filters: every pass (none), one pass or block
(reasons, shapes, hints, steps), one reason or shape (the obligations), the
hint verdicts (``--hints``), or what changed since another run (``--vs``).
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict

from rich import box
from rich.console import Console
from rich.markup import escape
from rich.panel import Panel
from rich.table import Table
from rich.text import Text

from .db import Filters, SweepDB
from .display import _cell, _label, _top

SHORT = {"completeness": "compl.", "soundness": "sound."}
SHAPE_CHARS = 140  # shape and expression text in tables
# Data goes into tables as Text, never as a str: rich would read "[x0 - 8*x1, 3]"
# as markup and drop it.
CW = Text("c[w] = 0")


def runs(db: SweepDB, limit: int, console: Console | None = None) -> None:
    console = console or Console()
    t = Table(title=f"Runs in {db.path}", title_justify="left", box=box.SIMPLE_HEAD)
    for col in ("id", "created", "label", "code", "switches off", "scope"):
        t.add_column(col)
    for col in ("steps", "verified", "undecided", "hints used / rejected", "seconds"):
        t.add_column(col, justify="right")
    for r in db.runs(limit):
        created = r["created"][:16].replace("T", " ")
        if r["finished"] is None:
            created = Text(created + " (interrupted)", style="yellow")
        t.add_row(
            str(r["id"]),
            created,
            Text(r["label"] or ""),
            Text(_code(r)),
            Text(_off(r)) if _off(r) else _dash(),
            Text(_scope(r)),
            f"{r['steps']:,}",
            _cell(r["verified"] or 0, r["steps"]),
            f"{r['undecided'] or 0:,}",
            f"{r['hints_accepted'] or 0:,} / {r['hints_rejected'] or 0:,}",
            f"{r['seconds']:.0f}" if r["seconds"] is not None else "",
        )
    console.print(t)


def show(
    db: SweepDB,
    run_id: int | None,
    f: Filters,
    *,
    vs: int | None = None,
    hints: bool = False,
    accepted: bool = False,
    limit: int = 20,
    top: int = 15,
    console: Console | None = None,
) -> None:
    console = console or Console()
    run = db.run(run_id)
    console.print(_header(run, f))
    if vs is not None:
        parts = _compare(db, run, db.run(vs), f, limit, top)
    elif hints:
        parts = _hints(db, run, f, accepted, limit, top)
    elif f.shape is not None or f.reason is not None:
        parts = _obligations(db, run, f, limit, top)
    elif f.pass_ is not None or f.block is not None or f.pair is not None:
        parts = _detail(db, run, f, limit, top)
    else:
        parts = _overview(db, run, f, limit)
    for p in parts:
        if p is not None:
            console.print(p)
            console.print()


# ---------------------------------------------------------------- views


def _overview(db: SweepDB, run, f: Filters, limit: int) -> list:
    """Every pass in pipeline order, then the steps with most undecided obligations."""
    rows = db.passes(run["id"], f)
    undecided: dict[tuple[str, str], Counter] = defaultdict(Counter)
    for r in db.reasons(run["id"], f, by_pass=True):
        undecided[(r["pass"], r["direction"])][_label(r["kind"], r["reason"])] += r["n"]
    via = db.via_hint(run["id"], f)
    t = Table(title="Passes (pipeline order)", title_justify="left", box=box.SIMPLE_HEAD)
    t.add_column("pass")
    t.add_column("direction")
    for col in ("steps", "fully discharged", "errors", "unmapped", "undecided"):
        t.add_column(col, justify="right")
    t.add_column("main reasons", style="dim")
    t.add_column("hints used / rejected", justify="right")
    t.add_column("discharged via a hint", justify="right")
    last = None
    for r in rows:
        u = undecided.get((r["pass"], r["direction"]), Counter())
        done = r["verified"] == r["steps"]
        discharged, with_hint = via.get((r["pass"], r["direction"]), (0, 0))
        compl = r["direction"] == "completeness"
        t.add_row(
            r["pass"] if r["pass"] != last else "",
            SHORT[r["direction"]],
            f"{r['steps']:,}",
            _cell(r["verified"], r["steps"]),
            _n(r["errors"]),
            _n(r["with_unmapped"]),
            _n(sum(u.values())),
            Text(_top(u)),
            f"{r['hints_accepted'] or 0:,} / {r['hints_rejected'] or 0:,}" if compl else _dash(),
            _cell(with_hint, discharged) if compl else _dash(),
            style="dim" if done else None,
        )
        last = r["pass"]
    return [t, _steps(db, run, f, limit)]


def _detail(db: SweepDB, run, f: Filters, limit: int, top: int) -> list:
    """One pass (or block, or pair): reasons, shapes, hints, and the steps with work left."""
    t = Table(title="Undecided obligations by reason", title_justify="left", box=box.SIMPLE_HEAD)
    for col in ("direction", "kind", "reason"):
        t.add_column(col)
    t.add_column("obligations", justify="right")
    t.add_column("steps", justify="right")
    reasons = db.reasons(run["id"], f)
    for r in reasons:
        t.add_row(
            SHORT[r["direction"]], r["kind"], Text(r["reason"]), f"{r['n']:,}", f"{r['steps']:,}"
        )
    if not reasons:
        t = Text("Nothing undecided here.", style="green")
    return [t, _shapes(db, run, f, top), _hint_summary(db, run, f), _steps(db, run, f, limit)]


def _obligations(db: SweepDB, run, f: Filters, limit: int, top: int) -> list:
    """The undecided obligations of one reason or shape."""
    n, steps = db.count_undecided(run["id"], f)
    parts: list = [Text(f"{n:,} undecided obligations in {steps:,} steps match.", style="bold")]
    if f.shape is None:
        parts.append(_shapes(db, run, f, top))
    else:
        texts = db.query("SELECT * FROM shapes WHERE id LIKE ?", (f.shape + "%",))
        for s in texts[:3]:
            parts.append(Panel(Text(s["text"]), title=f"shape {s['id']}", title_align="left"))
    t = Table(
        title=f"Obligations (first {limit})", title_justify="left", box=box.SIMPLE_HEAD
    )
    for col in ("block", "pair", "dir.", "pass", "obligation", "reason"):
        t.add_column(col)
    t.add_column(CW, overflow="fold", ratio=3)
    t.add_column("detail", overflow="fold", style="dim", ratio=2)
    for o in db.undecided(run["id"], f, limit):
        t.add_row(
            o["block"],
            o["pair"],
            SHORT[o["direction"]],
            o["pass"],
            Text(_name(o)),
            Text(o["reason"]),
            _cut(o["expr"]),
            _cut(o["detail"]),
        )
    parts += [t, _steps(db, run, f, min(limit, 5))]
    return parts


def _hints(db: SweepDB, run, f: Filters, accepted: bool, limit: int, top: int) -> list:
    which = "Accepted" if accepted else "Rejected"
    t = Table(
        title=f"{which} hints by {'rule' if accepted else 'reason'} and column family",
        title_justify="left",
        box=box.SIMPLE_HEAD,
    )
    t.add_column("rule" if accepted else "reason")
    t.add_column("family")
    t.add_column("hints", justify="right")
    t.add_column("steps", justify="right")
    for r in db.hint_kinds(run["id"], f, accepted)[:top]:
        t.add_row(Text(r["kind"]), Text(r["family"]), f"{r['n']:,}", f"{r['steps']:,}")
    ex = Table(title=f"{which} hints (first {limit})", title_justify="left", box=box.SIMPLE_HEAD)
    for col in ("block", "pair", "pass", "column", "kind"):
        ex.add_column(col)
    ex.add_column("note", overflow="fold", style="dim")
    for h in db.hints(run["id"], f, accepted, limit):
        ex.add_row(
            h["block"], h["pair"], h["pass"], Text(h["col"]), Text(h["kind"]), _cut(h["note"])
        )
    return [_hint_summary(db, run, f), t, ex]


def _compare(db: SweepDB, run, base, f: Filters, limit: int, top: int) -> list:
    if run["id"] == base["id"]:
        raise LookupError("--vs needs a different run")
    c = db.compare(run["id"], base["id"], f, limit)
    notes = [
        f"Compared with run {base['id']} ({escape(_code(base))}"
        + (f", {escape(base['label'])}" if base["label"] else "")
        + f") on {c.shared:,} shared steps."
    ]
    a_cfg, b_cfg = _config(run), _config(base)
    for k in sorted(a_cfg.keys() | b_cfg.keys()):
        if a_cfg.get(k) != b_cfg.get(k):
            notes.append(f"switch {k}: {_onoff(b_cfg.get(k))} -> {_onoff(a_cfg.get(k))}")
    if run["dumps"] != base["dumps"]:
        notes.append("[yellow]the dumps differ: obligations may be matched to the wrong ones[/]")
    if f.reason is not None or f.shape is not None:
        notes.append("obligations: only those matching --reason/--shape in the base run")
    elif c.matched != c.totals[1] or c.matched != c.totals[0]:
        notes.append(
            f"[yellow]{c.matched:,} obligations matched by name; this run has"
            f" {c.totals[0]:,}, the base {c.totals[1]:,}[/]"
        )
    head = Panel("\n".join(notes), box=box.ROUNDED)

    totals = Table(title="Totals on the shared steps", title_justify="left", box=box.SIMPLE_HEAD)
    totals.add_column("")
    for col in (f"run {base['id']}", f"run {run['id']}", "change"):
        totals.add_column(col, justify="right")
    b, a = c.counters["base"], c.counters["run"]
    # (column, label, whether an increase is progress)
    for key, label, up in (
        ("verified", "steps fully discharged", True),
        ("undecided", "undecided obligations", False),
        ("hints_accepted", "hints used", True),
        ("hints_rejected", "hints rejected", False),
        ("pinned", "pins", None),
        ("constants_solved", "constants solved", None),
    ):
        x, y = b[key] or 0, a[key] or 0
        totals.add_row(label, f"{x:,}", f"{y:,}", _delta(y - x, up))

    moves: Counter = Counter()
    rungs: Counter = Counter()
    for t in c.transitions:
        was_u, now_u = t["was"] == "undecided", t["now"] == "undecided"
        if was_u and not now_u:
            moves[("discharged now", f"by {t['now']}", _label(t["kind"], t["was_reason"]))] += t["n"]
        elif now_u and not was_u:
            moves[("regressed", f"was {t['was']}", _label(t["kind"], t["now_reason"]))] += t["n"]
        elif was_u and t["was_reason"] != t["now_reason"]:
            moves[("still undecided", "reason changed", f"{t['was_reason']} -> {t['now_reason']}")] += t["n"]
        elif was_u:
            moves[("still undecided", "", _label(t["kind"], t["now_reason"]))] += t["n"]
        elif t["was"] != t["now"]:
            rungs[(t["was"], t["now"])] += t["n"]
    obl = Table(title="Obligations", title_justify="left", box=box.SIMPLE_HEAD)
    for col in ("change", "how", "reason (in the run where it is undecided)"):
        obl.add_column(col)
    obl.add_column("obligations", justify="right")
    order = {"discharged now": 0, "regressed": 1, "still undecided": 2}
    for (what, how, why), n in sorted(moves.items(), key=lambda kv: (order[kv[0][0]], -kv[1])):
        style = {"discharged now": "green", "regressed": "red"}.get(what)
        obl.add_row(Text(what, style=style), Text(how), Text(why), f"{n:,}")
    for (was, now), n in rungs.most_common(top):
        obl.add_row(Text("other rung", style="dim"), Text(f"{was} -> {now}"), "", f"{n:,}")

    parts: list = [head, totals, obl]
    if c.discharged:
        parts.append(_changed(f"Discharged now (first {limit})", c.discharged, now=True))
    if c.regressed:
        parts.append(_changed(f"Regressed (first {limit})", c.regressed, now=False))
    if c.hints:
        h = Table(title="Hints whose verdict changed", title_justify="left", box=box.SIMPLE_HEAD)
        h.add_column("change")
        h.add_column("family")
        h.add_column("hints", justify="right")
        for r in c.hints[:top]:
            what = Text("now accepted", style="green") if r["now"] else Text("now rejected", style="red")
            h.add_row(what, Text(r["family"]), f"{r['n']:,}")
        parts.append(h)
    if c.step_changes:
        s = Table(title="Steps whose verdict changed", title_justify="left", box=box.SIMPLE_HEAD)
        for col in ("block", "pair", "dir.", "pass", "now"):
            s.add_column(col)
        for r in c.step_changes:
            now = Text("verified", style="green") if r["a_verified"] else Text("not verified", style="red")
            s.add_row(r["block"], r["pair"], SHORT[r["direction"]], r["pass"], now)
        parts.append(s)
    return parts


# ---------------------------------------------------------------- pieces


def _header(run, f: Filters) -> Panel:
    lines = [
        f"[bold]Run {run['id']}[/]"
        + (f"  {escape(run['label'])}" if run["label"] else "")
        + f"  [dim]{run['group_name']}  {escape(_code(run))}"
        + f"  {run['created'][:16].replace('T', ' ')}"
        + (f"  {run['seconds']:.0f} s" if run["seconds"] is not None else "")
        + "[/]"
    ]
    if run["finished"] is None:
        lines.append("[yellow]interrupted: only the steps swept before the stop are here[/]")
    off, scope = _off(run), _scope(run)
    if off or scope != "all":
        lines.append(f"switches off: {off or '-'}   scope: {escape(scope)}")
    shown = [
        f"{k} {v}"
        for k, v in (
            ("pass", f.pass_),
            ("direction", f.direction),
            ("block", f.block),
            ("pair", f.pair),
            ("kind", f.kind),
            ("reason", f.reason),
            ("shape", f.shape),
        )
        if v is not None
    ]
    if shown:
        lines.append("showing: " + escape(", ".join(shown)))
    return Panel("\n".join(lines), box=box.ROUNDED)


def _steps(db: SweepDB, run, f: Filters, limit: int) -> Table | Text:
    rows = db.steps(run["id"], f, limit)
    if not rows:
        return Text("Every step here is fully discharged.", style="green")
    t = Table(
        title=f"Steps not fully discharged (first {limit}, most undecided first)",
        title_justify="left",
        box=box.SIMPLE_HEAD,
    )
    for col in ("block", "pair", "dir.", "pass"):
        t.add_column(col)
    t.add_column("undecided", justify="right")
    t.add_column("unmapped", justify="right")
    t.add_column("look closer", style="dim", overflow="fold")
    for s in rows:
        t.add_row(
            s["block"],
            s["pair"],
            SHORT[s["direction"]],
            s["pass"],
            Text("error", style="red") if s["error"] else _n(s["shown_undecided"]),
            _n(s["unmapped"]),
            Text(_check_cmd(run, s)),
        )
    return t


def _shapes(db: SweepDB, run, f: Filters, top: int) -> Table | None:
    rows = db.shapes(run["id"], f, top)
    if not rows:
        return None
    t = Table(
        title=f"Shapes of the undecided obligations (top {top}; --shape ID to list one)",
        title_justify="left",
        box=box.SIMPLE_HEAD,
    )
    t.add_column("shape")
    t.add_column("obligations", justify="right")
    t.add_column("steps", justify="right")
    t.add_column("reason")
    t.add_column("columns renamed x0, x1, ...", overflow="fold")
    for r in rows:
        if r["shape"] is None:
            t.add_row(
                Text("-", style="dim"),
                f"{r['n']:,}",
                f"{r['steps']:,}",
                Text(r["reason"]),
                Text("no shape: an opaque or unmapped column", style="dim"),
            )
        else:
            t.add_row(
                r["shape"], f"{r['n']:,}", f"{r['steps']:,}", Text(r["reason"]), _cut(r["text"])
            )
    return t


def _hint_summary(db: SweepDB, run, f: Filters) -> Text | None:
    """Hints are completeness only: used, rejected (by reason), pins, constants."""
    if f.direction == "soundness":
        return None
    rows = [r for r in db.passes(run["id"], f) if r["direction"] == "completeness"]
    if not rows:
        return None
    used = sum(r["hints_accepted"] or 0 for r in rows)
    rejected = sum(r["hints_rejected"] or 0 for r in rows)
    pins = sum(r["pinned"] or 0 for r in rows)
    consts = sum(r["constants_solved"] or 0 for r in rows)
    why = Counter()
    for r in db.hint_kinds(run["id"], f, accepted=False):
        why[r["kind"]] += r["n"]
    compl = [v for (_, d), v in db.via_hint(run["id"], f).items() if d == "completeness"]
    discharged = sum(n for n, _ in compl)
    with_hint = sum(h for _, h in compl)
    out = Text("Completeness: ", style="bold")
    out.append(f"hints {used:,} used, {rejected:,} rejected")
    if why:
        out.append(f" ({_top(why, 4)})", style="dim")
    out.append(f"; {pins:,} pins; {consts:,} constants solved; ")
    out.append(f"{with_hint:,} of {discharged:,} discharged obligations used a hint")
    out.append("\n(--hints lists the rejected ones)", style="dim")
    return out


def _changed(title: str, rows, now: bool) -> Table:
    t = Table(title=title, title_justify="left", box=box.SIMPLE_HEAD)
    for col in ("block", "pair", "dir.", "pass", "obligation"):
        t.add_column(col)
    t.add_column("now" if now else "reason now")
    t.add_column(CW, overflow="fold")
    for r in rows:
        t.add_row(
            r["block"],
            r["pair"],
            SHORT[r["direction"]],
            r["pass"],
            Text(_name(r)),
            Text(r["now"] if now else (r["now_reason"] or "")),
            _cut(r["expr"]),
        )
    return t


def _name(o) -> str:
    """Full obligation name: the candidate's label (After in completeness)."""
    label = o["after"] if o["direction"] == "completeness" else o["before"]
    return f"{label}:{o['ob']}"


def _check_cmd(run, s) -> str:
    a, b = s["pair"].split("->")
    return (
        f"uv run redesign check {run['group_name']} {s['block']} {a} {b}"
        f" --direction {s['direction']} -v"
    )


def _code(r) -> str:
    code = f"{r['git_branch'] or '?'}@{r['git_commit'] or '?'}"
    return code + (f"+dirty:{r['git_dirty']}" if r["git_dirty"] else "")


def _config(r) -> dict:
    return json.loads(r["config"]) if r["config"] else {}


def _off(r) -> str:
    return ", ".join(k for k, v in _config(r).items() if v is False)


def _scope(r) -> str:
    passes, blocks = json.loads(r["passes"]), json.loads(r["blocks"])
    parts = []
    if passes:
        parts.append("passes " + ", ".join(passes))
    if blocks:
        parts.append(f"{len(blocks)} blocks" if len(blocks) > 3 else "blocks " + ", ".join(blocks))
    return "; ".join(parts) or "all"


def _onoff(v) -> str:
    return {True: "on", False: "off", None: "?"}[v]


def _n(n) -> Text | str:
    return f"{n:,}" if n else _dash()


def _dash() -> Text:
    return Text("-", style="dim")


def _delta(d: int, up: bool | None) -> Text:
    """A change, green when it is progress (``up``: an increase is), red when not."""
    if not d:
        return _dash()
    if up is None:
        return Text(f"{d:+,}")
    return Text(f"{d:+,}", style="green" if (d > 0) == up else "red")


def _cut(s: str | None, n: int = SHAPE_CHARS) -> Text:
    if not s:
        return Text("")
    return Text(s if len(s) <= n else s[:n] + " …")
