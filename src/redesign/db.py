"""Sweep results in SQLite: runs, steps, undecided obligations and hints.

``redesign sweep`` records every run here (``--no-db`` to skip) and
``redesign db`` reads the runs back (rendered by ``dbview``). Undecided
obligations get a row each, with their expression, a shape for grouping and
the detail. Discharged ones (about 99%) are only counted per step, by rung,
and kept as one byte each in the step's verdicts, which is what ``compare``
matches obligation by obligation. A full keccak run is about 10 MB.

The tables are plain, so ``sqlite3 reports/sweeps.db`` or Datasette work too.
"""

from __future__ import annotations

import hashlib
import json
import re
import sqlite3
import subprocess
from collections import Counter
from dataclasses import dataclass, fields
from datetime import datetime
from pathlib import Path
from typing import Self

from src.lens.canon import ONE, CanonError, canon_zero
from src.lens.diff import _bus_exact_key
from src.lens.resolve import group_dir
from src.paths import POWDR_DUMPS_DIR, REPORTS_DIR, VERIFIER_DIR

from .adapter import HINT_TAG
from .circuit import Circuit
from .sweep import Obligation, Report

DEFAULT_PATH = REPORTS_DIR / "sweeps.db"
SCHEMA_VERSION = 1
EXPR_CHARS = 2000  # longer expressions are cut (shapes are not: they are hashed)
KINDS = {"constraint": "c", "bus": "b"}  # obligation kind -> name prefix ("c17", "b3")

# A verdict byte: the rung's code in the low 5 bits, then three flags.
RUNG_BITS = 0x1F
VIA_MAPPING, VIA_HINT, CACHED = 0x20, 0x40, 0x80

SCHEMA = """
CREATE TABLE IF NOT EXISTS runs (
    id INTEGER PRIMARY KEY,
    created TEXT NOT NULL,
    finished TEXT,              -- NULL: interrupted
    label TEXT,
    group_name TEXT NOT NULL,
    blocks TEXT NOT NULL,       -- JSON list, [] = all
    passes TEXT NOT NULL,       -- JSON list, [] = all
    config TEXT,                -- JSON: the on/off switches of the sweep
    git_commit TEXT,
    git_branch TEXT,
    git_dirty TEXT,             -- hash of the uncommitted changes under src/, NULL if clean
    dumps TEXT,                 -- hash of the dump directory listing (names, sizes)
    seconds REAL,
    meta TEXT                   -- run_sweep's meta, as JSON
);
CREATE TABLE IF NOT EXISTS steps (
    id INTEGER PRIMARY KEY,
    run_id INTEGER NOT NULL REFERENCES runs(id) ON DELETE CASCADE,
    block TEXT NOT NULL,
    pair TEXT NOT NULL,         -- "002->003"
    nnn INTEGER NOT NULL,       -- After's step number, for pipeline order
    before TEXT NOT NULL,
    after TEXT NOT NULL,
    pass TEXT NOT NULL,
    direction TEXT NOT NULL,
    verified INTEGER NOT NULL,  -- every obligation discharged, every column mapped
    error TEXT,                 -- mapping error: no obligations were checked
    obligations INTEGER NOT NULL,
    undecided INTEGER NOT NULL,
    unmapped INTEGER NOT NULL,
    -- One byte per obligation, by index (c0, c1, ... and b0, b1, ...):
    -- rung code (rung_codes) | 0x20 via mapping | 0x40 via a hint | 0x80 cached.
    constraint_verdicts BLOB,
    bus_verdicts BLOB,
    -- Report's counters; a counter added later becomes a column on first sight.
    premises_expanded INTEGER,
    premises_split INTEGER,
    hints_accepted INTEGER,
    hints_rejected INTEGER,
    constants_solved INTEGER,
    pinned INTEGER,
    UNIQUE (run_id, block, pair, direction)
);
CREATE INDEX IF NOT EXISTS steps_by_pass ON steps (run_id, pass);
CREATE TABLE IF NOT EXISTS rung_codes (
    code INTEGER PRIMARY KEY,
    rung TEXT NOT NULL UNIQUE
);
-- Every obligation, counted per step.
CREATE TABLE IF NOT EXISTS rungs (
    step_id INTEGER NOT NULL REFERENCES steps(id) ON DELETE CASCADE,
    kind TEXT NOT NULL,         -- constraint | bus
    rung TEXT NOT NULL,         -- a discharging rung, or undecided
    via_mapping INTEGER NOT NULL,
    via_hint INTEGER NOT NULL,  -- discharged with a hint's help (used, maybe not needed)
    cached INTEGER NOT NULL,
    n INTEGER NOT NULL,
    PRIMARY KEY (step_id, kind, rung, via_mapping, via_hint, cached)
) WITHOUT ROWID;
-- The undecided obligations, one row each.
CREATE TABLE IF NOT EXISTS undecided (
    step_id INTEGER NOT NULL REFERENCES steps(id) ON DELETE CASCADE,
    ob TEXT NOT NULL,           -- "c17" or "b3"; full name "<candidate label>:<ob>"
    kind TEXT NOT NULL,
    reason TEXT NOT NULL,
    cached INTEGER NOT NULL,
    via_mapping INTEGER NOT NULL,
    expr TEXT,                  -- c[w] = 0 in canonical form (c itself if c[w] has no key)
    shape TEXT REFERENCES shapes(id),  -- NULL: an opaque or unmapped column
    detail TEXT,
    PRIMARY KEY (step_id, ob)
) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS shapes (
    id TEXT PRIMARY KEY,        -- short hash of text
    text TEXT NOT NULL          -- c[w] with columns renamed x0, x1, ...
) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS hints (
    step_id INTEGER NOT NULL REFERENCES steps(id) ON DELETE CASCADE,
    col TEXT NOT NULL,
    family TEXT NOT NULL,       -- col without its @id and trailing _<n>
    accepted INTEGER NOT NULL,
    kind TEXT NOT NULL,         -- the rule that proved it, or why it was rejected
    note TEXT,
    PRIMARY KEY (step_id, col)
) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS unmapped (
    step_id INTEGER NOT NULL REFERENCES steps(id) ON DELETE CASCADE,
    col TEXT NOT NULL,
    reason TEXT NOT NULL,
    PRIMARY KEY (step_id, col)
) WITHOUT ROWID;
"""


class SweepDB:
    """A connection to the results database; creates the schema if needed."""

    def __init__(self, path: Path = DEFAULT_PATH, create: bool = True):
        if not create and not path.exists():
            raise FileNotFoundError(f"no sweep database at {path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        self.path = path
        self.con = sqlite3.connect(path)
        self.con.row_factory = sqlite3.Row
        self.con.execute("PRAGMA foreign_keys = ON")
        self.con.execute("PRAGMA journal_mode = WAL")
        self.con.execute("PRAGMA synchronous = NORMAL")
        version = self.con.execute("PRAGMA user_version").fetchone()[0]
        if version > SCHEMA_VERSION:
            raise RuntimeError(f"{path} has schema {version}; this code knows {SCHEMA_VERSION}")
        self.con.executescript(SCHEMA)
        self.con.execute(f"PRAGMA user_version = {SCHEMA_VERSION}")
        self._step_columns = {r[1] for r in self.con.execute("PRAGMA table_info(steps)")}
        self._codes = {r["rung"]: r["code"] for r in self.query("SELECT * FROM rung_codes")}

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *exc) -> None:
        self.con.close()

    # ------------------------------------------------------------ writing

    def start_run(
        self,
        group: str,
        label: str | None = None,
        blocks=(),
        passes=(),
        root: Path | None = None,
    ) -> int:
        """A new run row; the code and dumps it runs on are identified now."""
        commit, branch, dirty = _git()
        directory = group_dir(group, root or POWDR_DUMPS_DIR)
        with self.con:
            cur = self.con.execute(
                "INSERT INTO runs (created, label, group_name, blocks, passes,"
                " git_commit, git_branch, git_dirty, dumps)"
                " VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (
                    _now(),
                    label,
                    group,
                    json.dumps(sorted(blocks)),
                    json.dumps(sorted(passes)),
                    commit,
                    branch,
                    dirty,
                    _dumps_hash(directory),
                ),
            )
        return cur.lastrowid

    def add_pair(
        self,
        run_id: int,
        records: list[dict],
        reports: list[Report | None],
        before: Circuit,
        after: Circuit,
    ) -> None:
        """One step pair (both directions), in one transaction."""
        with self.con:
            for rec, r in zip(records, reports):
                self._add_step(run_id, rec, r, (before, after))

    def finish(self, run_id: int, meta: dict) -> None:
        """Mark the run complete; its config is the on/off switches in ``meta``."""
        config = {k: v for k, v in meta.items() if isinstance(v, bool)}
        with self.con:
            self.con.execute(
                "UPDATE runs SET finished = ?, config = ?, seconds = ?, meta = ?"
                " WHERE id = ?",
                (_now(), json.dumps(config), meta.get("seconds"), json.dumps(meta), run_id),
            )

    def drop(self, run_id: int) -> bool:
        """Delete a run and everything recorded for it; False if there is none."""
        with self.con:
            cur = self.con.execute("DELETE FROM runs WHERE id = ?", (run_id,))
        return cur.rowcount > 0

    def _add_step(self, run_id: int, rec: dict, r: Report | None, circuits) -> None:
        obligations = r.obligations if r else []
        counters = _counters(r) if r else {}
        for name in counters.keys() - self._step_columns:
            self.con.execute(f"ALTER TABLE steps ADD COLUMN {name} INTEGER")
            self._step_columns.add(name)
        verdicts = {kind: bytearray() for kind in KINDS}
        counts: Counter = Counter()
        for o in obligations:
            hint = o.rung != "undecided" and f"solved {HINT_TAG}" in o.detail
            counts[(o.kind, o.rung, int(o.via_mapping), int(hint), int(o.cached))] += 1
            i = int(o.name.rsplit(":", 1)[1][1:])
            v = verdicts[o.kind]
            v.extend(bytes(i + 1 - len(v)))
            v[i] = (
                self._code(o.rung)
                | (VIA_MAPPING if o.via_mapping else 0)
                | (VIA_HINT if hint else 0)
                | (CACHED if o.cached else 0)
            )
        row = {
            "run_id": run_id,
            "block": rec["block"],
            "pair": rec["pair"],
            "nnn": int(rec["pair"].split("->")[1]),
            "before": rec["before"],
            "after": rec["after"],
            "pass": rec["pass"],
            "direction": rec["direction"],
            "verified": int(rec["verified"]),
            "error": rec["error"],
            "obligations": len(obligations),
            "undecided": sum(o.rung == "undecided" for o in obligations),
            "unmapped": len(r.mapping.unmapped) if r else 0,
            "constraint_verdicts": bytes(verdicts["constraint"]) if r else None,
            "bus_verdicts": bytes(verdicts["bus"]) if r else None,
            **counters,
        }
        cur = self.con.execute(
            f"INSERT INTO steps ({', '.join(row)}) VALUES ({', '.join('?' * len(row))})",
            list(row.values()),
        )
        step = cur.lastrowid
        if r is None:
            return
        self.con.executemany(
            "INSERT INTO rungs VALUES (?, ?, ?, ?, ?, ?, ?)",
            [(step, *k, n) for k, n in counts.items()],
        )
        # The candidate is the circuit the obligations' names point into.
        cand = {c.label: c for c in circuits}
        rows, shapes = [], {}
        for o in obligations:
            if o.rung == "undecided":
                label, ob = o.name.rsplit(":", 1)
                rows.append(_undecided_row(step, ob, o, cand.get(label), shapes))
        self.con.executemany(
            "INSERT OR IGNORE INTO shapes (id, text) VALUES (?, ?)", shapes.items()
        )
        self.con.executemany(
            "INSERT INTO undecided VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)", rows
        )
        self.con.executemany(
            "INSERT INTO hints VALUES (?, ?, ?, ?, ?, ?)",
            [
                (step, col, family(col), int(ok), kind, note or None)
                for col, ok, kind, note in r.hints
            ],
        )
        self.con.executemany(
            "INSERT INTO unmapped VALUES (?, ?, ?)",
            [
                (step, col, r.mapping.unmapped_reason.get(col, "witness search failed"))
                for col in sorted(r.mapping.unmapped)
            ],
        )

    def _code(self, rung: str) -> int:
        """The rung's code in verdict bytes; a new rung gets the next one."""
        if rung not in self._codes:
            code = len(self._codes) + 1
            if code > RUNG_BITS:
                raise RuntimeError(f"more than {RUNG_BITS} rungs: widen the verdict bytes")
            self.con.execute("INSERT INTO rung_codes VALUES (?, ?)", (code, rung))
            self._codes[rung] = code
        return self._codes[rung]

    # ------------------------------------------------------------ reading

    def query(self, sql: str, params=()) -> list[sqlite3.Row]:
        return self.con.execute(sql, params).fetchall()

    def run(self, run_id: int | None = None) -> sqlite3.Row:
        """One run; by default the latest finished one."""
        if run_id is None:
            rows = self.query(
                "SELECT * FROM runs WHERE finished IS NOT NULL ORDER BY id DESC LIMIT 1"
            )
            if not rows:
                raise LookupError(f"no finished run in {self.path}")
        else:
            rows = self.query("SELECT * FROM runs WHERE id = ?", (run_id,))
            if not rows:
                raise LookupError(f"no run {run_id} in {self.path}")
        return rows[0]

    def runs(self, limit: int = 20) -> list[sqlite3.Row]:
        return self.query(
            "SELECT r.*, COUNT(s.id) AS steps, SUM(s.verified) AS verified,"
            " SUM(s.error IS NOT NULL) AS errors, SUM(s.undecided) AS undecided,"
            " SUM(s.hints_accepted) AS hints_accepted,"
            " SUM(s.hints_rejected) AS hints_rejected"
            " FROM runs r LEFT JOIN steps s ON s.run_id = r.id"
            " GROUP BY r.id ORDER BY r.id DESC LIMIT ?",
            (limit,),
        )

    def passes(self, run_id: int, f: Filters) -> list[sqlite3.Row]:
        """Per (pass, direction): step outcomes and counters, in pipeline order."""
        where, params = f.steps(run_id)
        return self.query(
            "SELECT s.pass, s.direction, MIN(s.nnn) AS first, COUNT(*) AS steps,"
            " SUM(s.verified) AS verified, SUM(s.error IS NOT NULL) AS errors,"
            " SUM(s.unmapped > 0) AS with_unmapped,"
            " SUM(s.hints_accepted) AS hints_accepted,"
            " SUM(s.hints_rejected) AS hints_rejected,"
            " SUM(s.pinned) AS pinned, SUM(s.constants_solved) AS constants_solved"
            f" FROM steps s WHERE {where} GROUP BY s.pass, s.direction"
            " ORDER BY first, s.direction",
            params,
        )

    def reasons(self, run_id: int, f: Filters, by_pass: bool = False) -> list[sqlite3.Row]:
        """Undecided obligations per (direction, kind, reason), optionally per pass."""
        where, params = f.undecided(run_id)
        group = "s.pass, s.direction, o.kind, o.reason" if by_pass else (
            "s.direction, o.kind, o.reason"
        )
        return self.query(
            f"SELECT {group}, COUNT(*) AS n, COUNT(DISTINCT o.step_id) AS steps"
            f" FROM undecided o JOIN steps s ON s.id = o.step_id"
            f" WHERE {where} GROUP BY {group} ORDER BY n DESC",
            params,
        )

    def via_hint(self, run_id: int, f: Filters) -> dict[tuple[str, str], tuple[int, int]]:
        """(pass, direction) -> (discharged, discharged with a hint's help)."""
        where, params = f.steps(run_id)
        if f.kind is not None:
            where, params = f"{where} AND r.kind = ?", [*params, f.kind]
        rows = self.query(
            "SELECT s.pass, s.direction, SUM(r.n) AS discharged,"
            " SUM(r.n * r.via_hint) AS via_hint FROM rungs r"
            f" JOIN steps s ON s.id = r.step_id WHERE {where} AND r.rung != 'undecided'"
            " GROUP BY s.pass, s.direction",
            params,
        )
        return {(r["pass"], r["direction"]): (r["discharged"], r["via_hint"]) for r in rows}

    def steps(self, run_id: int, f: Filters, limit: int) -> list[sqlite3.Row]:
        """Steps that are not verified, most (matching) undecided obligations first."""
        where, params = f.steps(run_id)
        und_where, und_params = f.undecided(run_id)
        # With an obligation filter, only the steps that have a matching one.
        has = " AND u.n > 0" if f.selects_obligations() else ""
        return self.query(
            "SELECT s.*, COALESCE(u.n, 0) AS shown_undecided FROM steps s"
            " LEFT JOIN (SELECT o.step_id, COUNT(*) AS n FROM undecided o"
            f"  JOIN steps s ON s.id = o.step_id WHERE {und_where}"
            "  GROUP BY o.step_id) u ON u.step_id = s.id"
            f" WHERE {where} AND NOT s.verified{has}"
            " ORDER BY shown_undecided DESC, s.block, s.nnn LIMIT ?",
            [*und_params, *params, limit],
        )

    def shapes(self, run_id: int, f: Filters, limit: int) -> list[sqlite3.Row]:
        """The most common shapes of undecided obligations (NULL: no shape)."""
        where, params = f.undecided(run_id)
        return self.query(
            "SELECT o.shape, sh.text, COUNT(*) AS n, COUNT(DISTINCT o.step_id) AS steps,"
            " MIN(o.reason) AS reason, MIN(o.expr) AS example"
            " FROM undecided o JOIN steps s ON s.id = o.step_id"
            " LEFT JOIN shapes sh ON sh.id = o.shape"
            f" WHERE {where} GROUP BY o.shape ORDER BY n DESC LIMIT ?",
            [*params, limit],
        )

    def undecided(self, run_id: int, f: Filters, limit: int) -> list[sqlite3.Row]:
        """Undecided obligations matching the filters, step by step."""
        where, params = f.undecided(run_id)
        return self.query(
            "SELECT s.block, s.pair, s.direction, s.pass, s.before, s.after, o.*"
            " FROM undecided o JOIN steps s ON s.id = o.step_id"
            f" WHERE {where} ORDER BY s.block, s.nnn, s.direction, o.kind, o.ob LIMIT ?",
            [*params, limit],
        )

    def count_undecided(self, run_id: int, f: Filters) -> tuple[int, int]:
        """(undecided obligations, steps they are in) matching the filters."""
        where, params = f.undecided(run_id)
        r = self.query(
            "SELECT COUNT(*), COUNT(DISTINCT o.step_id) FROM undecided o"
            f" JOIN steps s ON s.id = o.step_id WHERE {where}",
            params,
        )[0]
        return r[0], r[1]

    def hint_kinds(self, run_id: int, f: Filters, accepted: bool) -> list[sqlite3.Row]:
        """Hints per (kind, family): why they were rejected (or how accepted)."""
        where, params = f.steps(run_id)
        return self.query(
            "SELECT h.kind, h.family, COUNT(*) AS n, COUNT(DISTINCT h.step_id) AS steps"
            " FROM hints h JOIN steps s ON s.id = h.step_id"
            f" WHERE {where} AND h.accepted = ? GROUP BY h.kind, h.family"
            " ORDER BY n DESC",
            [*params, int(accepted)],
        )

    def hints(self, run_id: int, f: Filters, accepted: bool, limit: int) -> list[sqlite3.Row]:
        where, params = f.steps(run_id)
        return self.query(
            "SELECT s.block, s.pair, s.pass, h.* FROM hints h"
            " JOIN steps s ON s.id = h.step_id"
            f" WHERE {where} AND h.accepted = ?"
            " ORDER BY s.block, s.nnn, h.col LIMIT ?",
            [*params, int(accepted), limit],
        )

    # ------------------------------------------------------------ comparing

    def compare(self, run_id: int, base_id: int, f: Filters, limit: int) -> Comparison:
        """What changed from ``base_id`` to ``run_id`` on the steps both have.

        Steps are matched on (block, pair, direction), obligations on their
        name (their index in the verdict bytes), hints on their column.
        ``--reason`` and ``--shape`` select obligations by what they were in
        the base run.
        """
        where, params = f.steps(run_id)
        self.con.execute("DROP TABLE IF EXISTS temp.shared")
        self.con.execute(
            "CREATE TEMP TABLE shared AS SELECT s.id AS a, b.id AS b,"
            " s.verified AS a_verified, b.verified AS b_verified,"
            " s.block, s.pair, s.direction, s.pass, s.nnn, s.before, s.after"
            " FROM steps s JOIN steps b ON b.run_id = ? AND b.block = s.block"
            f" AND b.pair = s.pair AND b.direction = s.direction WHERE {where}",
            [base_id, *params],
        )
        rung_of = {code: rung for rung, code in self._codes.items()}
        rung_of[0] = "missing"  # a gap in the verdict bytes (not expected)
        kind_where = "" if f.kind is None else " WHERE o.kind = ?"
        kind_params = [] if f.kind is None else [f.kind]
        und: dict[int, dict[str, sqlite3.Row]] = {}
        for side in ("a", "b"):
            for o in self.query(
                f"SELECT o.* FROM shared p JOIN undecided o ON o.step_id = p.{side}"
                + kind_where,
                kind_params,
            ):
                und.setdefault(o["step_id"], {})[o["ob"]] = o
        pairs = self.query(
            "SELECT p.*, a.constraint_verdicts AS a_c, a.bus_verdicts AS a_b,"
            " b.constraint_verdicts AS b_c, b.bus_verdicts AS b_b FROM shared p"
            " JOIN steps a ON a.id = p.a JOIN steps b ON b.id = p.b"
            " ORDER BY p.block, p.nnn, p.direction"
        )
        transitions: Counter = Counter()  # (kind, was, now, was_reason, now_reason)
        discharged, regressed = [], []
        matched = total_a = total_b = 0
        selecting = f.reason is not None or f.shape is not None
        for p in pairs:
            rows_a, rows_b = und.get(p["a"], {}), und.get(p["b"], {})
            for kind, prefix in KINDS.items():
                if f.kind not in (None, kind):
                    continue
                va, vb = p[f"a_{prefix}"] or b"", p[f"b_{prefix}"] or b""
                total_a, total_b = total_a + len(va), total_b + len(vb)
                n = min(len(va), len(vb))
                base_undecided = sorted(
                    int(ob[1:]) for ob, o in rows_b.items() if o["kind"] == kind
                )
                if selecting:
                    idxs = [
                        i for i in base_undecided
                        if i < n and f.matches(rows_b[f"{prefix}{i}"])
                    ]
                    matched += len(idxs)
                elif va == vb:
                    # Same verdicts: only a reason can have changed.
                    idxs = base_undecided
                    matched += n
                else:
                    idxs = range(n)
                    matched += n
                for i in idxs:
                    was, now = rung_of[vb[i] & RUNG_BITS], rung_of[va[i] & RUNG_BITS]
                    if was == now != "undecided":
                        continue
                    ob = f"{prefix}{i}"
                    a_row, b_row = rows_a.get(ob), rows_b.get(ob)
                    was_reason = b_row["reason"] if b_row else None
                    now_reason = a_row["reason"] if a_row else None
                    transitions[(kind, was, now, was_reason, now_reason)] += 1
                    change = None
                    if was == "undecided" and now != "undecided":
                        change, out = b_row, discharged
                    elif now == "undecided" and was != "undecided":
                        change, out = a_row, regressed
                    if change is not None and len(out) < limit:
                        out.append(
                            {
                                **{
                                    k: p[k]
                                    for k in ("block", "pair", "direction", "pass", "before", "after")
                                },
                                "ob": ob,
                                "kind": kind,
                                "was": was,
                                "now": now,
                                "was_reason": was_reason,
                                "now_reason": now_reason,
                                "expr": change["expr"] if change else None,
                                "detail": a_row["detail"] if a_row else None,
                            }
                        )
        steps = self.query(
            "SELECT COUNT(*) AS shared, SUM(a_verified AND NOT b_verified) AS newly,"
            " SUM(b_verified AND NOT a_verified) AS lost FROM shared"
        )[0]
        hints = self.query(
            "SELECT hb.accepted AS was, ha.accepted AS now, hb.family, COUNT(*) AS n"
            " FROM shared p JOIN hints hb ON hb.step_id = p.b"
            " JOIN hints ha ON ha.step_id = p.a AND ha.col = hb.col"
            " WHERE ha.accepted != hb.accepted GROUP BY 1, 2, 3 ORDER BY n DESC"
        )
        sums = (
            "SUM(s.undecided) AS undecided, SUM(s.verified) AS verified,"
            " SUM(s.hints_accepted) AS hints_accepted, SUM(s.hints_rejected) AS hints_rejected,"
            " SUM(s.pinned) AS pinned, SUM(s.constants_solved) AS constants_solved"
        )
        counters = {
            side: self.query(f"SELECT {sums} FROM shared p JOIN steps s ON s.id = p.{col}")[0]
            for side, col in (("base", "b"), ("run", "a"))
        }
        step_changes = self.query(
            "SELECT * FROM shared WHERE a_verified != b_verified"
            " ORDER BY block, nnn, direction LIMIT ?",
            (limit,),
        )
        return Comparison(
            shared=steps["shared"],
            newly_verified=steps["newly"] or 0,
            no_longer_verified=steps["lost"] or 0,
            transitions=[
                {"kind": k, "was": w, "now": n, "was_reason": wr, "now_reason": nr, "n": c}
                for (k, w, n, wr, nr), c in transitions.items()
            ],
            matched=matched,
            totals=(total_a, total_b),
            discharged=discharged,
            regressed=regressed,
            hints=hints,
            counters=counters,
            step_changes=step_changes,
        )


@dataclass
class Comparison:
    shared: int  # steps both runs have (after the filters)
    newly_verified: int
    no_longer_verified: int
    # Obligations whose rung or undecided reason changed, and the still-undecided
    # ones: {kind, was, now, was_reason, now_reason, n}.
    transitions: list[dict]
    matched: int  # obligations matched by name (and by the base-side filters)
    totals: tuple[int, int]  # obligations on the shared steps: (run, base)
    discharged: list[dict]  # examples: undecided in base, discharged now
    regressed: list[dict]  # examples: discharged in base, undecided now
    hints: list  # (was, now, family, n) for hints whose verdict changed
    counters: dict  # "base" / "run" -> summed counters on the shared steps
    step_changes: list  # shared steps whose verified changed


@dataclass
class Filters:
    """What ``redesign db show`` narrows to; None means everything."""

    pass_: str | None = None
    direction: str | None = None
    block: str | None = None
    pair: str | None = None  # one step, as the sweep writes it: "002->003"
    kind: str | None = None
    reason: str | None = None  # a prefix: "nonlinear" matches "nonlinear, no match"
    shape: str | None = None  # a shape id (or a prefix of one)

    def steps(self, run_id: int) -> tuple[str, list]:
        """WHERE clause on ``steps s``."""
        conds, params = ["s.run_id = ?"], [run_id]
        for col, v in (
            ("pass", self.pass_),
            ("direction", self.direction),
            ("block", self.block),
            ("pair", self.pair),
        ):
            if v is not None:
                conds.append(f"s.{col} = ?")
                params.append(v)
        return " AND ".join(conds), params

    def undecided(self, run_id: int) -> tuple[str, list]:
        """WHERE clause on ``undecided o JOIN steps s``."""
        conds, params = self.steps(run_id)
        conds, params = [conds], list(params)
        for col, v, prefix in (
            ("kind", self.kind, False),
            ("reason", self.reason, True),
            ("shape", self.shape, True),
        ):
            if v is not None:
                conds.append(f"o.{col} LIKE ? ESCAPE '\\'" if prefix else f"o.{col} = ?")
                params.append(_like_prefix(v) if prefix else v)
        return " AND ".join(conds), params

    def selects_obligations(self) -> bool:
        return any(v is not None for v in (self.kind, self.reason, self.shape))

    def matches(self, o) -> bool:
        """The obligation filters, in Python, for an ``undecided`` row."""
        return (
            self.kind in (None, o["kind"])
            and (self.reason is None or o["reason"].startswith(self.reason))
            and (self.shape is None or (o["shape"] or "").startswith(self.shape))
        )


# ---------------------------------------------------------------- rows


def _undecided_row(
    step: int, ob: str, o: Obligation, cand: Circuit | None, shapes: dict
) -> tuple:
    expr = shape_id = None
    if o.key is not None:
        expr = render(o.key, o.kind)
        text = render(o.key, o.kind, rename=True)
        shape_id = hashlib.sha1(text.encode()).hexdigest()[:8]
        shapes[shape_id] = text
    elif cand is not None:
        # An opaque or unmapped column: show c itself, as the dump has it.
        expr = _raw(ob, o.kind, cand)
    if expr is not None and len(expr) > EXPR_CHARS:
        expr = expr[:EXPR_CHARS] + " …"
    return (
        step,
        ob,
        o.kind,
        o.reason,
        int(o.cached),
        int(o.via_mapping),
        expr,
        shape_id,
        o.detail or None,
    )


def _raw(ob: str, kind: str, cand: Circuit) -> str | None:
    i = int(ob[1:])
    try:
        if kind == "bus":
            return render(_bus_exact_key(cand.stateless[i]), kind)
        return render(canon_zero(cand.constraints[i]), kind)
    except (CanonError, IndexError):
        return None


def _counters(r: Report) -> dict[str, int]:
    """Report's int fields: premises expanded, hints accepted, pins, ..."""
    out = {}
    for f in fields(r):
        v = getattr(r, f.name)
        if type(v) is int and f.name.isidentifier():
            out[f.name] = v
    return out


def family(col: str) -> str:
    """A column's family, as in tools/hint-rejects: no @id, no trailing _<n>."""
    return re.sub(r"_\d+$", "", col.split("@")[0])


# ---------------------------------------------------------------- rendering keys


def render(key: tuple, kind: str = "constraint", rename: bool = False) -> str:
    """A lens canonical key as text; with ``rename``, columns become x0, x1, ...

    Renamed in order of first appearance, so obligations that differ only in
    their columns get the same text (their shape). Constants are kept.
    """
    names: dict[str, str] = {}

    def name(col: str) -> str:
        if not rename:
            return col
        return names.setdefault(col, f"x{len(names)}")

    if kind == "bus":
        bus, mult, args = key
        return f"bus {bus} mult {_lin(mult, name)} args [{', '.join(_lin(a, name) for a in args)}]"
    # canon_zero makes the constant term monic; as "= 0", flip the sign so the
    # first term shown is positive ("a*b - c - 1", not "-a*b + c + 1").
    first = next((c for atom, c in key if atom != ONE), 1)
    if first < 0:
        key = tuple((atom, -c) for atom, c in key)
    return _lin(key, name)


def _lin(lin: tuple, name) -> str:
    if not lin:
        return "0"
    # The constant last: "x - 1" reads better than "-1 + x".
    terms = [t for t in lin if t[0] != ONE] + [t for t in lin if t[0] == ONE]
    out = []
    for i, (atom, c) in enumerate(terms):
        if atom == ONE:
            body = str(abs(c))
        else:
            body = _atom(atom, name)
            if abs(c) != 1:
                body = f"{abs(c)}*{body}"
        if i == 0:
            out.append(f"-{body}" if c < 0 else body)
        else:
            out.append(f"- {body}" if c < 0 else f"+ {body}")
    return " ".join(out)


def _atom(atom: tuple, name) -> str:
    if atom[0] == "v":
        return name(atom[1])
    parts = []
    for f in atom[1]:
        single = len(f) == 1 and f[0][1] == 1 and f[0][0] != ONE and f[0][0][0] == "v"
        parts.append(_lin(f, name) if single else f"({_lin(f, name)})")
    return "*".join(parts)


# ---------------------------------------------------------------- identity


def _git() -> tuple[str | None, str | None, str | None]:
    """(commit, branch, hash of uncommitted changes under src/ or None)."""

    def git(*args: str) -> str:
        return subprocess.run(
            ["git", *args], cwd=VERIFIER_DIR, capture_output=True, text=True, check=True
        ).stdout

    try:
        commit = git("rev-parse", "--short", "HEAD").strip()
        branch = git("rev-parse", "--abbrev-ref", "HEAD").strip()
        diff = git("diff", "HEAD", "--", "src")
        new = git("ls-files", "--others", "--exclude-standard", "--", "src").split()
    except (OSError, subprocess.CalledProcessError):
        return None, None, None
    if not diff and not new:
        return commit, branch, None
    h = hashlib.sha1(diff.encode())
    for path in sorted(new):  # new files are part of what ran, too
        h.update(path.encode())
        h.update((VERIFIER_DIR / path).read_bytes())
    return commit, branch, h.hexdigest()[:10]


def _dumps_hash(directory: Path) -> str | None:
    if not directory.is_dir():
        return None
    h = hashlib.sha1()
    for p in sorted(directory.iterdir()):
        h.update(f"{p.name}:{p.stat().st_size}\n".encode())
    return h.hexdigest()[:10]


def _now() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def _like_prefix(s: str) -> str:
    return re.sub(r"([\\%_])", r"\\\1", s) + "%"
