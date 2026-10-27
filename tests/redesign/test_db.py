"""Sweeps recorded in SQLite: what is stored adds up, and the views render it."""

import argparse
import dataclasses
from collections import Counter

import pytest
from rich.console import Console

from src.lens.canon import canon_value, canon_zero
from src.lens.resolve import ResolveError
from src.redesign.check import check
from src.redesign.circuit import load_step
from src.redesign.cli import _pair
from src.redesign.corpus import _record, run_sweep
from src.redesign.db import RUNG_BITS, Filters, SweepDB, render
from src.redesign.dbview import show
from src.redesign.sweep import REASONS, Report


def _record_run(db, group, blocks, **kw):
    run = db.start_run(group, blocks=blocks, passes=kw.get("passes", ()))
    data = run_sweep(group, blocks, on_pair=lambda *a: db.add_pair(run, *a), **kw)
    db.finish(run, data["meta"])
    return run, data


@pytest.fixture(scope="module")
def recorded(tmp_path_factory):
    """One small block in full, and 2100224's solver steps with and without rule O."""
    db = SweepDB(tmp_path_factory.mktemp("db") / "sweeps.db")
    small = _record_run(db, "keccak", ["2106332"])
    solver = {"passes": ["solver"], "directions": ("completeness",)}
    on = _record_run(db, "keccak", ["2100224"], **solver)
    off = _record_run(db, "keccak", ["2100224"], use_one_hot=False, **solver)
    yield db, small, on, off
    db.con.close()


def _steps(db, run):
    return {(s["block"], s["pair"], s["direction"]): s for s in db.query(
        "SELECT * FROM steps WHERE run_id = ?", (run,)
    )}


def test_shape_ignores_column_names_but_not_constants():
    a = canon_zero([["a", "*", "b"], "-", ["c", "+", 1]])
    p = canon_zero([["p", "*", "q"], "-", ["r", "+", 1]])
    two = canon_zero([["p", "*", "q"], "-", ["r", "+", 2]])
    assert render(a) == "a*b - c - 1"
    assert render(a, rename=True) == render(p, rename=True) == "x0*x1 - x2 - 1"
    assert render(two, rename=True) != render(p, rename=True)
    bus = (3, canon_value(1), (canon_value(["x", "-", ["y", "*", 256]]), canon_value(8)))
    assert render(bus, "bus", rename=True) == "bus 3 mult 1 args [x0 - 256*x1, 8]"


def test_records_add_up(recorded):
    db, (run, data), _, _ = recorded
    steps = _steps(db, run)
    assert len(steps) == len(data["steps"]) == 2 * 40
    codes = {r["code"]: r["rung"] for r in db.query("SELECT * FROM rung_codes")}
    for rec in data["steps"]:
        s = steps[(rec["block"], rec["pair"], rec["direction"])]
        assert s["obligations"] == rec["obligations"] and bool(s["verified"]) == rec["verified"]
        # Every obligation is counted once by rung, and has one verdict byte.
        rungs = Counter()
        for r in db.query("SELECT * FROM rungs WHERE step_id = ?", (s["id"],)):
            rungs[(r["kind"], r["rung"])] += r["n"]
        assert sum(rungs.values()) == rec["obligations"]
        verdicts = Counter()
        for kind, col in (("constraint", "constraint_verdicts"), ("bus", "bus_verdicts")):
            verdicts.update((kind, codes[b & RUNG_BITS]) for b in s[col])
        assert verdicts == rungs
        # The undecided ones have a row each, with a documented reason and a text.
        rows = db.query("SELECT * FROM undecided WHERE step_id = ?", (s["id"],))
        undecided = sum(n for k, n in rec["categories"].items() if k.split("|")[1] == "undecided")
        assert len(rows) == s["undecided"] == undecided
        assert all(r["reason"] in REASONS and r["expr"] for r in rows)


def test_hint_verdicts_match_the_counters(recorded):
    db, _, (run, _), _ = recorded
    for s in _steps(db, run).values():
        n = Counter(
            r["accepted"]
            for r in db.query("SELECT accepted FROM hints WHERE step_id = ?", (s["id"],))
        )
        assert (n[1], n[0]) == (s["hints_accepted"], s["hints_rejected"])
    s = _steps(db, run)[("2100224", "002->003", "completeness")]
    assert (s["hints_accepted"], s["hints_rejected"]) == (6339, 4564)  # test_opcode_flags_...


def test_pass_filter(recorded):
    _, _, (_, data), _ = recorded
    assert data["steps"] and all(r["pass"] == "solver" for r in data["steps"])
    with pytest.raises(ResolveError, match="no step from pass nope"):
        run_sweep("keccak", ["2106332"], passes=["nope"])


def test_pair_filter(recorded):
    db, _, (on, _), (off, _) = recorded
    assert _pair("2 -> 3") == _pair("002->003") == "002->003"
    with pytest.raises(argparse.ArgumentTypeError):
        _pair("3")
    f = Filters(pair="002->003", kind="constraint")
    assert db.count_undecided(on, f) == (282, 1)  # test_opcode_flags_pinned_by_one_hot
    c = db.compare(on, off, f, limit=5)
    assert c.shared == 1 and {r["pair"] for r in c.discharged} == {"002->003"}


def test_compare_rule_o_off_then_on(recorded):
    db, _, (on, _), (off, _) = recorded
    f = Filters(kind="constraint")
    c = db.compare(on, off, f, limit=5)
    net = Counter()
    for t in c.transitions:
        if t["was"] == "undecided" and t["now"] != "undecided":
            net["discharged"] += t["n"]
        elif t["now"] == "undecided" and t["was"] != "undecided":
            net["regressed"] += t["n"]
    a, b = _steps(db, on), _steps(db, off)

    def und(s):
        return db.query(
            "SELECT COUNT(*) FROM undecided WHERE step_id = ? AND kind = 'constraint'",
            (s["id"],),
        )[0][0]

    assert net["discharged"] - net["regressed"] == sum(und(b[k]) - und(a[k]) for k in a)
    key = ("2100224", "002->003", "completeness")
    assert (und(b[key]), und(a[key])) == (1150, 282)  # test_opcode_flags_pinned_by_one_hot
    assert c.discharged and all(r["was"] == "undecided" for r in c.discharged)
    assert c.hints and any(r["now"] for r in c.hints)  # the pins let more hints through


def test_new_counter_becomes_a_column(tmp_path):
    @dataclasses.dataclass
    class Later(Report):
        rule_x_fired: int = 7

    (r,) = check("keccak", "2106332", "008", "009", ("completeness",))
    later = Later(**{f.name: getattr(r, f.name) for f in dataclasses.fields(r)})
    base = {"block": "2106332", "pair": "008->009", "before": "", "after": "", "pass": "p"}
    before, after = load_step("keccak", "2106332", "008"), load_step("keccak", "2106332", "009")
    with SweepDB(tmp_path / "x.db") as db:
        run = db.start_run("keccak")
        db.add_pair(run, [_record(base, later)], [later], before, after)
        assert db.query("SELECT rule_x_fired FROM steps")[0][0] == 7


def test_drop_and_interrupted_runs(tmp_path):
    with SweepDB(tmp_path / "x.db") as db:
        done, _ = _record_run(db, "keccak", ["2106332"], passes=["exec_bus"])
        cut = db.start_run("keccak")  # never finished
        assert db.run()["id"] == done  # the default is the latest finished run
        assert db.drop(done) and not db.drop(done)
        for table in ("steps", "rungs", "undecided", "hints", "unmapped"):
            assert db.query(f"SELECT COUNT(*) FROM {table}")[0][0] == 0
        assert db.run(cut)["finished"] is None
        with pytest.raises(LookupError):
            db.run()


@pytest.mark.parametrize(
    "kw, titles",
    [
        ({}, ["Passes (pipeline order)", "Steps not fully discharged"]),
        # "args [": brackets in the data are shown, not read as rich markup.
        ({"f": Filters(pass_="solver")}, ["Undecided obligations by reason", "args [", "hints"]),
        ({"f": Filters(reason="linear")}, ["undecided obligations in", "Obligations (first"]),
        ({"f": Filters(pair="013->014")}, ["Undecided obligations by reason", "pair 013->014"]),
        ({"hints": True}, ["Rejected hints by reason and column family"]),
        ({"vs": "off"}, ["Totals on the shared steps", "Discharged now", "switch one_hot: off -> on"]),
    ],
    ids=["overview", "pass", "reason", "pair", "hints", "vs"],
)
def test_views_render(recorded, kw, titles):
    db, _, (on, _), (off, _) = recorded
    kw = dict(kw)
    if kw.get("vs") == "off":
        kw["vs"] = off
    console = Console(record=True, width=200)
    show(db, on, kw.pop("f", Filters()), console=console, **kw)
    out = console.export_text()
    for title in titles:
        assert title in out
