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
    db, _, (run, _), (off, _) = recorded
    for s in _steps(db, run).values():
        n = Counter(
            (r["accepted"], r["agreed"])
            for r in db.query("SELECT * FROM hints WHERE step_id = ?", (s["id"],))
        )
        assert n[(0, 1)] == 0  # a rejected hint never agreed
        assert (n[(1, 0)] + n[(1, 1)], n[(0, 0)]) == (s["hints_accepted"], s["hints_rejected"])
        assert n[(1, 1)] == s["hints_agreed"]
    key = ("2100224", "002->003", "completeness")
    s = _steps(db, run)[key]
    # test_opcode_flags_pinned_by_one_hot has (6339, 4564) without rule C.
    assert (s["hints_accepted"], s["hints_rejected"]) == (8508, 2395)
    # Every pin has a hint that agrees: pins (one-hot, rule C) and constants
    # (x - c), all derived before the hints.
    assert s["hints_agreed"] == s["pinned"] + s["constants_solved"] == 7370
    o = _steps(db, off)[key]
    assert o["hints_agreed"] == o["constants_solved"] == 4111 and o["pinned"] == 0
    # Rejected there: mostly the shift chip's constants (rule C pins load/store).
    rejected = Counter()
    for r in db.hint_forms(run, Filters(pair="002->003"), accepted=False):
        rejected[r["form"]] += r["n"]  # summed over the reject kinds
    assert rejected == {"c": 2359, "y": 36}


SOLVER = {"passes": ["solver"], "directions": ("completeness",)}  # steps with hints


def test_schema_1_gains_the_agreed_bit_and_forms(tmp_path):
    path = tmp_path / "x.db"
    with SweepDB(path) as db:
        run, _ = _record_run(db, "keccak", ["2106332"], **SOLVER)
        # Back to schema 1: no agreed bit and no forms anywhere.
        db.con.execute("ALTER TABLE hints DROP COLUMN agreed")
        db.con.execute("ALTER TABLE hints DROP COLUMN form")
        db.con.execute("ALTER TABLE steps DROP COLUMN hints_agreed")
        db.con.execute("PRAGMA user_version = 1")
    with SweepDB(path) as db:
        assert db.query("PRAGMA user_version")[0][0] == 4
        old = db.query("SELECT COUNT(*), COUNT(agreed), COUNT(form) FROM hints")[0]
        assert old[0] > 0 and (old[1], old[2]) == (0, 0)
        assert db.runs()[0]["hints_agreed"] is None  # unknown, not 0
        again, _ = _record_run(db, "keccak", ["2106332"], **SOLVER)
        assert db.runs()[0]["hints_agreed"] is not None
        new = db.query(
            "SELECT COUNT(*), COUNT(form) FROM hints h JOIN steps s ON s.id = h.step_id"
            " WHERE s.run_id = ?",
            (again,),
        )[0]
        assert new[0] == new[1] > 0
        console = Console(record=True, width=200)
        show(db, again, Filters(), vs=run, console=console)
        assert "of them, agreed with a pin" in console.export_text()


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
    outcomes = {(r["was"], r["now"]) for r in c.hints}
    assert ("rejected", "agreed") in outcomes  # the pins let more hints through


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
        ({"hints": True}, ["Rejected hints by the form of t", "by form: x := c"]),
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
