# M3 coverage: Keccak, 2026-09-26

The solver-free sweep examined all 61 available blocks: 2,451 consecutive
pass pairs, or 4,902 directional checks. There were no missing or duplicate
results, snapshot gaps, or input-hash changes. This measures local mapping
and cheap-check coverage, **not circuit equivalence**.

The full run took 159.2 seconds with two workers and a 10-second limit per
direction. Four directions on block 2100224 timed out; a targeted retry with
a 60-second limit completed them in 11.3–12.9 seconds each (24.8 seconds total).
No encoding or witness rules changed between the runs. The combined evidence
below retains both runs' provenance; it is not a single uniform-budget run.

## Results after the targeted retry

| Direction | No local residuals | Has local residuals | Incomplete mapping | Recursion limit |
|---|---:|---:|---:|---:|
| Completeness | 1,716 | 735 | 0 | 0 |
| Soundness | 1,590 | 744 | 116 | 1 |
| Total | 3,306 | 1,479 | 116 | 1 |

Both directions were supported for 2,334 pairs. Of those, 1,467 had no local
residuals in either direction. Unsupported directions have **unknown** residual
counts; they are not included as zero in the totals below.

| Direction | Counted directions | Algebraic total | Algebraic residual | Stateless total | Stateless residual |
|---|---:|---:|---:|---:|---:|
| Completeness | 2,451 | 478,476 | 70,279 | 421,484 | 28,529 |
| Soundness | 2,334 | 465,689 | 68,915 | 394,753 | 17,341 |

These are sums across directional checks, not distinct constraints in the
dataset. Residuals remain after mapping, canonical matching, trivial checks,
and sweep-local cache reuse. They are proof work, not demonstrated bugs.

## Unsupported cases

All 117 uncounted directions are soundness checks:

| Pass transition | Count | Observed limitation |
|---|---:|---|
| `inlining -> remove_disconnected` | 57 | Missing witnesses; examples include timestamp-decomposition helpers. |
| `solver -> remove_trivial` | 56 | Missing witnesses; examples include previous timestamps and their decomposition helpers. |
| `remove_disconnected -> rule_based` | 2 | Unmapped inverse markers in blocks 2100224 and 2103472. |
| `remove_trivial -> remove_free` | 1 | Unmapped columns in block 2100224, including shift-carry helpers. |
| `low_degree_bus -> inlining` | 1 | Block 2100224, 045->046: recursion limit during mapping. |

Every affected block/pass and the missing-column names are retained in
`results.jsonl`; `results.csv` supplies a flat index of all directions.
The existing mapping gaps and recursion limitation were recorded, not fixed.

The four timeout retries were 2100224 000->001 and 001->002 in both directions.
They timed out in **cheap checks, not Z3**. After retry, 000->001 has 1,352
forward algebraic residuals and no reverse local residuals; 001->002 has
9,150 algebraic and 1,986 stateless residuals in each direction.

The median recorded direction took 0.014 seconds; the 95th percentile was
0.205 seconds. These are observations under the recorded worker settings,
not performance guarantees.

## Commands and evidence

The combined report is
[runs/m3-sweep-combined.z3_k__jd](runs/m3-sweep-combined.z3_k__jd/).
Its manifest links the original
[full sweep](runs/m3-sweep.hp9pdcdc/) and [retry](runs/m3-sweep.zlur_34u/),
with source/input hashes checked before replacing the four timeout records.

```bash
# Inspect the existing report without recomputing.
uv run python m3-sweep.py --report runs/m3-sweep-combined.z3_k__jd --only-unsupported --sort block --limit 0
uv run python m3-sweep.py --report runs/m3-sweep-combined.z3_k__jd --sort residual --limit 20

# New complete sweep with additional headroom for the largest block.
uv run python m3-sweep.py keccak -j 2 --timeout 60 --sort residual
```

Baseline commit: `19a7485a8b19207eeb3abfffb467cd6b4629d941`, plus the
working-tree recipe support in shared M3 modules and the new sweep command.
The run manifests identify exact source hashes; this is not a clean-commit-only
measurement. Python 3.14.7; BabyBear; no solver calls, no definition audit,
no stateful IO proof, and no additional per-worker memory cap.

Regression validation: 70 tests passed, including the 17 new sweep tests,
existing lens tests, gadget checks, and derived-definition regressions.
The only warning was the existing semver deprecation warning.
