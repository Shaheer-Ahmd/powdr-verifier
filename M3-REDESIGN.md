# Verifier redesign through M3

The redesign separates **choosing witness values** from **proving that those
values satisfy the destination circuit**. M1 loads and compares circuit
snapshots, M2 constructs explicit variable mappings, and M3 checks individual
obligations without a solver. This document includes the polynomial matcher
and zero-gadget checker integrated into M3, and stops at the residuals they
leave behind.

An unresolved obligation means more proof work is needed. Even when all local
obligations are discharged, these stages do not establish stateful IO
equivalence, general derived-definition consistency, or correctness of the
program against a specification.

Contents: [Setup](#setup-and-inputs) · [M0](#m0-existing-baseline) ·
[M1](#m1-partition-and-compare) · [M2](#m2-build-witness-mappings) ·
[M3](#m3-check-local-obligations) · [Polynomial matching](#polynomial-matching) ·
[Zero gadget](#zero-gadget-checking) · [Sweeps](#batch-sweeps-and-reports) ·
[Validation](#validation) · [Files](#file-guide).

## Pipeline and proof directions

```text
Before and After snapshots
    -> M1: partition constraints and compare snapshots
    -> M2: map candidate columns to reference expressions
    -> M3: substitute that mapping into candidate obligations
         -> canonical checks
         -> optional polynomial matching
         -> optional zero-gadget rules
    -> discharged obligations with reasons, or explicit residuals
```

Each pair is checked in both directions:

| Direction | Reference supplies premises | Candidate supplies goals |
|---|---|---|
| Completeness | Before | After |
| Soundness | After | Before |

A mapping gives every live candidate column an expression over reference
columns. All mapped candidate obligations must then follow from the reference
constraints and any explicitly reported assumptions. A complete mapping is
necessary for these checks, but is not itself a proof.

## Setup and inputs

Run the commands from the `verifier/` repository. Install the Python environment
as described in [README.md](README.md); Python 3.13 or newer is required.

```bash
uv sync --group dev
```

With an existing environment, `.venv/bin/python` can replace `uv run python`.
The M1–M3 commands do not invoke an SMT solver or the Rust simplifier.

Examples use existing dumps under `powdr-dumps/guest-keccak/`, especially:

```text
apc_candidate_2106332_008_trivial_simp.json
apc_candidate_2106332_009_rule_based.json
apc_candidate_2106332_substitutions.json
```

Dumps are generated inputs and are ignored by Git. If they are absent, the
existing generation command is `uv run python orchestrate.py powdr-guest
guest-keccak`; it requires the full powdr/Rust setup from README.md. Synthetic
tests can run without dumps; tests that require the real fixtures skip when
those files are missing.

## M0 Existing baseline

M0 uses the existing tools to inspect a rewrite and establish a baseline. It
does not introduce a redesigned proof stage. Inspect the example pair with:

```bash
uv run lens diff keccak 2106332 008 009
uv run membus align keccak 2106332 008 009 --no-assume-is-valid
```

The optional legacy verification command is:

```bash
uv run python orchestrate.py verify guest-keccak 2106332 8 \
  --solver z3-5.1.0 --memory-encoding interface \
  --no-interface-ignore-checks -j 1
```

Unlike M1–M3, this runs encoding, simplification, and solving and needs the
configured executables. Its `data/` and `reports/` outputs may replace earlier
artifacts, so preserve evidence before rerunning. `main.py verify` alone
generates verification conditions; command completion is not a solver verdict.

## M1 Partition and compare

`partition_circuit` validates the snapshot and separates its contents while
preserving original indices and duplicates:

| Kind | Contents | Treatment through M3 |
|---|---|---|
| Algebraic | Expressions constrained to equal zero | Mapped and checked |
| Stateless | Bus IDs 2, 3, 6, 7 | Multiplicity and payloads compared |
| Stateful | Bridge and memory, IDs 0 and 1 | Preserved and counted, not proved |
| Derived metadata | Helper definitions | Used as witness recipes, not automatically asserted |

Lens compares canonical expression keys and reports removed, added, and
similarity-paired changed entries. A `changed` pair is a useful comparison,
not an equality proof. The `build_diff` API supports explicit cross-format
comparison with `allow_cross_format=True`; the default rejects mixed formats.

```bash
uv run python m1-builddiff.py
uv run python m1-partition.py
uv run python -m pytest tests/lens/test_diff.py tests/lens/test_resolve.py -q
```

The first two commands exercise the real 2106332 and 2099512 fixtures as well
as synthetic format and validation cases.

## M2 Build witness mappings

`build_mapping` resolves each live candidate column using a same-name reference
column, then a derived recipe, then substitution metadata. It expands recipe
dependencies recursively. Missing sources, cycles, and unsupported recipes
remain explicit mapping failures.

For a collapse such as the one below, old helpers may have no exported reverse
recipe:

| Before | After |
|---|---|
| `sum(a_i * inv_i) - c = 0` | `f * sum(a_i) - c = 0` |
| Separate `inv_i` helpers | `f := QuotientOrZero(c, sum(a_i))` |

Completeness can use the new helper's recipe. For soundness,
`add_collapsed_witnesses` tries one reference column as the common value of
multiple missing helpers. It accepts the first trial whose substituted
polynomial equals a reference polynomial. For this gadget, every `inv_i := f`
makes the weighted equation match. Other constraints still require checking.

Inspect both mappings without running a proof stage:

```bash
uv run python - <<'PY'
from pathlib import Path
from src.lens.loader import load
from src.verify.witness_mapping import build_mapping
from src.verify.collapsed_witness import add_collapsed_witnesses

root = Path('powdr-dumps/guest-keccak')
before = load(root / 'apc_candidate_2106332_008_trivial_simp.json')
after = load(root / 'apc_candidate_2106332_009_rule_based.json')
subs = load(root / 'apc_candidate_2106332_substitutions.json')
for direction, ref, cand in [('completeness', before, after),
                             ('soundness', after, before)]:
    mapping, proposals = add_collapsed_witnesses(
        ref, cand, build_mapping(ref, cand, subs))
    print(direction, 'total:', mapping.total)
    print('witnesses:', mapping.witnesses)
    print('unresolved:', mapping.unresolved)
    print('collapse proposals:', proposals)
PY
```

Mappings contain only reference-side expressions. Substitution into goals is
simultaneous: a replacement expression is not recursively substituted again.

## M3 Check local obligations

`cheap_sweep` substitutes the mapping into candidate algebraic constraints and
stateless bus rows. Its baseline checks are a per-sweep cache, triviality,
and canonical equality with reference constraints or rows. Stateless keys
include the bus ID, multiplicity, and every payload field.

The library keeps extensions opt-in:

```python
goals = cheap_sweep(
    reference, candidate, mapping,
    polynomial_matching=True,
    zero_check_direction=direction,  # completeness or soundness
    reference_recv_bytes=False,
)
residuals = [(g.kind, g.index) for g in goals if g.status == 'residual']
```

With no keyword options, `cheap_sweep` performs only the baseline canonical
checks. In contrast, the batch CLI enables polynomial and zero-gadget checks
by default, without assuming receive payloads are bytes.

Run the canonical-only baseline on one pair:

```bash
uv run python m3-sweep.py keccak 2106332 --from-step 8 --to-step 9 \
  --no-polynomial-matching --no-zero-check -j 1 --timeout 60
```

For this pair it leaves algebraic indices 14 and 15 in completeness, and
9 through 13 in soundness. The example below additionally enables the zero
checker, but grants no byte contract and leaves indices 15 and 9 through 12:

```bash
uv run python m3-example.py
```

The example does not enable the separate general polynomial-matching stage.
Each obligation records its original and mapped form, status, and reason.
Polynomial and gadget discharges also retain replayable proof evidence.

## Polynomial matching

`polynomial_key` expands arithmetic, collects monomials, reduces coefficients
modulo BabyBear (`p = 2013265921`), removes zero coefficients, and sorts the
result. Thus `f*(a0+a1)` and `a0*f+a1*f` have identical keys. A monomial is a
tuple of sorted column names; repeated factors represent powers. Constants
use the empty monomial, and the zero polynomial has an empty key.

```bash
uv run python - <<'PY'
from src.verify.polynomial_normalization import polynomial_key
print(polynomial_key([['x@0', '*', 'y@1'], '-', [2, '*', 'z@2']]))
PY
```

The output is `((('x@0', 'y@1'), 1), (('z@2',), 2013265919))`.

The matcher discharges an algebraic goal if it is identically zero, equals
a reference polynomial, or is a nonzero scalar multiple of one. Only the
last case uses `zero_equation_key`: equation scaling is never used to compare
bus values. Stateless rows discharge on exact polynomial equality of all
fields or an identically zero multiplicity.

The recipe adapter folds supported constant cases and treats other recipes
as opaque variables. It does not cancel symbolic quotient denominators.
The default expansion budget is 2,048 terms; unsupported arithmetic or a
budget failure leaves the goal unresolved by this stage.

To isolate this stage from the gadget rules:

```bash
uv run python m3-sweep.py keccak 2106332 --from-step 8 --to-step 9 \
  --no-zero-check -j 1 --timeout 60
uv run python -m pytest tests/test_polynomial_normalization.py \
  tests/test_polynomial_matching.py -q
```

The same arithmetic is used earlier during collapsed-witness discovery and
inside gadget checks. `--no-polynomial-matching` disables the general discharge
stage, not those internal uses. See
[POLYNOMIAL-NORMALIZATION.md](POLYNOMIAL-NORMALIZATION.md) for the APIs and
`check_polynomial_proofs` replay requirements.

## Zero gadget checking

Write `S = sum(a_i)` and `T = sum(a_i*inv_i)`. The supported pattern is:

| Before | After |
|---|---|
| `(1-c)*a_i = 0` for each limb | `(1-c)*S = 0` |
| `T-c = 0` | `f*S-c = 0` |
| Individual markers | `f := QuotientOrZero(c,S)` |

The selector may also be `1-cmp`, covering the opposite polarity. Recognition
supports 2–64 distinct unweighted limbs.

`propose_certificates` locates the equations, variable roles, recipe, and
possible bounds. `check_certificate` independently validates the input hashes,
equations, supplied witness map, and bound sources. `discharge_zero_checks`
then attaches justified claims to the corresponding remaining obligations.

Completeness uses `f := QuotientOrZero(c,S)`. Summing Before's individual zero
equations gives After's sum equation. For the weighted equation, a nonzero
`S` permits division; when `S = 0`, no-cancellation bounds force all limbs to
zero, so Before's weighted equation forces `c = 0`.

Soundness uses every `inv_i := f`, making the weighted equations identical.
For each individual zero equation, `(1-c)*S = 0` implies either `c = 1`, when
the product is already zero, or `S = 0`, when the same bounds force every
limb to zero. The required condition is:

```text
0 <= canonical(a_i) <= U_i, and sum(U_i) < p
    implies: sum(a_i) = 0 in the field => every a_i = 0
```

Bounds must be justified on the reference side of the current direction.
Supported sources are constant-active variable-range rows and explicitly
authorized memory-receive byte contracts. Four bytes give `sum(U_i)=1020<p`.
The memory contract is an assumption about the environment, not a theorem
proved by examining the receive row.

The standalone checker uses 2106332 008->009 by default:

```bash
uv run python zero-check.py
uv run python zero-check.py --reference-recv-bytes
```

The first command intentionally exits 1 with residuals; the second exits 0
with conditional local closure. `--before`, `--after`, and `--substitutions`
select other inputs. Save complete evidence to a file that does not yet exist:

```bash
uv run python zero-check.py --reference-recv-bytes \
  --output /tmp/zero-check-m3-evidence.json
```

The three modes below isolate the zero checker's contribution to the pair:

```bash
uv run python m3-sweep.py keccak 2106332 --from-step 8 --to-step 9 \
  --no-polynomial-matching --no-zero-check -j 1 --timeout 60
uv run python m3-sweep.py keccak 2106332 --from-step 8 --to-step 9 \
  --no-polynomial-matching -j 1 --timeout 60
uv run python m3-sweep.py keccak 2106332 --from-step 8 --to-step 9 \
  --no-polynomial-matching --reference-recv-bytes -j 1 --timeout 60
```

| Mode | Completeness residuals | Soundness residuals |
|---|---:|---:|
| Canonical checks only | 2 | 5 |
| Plus zero checker, no byte contract | 1 | 4 |
| Plus zero checker and explicit byte contract | 0 | 0 |

These are local counts. The last row is conditional on the reported contract.
The checker applies fixed mathematical rules in trusted Python; it does not
invoke SMT or Lean. Missing bounds leave the bound-dependent rules unavailable.
See [ZERO-CHECK.md](ZERO-CHECK.md) for certificate details.

## Batch sweeps and reports

The sweep checks adjacent numbered snapshots in both directions. It reports
missing steps rather than comparing across a gap, and excludes optimizer
auxiliary dumps and substitution files from the snapshot inventory.

```bash
# One block, every available adjacent pair.
uv run python m3-sweep.py keccak 2106332 -j 2 --timeout 60

# Every Keccak block and adjacent pair, with default solver-free extensions.
uv run python m3-sweep.py keccak -j 2 --timeout 60 --sort residual

# Every group under powdr-dumps/.
uv run python m3-sweep.py all -j 2 --timeout 60
```

`--timeout` is a wall-time budget per direction, not a solver timeout. The
default is 10 seconds; the commands above explicitly allow 60. `--limit`
limits displayed rows only, never the work performed. Add
`--reference-recv-bytes` only when intentionally granting that contract.

Each run creates a fresh `runs/m3-sweep.*` directory. `--output PATH` selects
another new directory; existing output directories are rejected.

| Artifact | Contents |
|---|---|
| `manifest.json` | Inputs, source hashes, field, flags, assumptions, worker count, and budgets |
| `results.jsonl` | Per-direction mappings, counts, residual indices, proofs, assumptions, and errors |
| `results.csv` | Flat per-direction summary |
| `summary.json` | Coverage and aggregate obligation counts |

Set `RUN_DIR` to the directory printed by a completed run and inspect it
without rerunning verification:

```bash
RUN_DIR=runs/m3-sweep.REPLACE_WITH_ACTUAL_RUN
uv run python m3-sweep.py --report "$RUN_DIR" --sort residual --limit 20
uv run python m3-sweep.py --report "$RUN_DIR" --only-unsupported --limit 0
```

`no-local-residuals` means all counted local goals were discharged under the
reported assumptions. `local-residuals` means some still need proof. An
unmapped, unsupported, timed-out, or failed direction has unknown counts where
checking could not finish; it is never counted as zero residuals. The CLI's
successful exit is not a whole-circuit equivalence verdict.

Historical inventory and normalization measurements are in
[M3-COVERAGE.md](M3-COVERAGE.md) and
[POLYNOMIAL-NORMALIZATION.md](POLYNOMIAL-NORMALIZATION.md). They describe
specific source/input versions; they are not results of a new sweep.
[RESIDUAL-CLASSIFICATION.md](RESIDUAL-CLASSIFICATION.md) records a diagnostic
analysis of an earlier residual set. Its workspace scripts and saved runs
are optional evidence, not runtime dependencies of M3.

## Validation

Run the self-contained M3 suites and existing lens regressions:

```bash
uv run python -m pytest \
  tests/test_polynomial_normalization.py tests/test_polynomial_matching.py \
  tests/test_zero_check.py tests/test_m3_sweep.py tests/test_m3_display.py \
  tests/lens/test_diff.py tests/lens/test_resolve.py -q
```

These cover arithmetic, proof replay and tampering, explicit contract use,
preservation of unrelated obligations, inventory, worker isolation, and report
formatting. Real-pair tests use the local dumps; synthetic tests do not require
them. Solver-free acceptance does not cover stateful IO or general definition
auditing.

## File guide

| File | Responsibility |
|---|---|
| `src/lens/loader.py`, `src/lens/diff.py` | Load and compare dumps |
| `src/verify/circuit_partition.py` | Validate and partition constraints, buses, and metadata |
| `src/verify/witness_mapping.py` | Resolve candidate witnesses into reference expressions |
| `src/verify/collapsed_witness.py` | Propose uniform collapsed-helper mappings |
| `src/verify/cheap_obligations.py` | Enumerate local goals, apply mappings, and orchestrate cheap checks |
| `src/verify/polynomial_normalization.py` | Canonical sparse-polynomial arithmetic |
| `src/verify/polynomial_matching.py` | General polynomial discharge and proof replay |
| `src/verify/zero_check.py` | Gadget discovery, independent certificate checking, and discharge |
| `src/verify/m3_sweep.py`, `src/verify/m3_display.py` | Batch execution, saved evidence, and display |
| `m1-builddiff.py`, `m1-partition.py` | M1 acceptance examples |
| `m3-example.py` | Minimal mapping and zero-check example without a byte contract |
| `m3-sweep.py`, `zero-check.py` | Batch and standalone CLI entry points |

Some shared APIs retain optional hooks for later stages, such as supplied
definition goals and stricter whole-gadget checking. The commands in this
document stop at M3 and do not run those later verification stages.
