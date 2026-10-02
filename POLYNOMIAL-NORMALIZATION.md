# Shared bounded polynomial normalization

`src/verify/polynomial_normalization.py` owns the sparse-polynomial arithmetic
previously embedded in `collapsed_witness.py`, plus zero-equation scalar
normalization previously implemented in the residual classifier. The initial
extraction preserved behavior. A subsequent matching layer now uses it to
discharge M3 obligations; see the integration section below.

## API and scope

```python
from src.verify.polynomial_normalization import polynomial_key, zero_equation_key

expanded = [['x@0', '*', 'y@1'], '+', ['x@0', '*', 'z@2']]
factored = ['x@0', '*', ['y@1', '+', 'z@2']]
assert polynomial_key(expanded) == polynomial_key(factored)

x = polynomial_key('x@0')
twice_x = polynomial_key([2, '*', 'x@0'])
assert x != twice_x                         # different values / bus payloads
assert zero_equation_key(x) == zero_equation_key(twice_x)  # same zero equation
```

Keys are sorted `(monomial, coefficient)` tuples. A monomial is a sorted tuple
of column names; `()` denotes a constant monomial. The empty polynomial key
is zero. Coefficients are reduced modulo BabyBear, `2013265921`.

The module accepts integer constants, column names containing `@`, and the
existing APC arithmetic-list syntax (`+`, `-`, `*`, unary minus). It expands,
collects, cancels, and orders terms. It does not inspect circuits or buses,
discover witnesses, interpret recipes, invoke SMT, or discharge obligations.

`polynomial_key(expr, substitutions=None, *, field_prime=2013265921,
max_terms=None)` preserves the legacy one-pass substitution adapter. Supplied
RHS expressions are already reference-side expressions and are not substituted
again. Field configuration is explicit, but other fields are rejected in this
increment. Recipe lowering stays in adapters (the classifier and matching layer); general recipe
proofs stay outside the arithmetic engine. No cache is shared between callers.

`zero_equation_key(key, *, field_prime=2013265921)` takes a canonical key from
the same field and divides coefficients by the first nonzero coefficient. It
preserves only the equation's zero set, **not its expression value**. It must
not be used for bus payload equality. Zero remains zero.

## Limits and failure

The default remains 2,048 terms. Both intermediate term dictionaries and the
pre-expansion Cartesian product of multiplication operands are bounded.
The original evaluation order and conservative cutoff are preserved: a product
may exceed its bound even if eventual cancellation would shrink the result.
This is not a general AST-size, recursion-depth, time, or memory limit.

- Unsupported syntax raises `UnsupportedPolynomial`.
- Budget exhaustion raises its subclass `PolynomialBudgetExceeded`.
- Invalid field/budget configuration raises `ValueError`.

Existing callers that catch `UnsupportedPolynomial` still leave the operation
unresolved. No failure becomes zero or a proof. Explicit `max_terms` is the
supported per-call configuration; legacy imports of the function, exception,
and constants from `collapsed_witness` remain available. Mutating that module's
re-exported constants no longer configures the shared engine.

## Consumers and validation

- `collapsed_witness.py`: proposes uniform marker witnesses.
- `zero_check.py`: checks polynomial identities within gadget certificates.
- `../research/diagnostics/redesign/classify_residuals.py`: normalizes diagnostic
  expressions/bus fields and zero equations; recipe/table/affine logic stays there.
- `m3_sweep.py`: records the new transitive dependency's source hash.

Run the focused, solver-free suites from `verifier/`:

```bash
uv run python -m pytest tests/test_polynomial_normalization.py \
  tests/test_m3_sweep.py \
  tests/test_zero_check.py tests/lens/test_diff.py tests/lens/test_resolve.py -q
```

The optional `tests/test_residual_classification.py` belongs to the workspace
diagnostics and requires the sibling `../research/` scripts; it is not needed
for the verifier's standalone M3 checks.

Full-dataset regression uses a fresh sweep and classification, preserving the
classifier's source-hash checks (old manifests are never edited):

The following commands/evidence describe the historical extraction revision,
before polynomial matching was enabled. Current source hashes differ; for the
integrated implementation use the commands in the final section instead.

```bash
uv run python m3-sweep.py keccak -j 2 --timeout 60 \
  --output runs/polynomial-extraction-20260928-sweep
uv run python ../research/diagnostics/redesign/classify_residuals.py \
  runs/polynomial-extraction-20260928-sweep \
  --output runs/polynomial-extraction-20260928-classification-retry -j 2
uv run python ../research/diagnostics/redesign/compare_polynomial_extraction.py \
  runs/m3-sweep.pyvgk4o7 runs/polynomial-extraction-20260928-sweep \
  runs/residual-classification-20260927-refined \
  runs/polynomial-extraction-20260928-classification-retry \
  --output runs/polynomial-extraction-20260928-comparison.json
```

Output paths must be new. For subsequent repeats choose fresh paths consistently.
The comparison checks every direction record except timing fields, and every
classified residual including evidence, independently of worker completion
order. It also checks matching scope/budgets and the expected source-change set.

The initial `runs/polynomial-extraction-20260928-classification/` attempt was
blocked by the sandbox at multiprocessing forkserver socket creation. Its
partial artifacts are retained, not a completed classification. The `-retry`
directory uses the same command/budgets with approved process-startup access.

## Demonstrated result (2026-09-28)

The focused suites passed **137 tests**. The fresh 61-block sweep covered all
2,451 pairs / 4,902 directions in 356.56s (two workers, 60s per direction).
Classification covered all 185,052 residuals in 98.07s with two workers and
the original polynomial/affine bounds; no per-direction timeout or extra memory
cap was added to classification. These runs invoked no SMT.

`runs/polynomial-extraction-20260928-comparison.json` reports:

- All 4,902 sweep records identical after excluding only `seconds`, `timings`,
  and `worker_wall_seconds`. This includes residual indices, mapping metadata,
  statuses, input hashes, assumptions, and gadget certificates.
- All 185,052 classification records identical, including their evidence.
- Category counts identical: 143,219 concrete solver-free candidates and
  41,833 unresolved occurrences. These remain diagnostic categories.

The explicit-byte-contract zero-check demonstration remains 0/0 residuals,
saved in `runs/polynomial-extraction-20260928-zero-check.json`; the version of
`m3-example.py` used for that historical run also enabled the contract. The
current example leaves it disabled and reports the bound-dependent residuals.
Without the contract, the full sweep preserves those residuals.
The unchanged 116 unmapped and one unsupported directions remain uncounted.
No performance equivalence, new general M3 discharge, IO proof, or whole-circuit
equivalence is claimed by this extraction regression.

## M3 matching integration

The batch command now enables polynomial matching by default:

```bash
uv run python m3-sweep.py keccak -j 2 --timeout 60 --sort residual
# Pre-polynomial baseline, keeping the zero checker enabled:
uv run python m3-sweep.py keccak -j 2 --timeout 60 --no-polynomial-matching
```

At library level it remains opt-in: `cheap_sweep(..., polynomial_matching=True)`.
The order is canonical checks, polynomial matches, then configured zero-gadget
rules. Existing witnesses are reused. No SMT runs and no new assumptions are
granted. Existing byte contracts still require their explicit flag.

`polynomial_matching.py` adds five proof reasons:

- `polynomial-zero`: the mapped algebraic expression normalizes to zero.
- `polynomial-reference-match`: it equals an original reference polynomial.
- `nonzero-scale-reference-match`: it is a nonzero scalar multiple of one.
- `stateless-polynomial-reference-match`: bus ID, multiplicity, and every
  payload field match exactly after polynomial normalization.
- `stateless-polynomial-inactive`: the multiplicity normalizes to zero.

Only reference constraints are premises. Candidate constraints never justify
each other. Scalar normalization is never used for bus fields. Derived-definition
obligations and stateful IO are not processed by these new rules. Affine
combinations, Boolean facts, constant-table membership, and symbolic quotient
cancellation are not enabled here.

The recipe adapter folds Constant, constant-denominator QuotientOrZero (zero
denominator gives zero), and constant-guard IfEqZero. Other recipes remain
opaque, with structurally identical recipes sharing collision-free atoms in a
per-direction cache. Unsupported arithmetic, expansion budgets, or recursion
failures leave matches unavailable; malformed input still fails explicitly.

Every new discharge retains schema/field/budget, candidate kind/index, rule,
reference index where applicable, and nonzero scale where applicable. Batch
reports persist those records in `polynomial_proofs`, alongside the witness map
and input hashes. `check_polynomial_proof` / `check_polynomial_proofs` recheck
the specified claims from the original circuits and mapping without invoking
the matcher/search. Callers must bind inputs to report hashes; records cannot
authorize assumptions. This is trusted Python proof checking, not a Lean proof.

The batch manifest records the enabled flag and matching-module hash. JSON/CSV
reports distinguish polynomial discharges from zero-gadget discharges. The
counts can overlap conceptually: an identity previously discharged by the
zero-checker may now be attributed to the earlier polynomial stage.

Tests and the full-dataset proof audit:

```bash
uv run python -m pytest tests/test_polynomial_matching.py tests/test_m3_sweep.py \
  tests/test_zero_check.py tests/test_polynomial_normalization.py -q
uv run python ../research/diagnostics/redesign/audit_polynomial_sweep.py \
  runs/m3-sweep.nc6yza7c runs/m3-polynomial-enabled-20260928 \
  --output runs/m3-polynomial-enabled-20260928-audit.json
```

The audit requires a complete baseline and enabled run with matching input
hashes, selection and budgets. It checks every direction's coverage and mapping
metadata, no added residuals, attribution of every removed residual to saved
polynomial evidence, and replays all polynomial proofs. Output must be new.

### Measured integration result (2026-09-28)

Against the pre-integration `runs/m3-sweep.nc6yza7c` baseline, the complete
`runs/m3-polynomial-enabled-20260928` run reports:

| Metric | Before | Polynomial matching enabled |
|---|---:|---:|
| Algebraic residual occurrences | 139,182 | 24,071 |
| Stateless residual occurrences | 45,870 | 24,963 |
| Total residual occurrences | 185,052 | 49,034 |
| Directions with residuals | 1,479 | 631 |
| Directions with no local residuals | 3,306 | 4,154 |
| Uncounted directions | 117 | 117 |

This is a net reduction of 136,018 obligations (73.5%), exactly the earlier
normalization-category opportunity. The polynomial counter is 136,024 because
six identities previously handled by the zero-checker are now attributed to
polynomial matching; gadget discharges fall from 12 to 6. Neither run grants
the receive-byte contract. No new timeouts/errors or uncounted directions
appeared. The remaining 116 unmapped and one unsupported direction are not
treated as successes. These remain local-obligation results, not IO equivalence.

Validation: 161 targeted tests passed. The independent audit replayed all
136,024 saved polynomial proofs against the original inputs and witness maps,
confirmed every removed residual's attribution, and found no added residuals.
Its successful report is
`runs/m3-polynomial-enabled-20260928-audit.json`. No SMT solver was invoked.
