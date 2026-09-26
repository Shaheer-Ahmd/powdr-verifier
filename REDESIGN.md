# Verifier redesign: M0–M3

The redesign separates **choosing a variable mapping** from **checking each
constraint**. Through M3, the new components load and compare circuits,
construct explicit witnesses, and discharge obligations that can be checked
without a solver. Remaining obligations are reported, not proved. These
components do not replace the existing verification pipeline or include
stateful IO checks.

The commands below use `verifier/` as the working directory and Keccak
snapshots under `powdr-dumps/guest-keccak/`. Environment setup is described
in [README.md](README.md); the existing verification pipeline also requires
the configured solver and simplifier executables.

## Existing verification baseline (M0)

M0 established a baseline using the existing verifier on the gadget rewrite
`2106332 008->009`; it introduced no new verification component. The following
commands expose the circuit diff, memory alignment, and baseline verification:

```bash
uv run lens diff keccak 2106332 008 009
uv run membus align keccak 2106332 008 009 --no-assume-is-valid
uv run python orchestrate.py verify guest-keccak 2106332 8 \
  --solver z3-5.1.0 --memory-encoding interface \
  --no-interface-ignore-checks -j 1
```

The orchestrator runs encoding, simplification, and solving; `main.py verify`
alone generates verification conditions. Both soundness and completeness
checks returned UNSAT under the selected encoding. Results are recorded in
`data/` and `reports/`, where reruns can replace earlier artifacts. The
underlying concepts are described in [DEVELOPER.md](DEVELOPER.md#core-concepts).

## Circuit partitioning and comparison (M1)

The new partitioner separates each dump into algebraic constraints, stateless
table lookups (bus IDs 2, 3, 6, 7), and stateful memory/bridge interactions
(IDs 1, 0). Original indices, duplicates, and derived-column metadata are
preserved; malformed inputs and unsupported bus IDs are rejected.

The existing `lens` canonical-key diff is reused for circuit comparison.
`build_diff` now supports opt-in cross-format comparison through
`allow_cross_format=True`; it remains blocked by default. Similarity-paired
`changed` entries are **not** equality proofs.

Regression checks for the diff and partitioner:

```bash
uv run python m1-builddiff.py
uv run python m1-partition.py
```

On `2099512 014->015`, the diff identifies 33 removed zero constraints and no unmatched
After constraints. `2106332 008->009` has two unmatched After constraints:
one `added` plus the After half of one `changed` pair.

## Explicit variable mappings (M2)

The mapping distinguishes a **reference** circuit whose constraints provide
premises from a **candidate** circuit whose mapped constraints become proof
obligations. Completeness uses Before as reference and After as candidate;
soundness swaps them.

`build_mapping` assigns each live candidate column a reference-side expression:
same-name first, then the first derived definition, then a substitution.
Dependencies are resolved recursively; missing sources, cycles, and unsupported
recipes remain explicit failures. Live columns come from constraints and all
buses, not unused metadata alone.

`add_collapsed_witnesses` handles the gadget's reverse mapping: the four removed
inverse markers can all use After's `free_var_123@123`. It checks a polynomial
pattern to propose witnesses; it does **not** prove the other constraints.

A total mapping covers every live candidate column using only reference
columns. For the gadget, completeness maps 60/60 columns and soundness 63/63
after the collapse proposal. Mapping expressions were also compared with the
existing verifier's Skolem pins across five pairs in both directions,
composing dependent pins before comparison. Mapping totality alone does not
establish that agreement or equivalence.

## Solver-free obligation checks (M3)

The cheap-check stage substitutes the mapping into candidate algebraic
constraints and stateless rows. Each goal is checked against a sweep-local
cache, tested for triviality, then compared canonically with reference
obligations. Bus keys retain multiplicity and payload. Quotient recipes remain
opaque for canonical matching, and unsupported syntax fails explicitly.
Stateful rows are excluded from these local goals.

The minimal API example, [m3-example.py](m3-example.py), loads the gadget pair,
builds mappings in both directions, and prints the residual obligations without
running a solver:

```bash
uv run python m3-example.py
```

For the gadget, the residuals are algebraic indices **14, 15** for completeness and
**9, 10, 11, 12, 13** for soundness; all stateless goals discharge cheaply.
The no-op `2106332 007->008` and trivial-removal `2099512 014->015` pairs have
no local residuals in either direction. A residual means “needs proof”, not
“optimizer bug”. Even an empty local residual set says nothing yet about IO.

## File guide

| File | Purpose through M3 |
|---|---|
| `src/lens/loader.py` | Load JSON, identify its representation, unwrap the machine. |
| `src/lens/diff.py` | Canonical keys and multiset diff; M1 adds opt-in cross-format comparison. |
| `src/verify/circuit_partition.py` | Validate and separate algebraic, stateless, and stateful groups. |
| `src/verify/witness_mapping.py` | Find live columns, resolve witness recipes, report sources and gaps. |
| `src/verify/collapsed_witness.py` | Propose uniform witnesses for the collapsed inverse-marker pattern. |
| `src/verify/cheap_obligations.py` | Apply witnesses and classify local goals as discharged or residual. |
| `m1-builddiff.py`, `m1-partition.py` | Runnable M1 acceptance and input-validation checks. |
| `m3-example.py` | Minimal M2–M3 API usage for the gadget pair, reporting residuals in both directions. |

The original M2/M3 diagnostic scripts were temporary `/tmp` files, not
repository test entry points. `m3-example.py` uses the M3 API
without depending on those temporary paths. Later recipe/definition-audit
extensions to shared modules are outside this guide. M4 adds solver checks
for residuals; M5 adds stateful IO obligations.
