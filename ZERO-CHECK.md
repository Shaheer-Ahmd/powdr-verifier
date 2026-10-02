# Solver-free zero-check gadget certificates

`zero-check.py` extends the M3 local-obligation checks with a specialized
checker for the unweighted `QuotientOrZero` gadget. It does not call SMT.
The default inputs are Keccak `2106332 008_trivial_simp → 009_rule_based`.

Both polarities are supported: the selector can be `c` or `1-c`.
Certificates include names of the corresponding ordinary and polarity
theorems for traceability. Acceptance uses the Python checks; it does not
invoke Lean or require a separate Lean checkout.

This document covers per-obligation M3 checking. The shared checker also
offers `require_complete_gadget=True` for callers that require all no-wrap
bounds and markers unused outside the old weighted constraint. That stricter
mode returns no claims if either condition is missing. The M3 commands below
use the per-obligation mode described in [M3-REDESIGN.md](M3-REDESIGN.md).

## Commands and result scope

From `verifier/`:

```bash
uv run python zero-check.py --reference-recv-bytes
uv run python zero-check.py --reference-recv-bytes --output /tmp/zero-check-evidence.json
uv run python -m pytest tests/test_zero_check.py -q
```

The output file must not already exist. `--before`, `--after`, and optional
`--substitutions` select other files. The default gadget needs no substitution
file. These commands do not modify the dumps or stage files.

The acceptance result is **0 residual local obligations in both directions**:

| Direction | Initial M3 residuals | After specialized checking |
|---|---:|---:|
| Completeness | 2 | 0 |
| Soundness | 5 | 0 |

This result is `conditional-local-closed`: the four canonical field values
received at reference memory bus row 33, arguments 2–5, are **explicitly
assumed to be bytes**. The flag authorizes the `reference-recv-bytes-v1`
contract in each direction. The checker validates the actual row, payload
expressions, and constant receive multiplicity; it does not prove the
environment contract. Each bound and its source appear in the output.

Without that contract:

```bash
uv run python zero-check.py
```

the checker leaves 1 completeness and 4 soundness residuals and exits 1.
It still proves the two unconditional polynomial identities. No missing bound
is silently invented. Direct constant-active OpenVM variable-range rows can
also supply bounds without the receive contract.

Exit 0 means both directions have zero **algebraic/stateless** residuals under
the reported assumptions. It does not certify stateful IO, general derived
metadata consistency, VM executions, or Keccak correctness. Incomplete mappings
have unknown (`null`) residual counts, never zero. Saved baseline measurements
are unchanged, but new dataset sweeps now enable the zero checker by default.
Use `--no-zero-check --no-polynomial-matching` to reproduce the original baseline, or add
`--reference-recv-bytes` to authorize byte assumptions explicitly:

```bash
uv run python m3-sweep.py keccak -j 2 --timeout 60 --sort residual --reference-recv-bytes
```

The sweep records proof reasons, certificates, and contract use in its reports.
The batch sweep also enables polynomial matching before the gadget rules;
overlapping identities may therefore be counted under `poly`, not `zero`.
Use `--no-polynomial-matching` to isolate the gadget checker's contributions.
Without the byte flag the real gadget keeps 1/4 residuals; with it, 0/0.
The checker is also integrated into the library's `cheap_sweep`
as an opt-in post-canonical stage:

```python
goals = cheap_sweep(
    reference, candidate, mapping,
    zero_check_direction=direction,  # "completeness" or "soundness"
    reference_recv_bytes=True,       # explicit external contract
)
```

The supplied mapping is reused, not reconstructed. Newly discharged obligations
retain the checked certificate and claim (including assumptions) in `goal.proof`.
With no options, `cheap_sweep` retains its baseline behavior. With a direction
but no receive contract, only unconditional or directly range-justified rules
apply. `definition_goals` are preserved and are not discharged by gadget rules.

`uv run python m3-example.py` enables the checker with
`reference_recv_bytes=False`. It prints one completeness residual and four
soundness residuals without granting a byte contract. Use
`uv run python zero-check.py --reference-recv-bytes` for the conditional
zero-residual demonstration.

## Checked theorem

All equations are over the fixed BabyBear prime field, `p = 2013265921`.
Write `c = cmp`, `S = sum(a_i)`, and `T = sum(a_i*v_i)`.

The recognized Before equations are `(1-c)*a_i = 0` for each limb and
`T-c = 0`. The After equations are `(1-c)*S = 0` and `f*S-c = 0`, with
one definition of `f`: `QuotientOrZero(c,S)`. The roles must be distinct
columns; `v_i` disappear and `f` is introduced. The first implementation
supports 2–64 unweighted, distinct limbs, not partially collapsed gadgets.

The no-cancellation rule uses canonical integer representatives:

```
0 <= a_i <= U_i,  sum(U_i) < p
---------------------------------
S = 0 in the field => every a_i = 0
```

The bound checker recognizes constant-active OpenVM bus 3 rows with constant
widths 0–25, or four-limb bus 1 receives under the explicit byte contract.
It checks each payload against its claimed column. Symbolic/disabled gates
are not accepted. For four bytes, `sum(U_i) = 1020 < p`. These canonical
representative bounds do not require the raw integer encoding of a column
to lie in `[0,p)`.

Completeness chooses `f = QuotientOrZero(c,S)`:

1. Summing the old individual zero equations gives `(1-c)*S = 0`.
2. If `S != 0`, the quotient definition gives `f*S = c`. If `S = 0`,
   no-cancellation makes every limb zero, hence `T = 0`, and the reference
   equation `T-c = 0` gives `c = 0`. The quotient also returns zero.

Soundness chooses every `v_i = f`:

1. Substitution and polynomial normalization turn `T-c` into `f*S-c`.
2. From `(1-c)*S = 0`, either `c = 1` or `S = 0`. In the first case each
   `(1-c)*a_i` vanishes; in the second no-cancellation makes every limb zero.

These rules do not need Booleanity of `c`. Any Boolean constraint present in
the actual input is still an obligation and is handled by the ordinary M3
checks. No unconditional cancellation of a `QuotientOrZero` denominator is used.

## Implementation and evidence

`src/verify/zero_check.py` contains three layers:

- `propose_certificates` searches definitions and normalized equations for
  possible gadgets. Variable names carry no special meaning.
- `check_certificate` independently checks the original equations and indices,
  field, input/mapping hashes, definition, witness choices, and bound sources.
  It never calls the recognizer. It returns only justified individual claims.
- `syntactic_sweep` builds the M2 map, runs M3 checks, and uses checked claims
  to discharge matching residuals. Every other local obligation is preserved.

Polynomial matching reuses the shared bounded sparse-polynomial implementation
in `polynomial_normalization.py` (2048-term budget), extracted from
`collapsed_witness.py`. It handles reordered/expanded terms
and signed/residue coefficients; quotient terms are checked by the dedicated
rule, not treated as polynomials. Scaled equations and more general recipes
are outside this initial recognizer. Unsupported patterns remain residual or
unmapped; invalid inputs/certificates raise errors, never a proof verdict.

The JSON report contains complete local obligations, initial/final residuals,
witnesses, certificates, checked claims, used proof links, source bounds,
authorized contracts, actual assumptions, and omitted stateful counts. A
certificate serialized to JSON can be passed back to `check_certificate` with
the original inputs and mapping; the caller must independently authorize the
receive-byte contract. A certificate cannot authorize its own assumptions.

The selected `f` must have exactly one definition. Other derived metadata is
not a general definition audit: dead helper records are not revived, and
additional metadata obligations remain outside this entry point's scope.
The old markers' additional uses are not ignored: they remain in the complete
local obligation list (or prevent mapping). Stateful uses still require IO work.

`tests/test_zero_check.py` checks the real acceptance counts, bounds/guard
rejection, changed equations and recipes, conflicting mappings, certificate
tampering, preserved extra obligations, renaming/reordering, explicit contract
authorization, and JSON certificate replay. Exhaustive arithmetic checks over
small prime fields exercise both theorem schemas without SMT. These tests
are not a Lean proof; the parser, polynomial arithmetic, rule implementation,
fixed prime, and supported OpenVM range semantics remain trusted.
