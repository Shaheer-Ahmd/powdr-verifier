# Classification of remaining Keccak residuals

Analysis date: 2026-09-27. Source: `runs/m3-sweep.pyvgk4o7`, the complete
61-block, 2,451-pair, 4,902-direction sweep with the zero checker enabled and
**no receive-byte contract granted**. Its 12 unconditional gadget discharges
are already excluded from the residuals classified here.

The analysis covers **185,052 residual occurrences**: 139,182 algebraic and
45,870 stateless. Repeated obligations across passes/directions count separately;
these are not counts of unique equations. The 116 unmapped directions and one
recursion-limit direction are uncounted and excluded, not treated as zero.

No SMT ran, and no production discharges or verdicts were changed. The exact
categories below identify checked diagnostic opportunities for future proof
rules; they are not a newly integrated equivalence result.

## Results

### Concrete solver-free discharge candidates: 143,219 (77.4%)

| Category | Count | Evidence checked |
|---|---:|---|
| Algebraic polynomial equals a reference polynomial | 99,734 | Expand, collect monomials, reduce coefficients modulo BabyBear. |
| Algebraic polynomial is identically zero | 14,534 | Normalized polynomial is empty, e.g. `x - x`. |
| Equation differs by a nonzero constant scale | 843 | Leading-coefficient normalization and recorded reference/scale. |
| Stateless payload and multiplicity polynomial match | 20,907 | Same bus ID and equal normalized multiplicity/all arguments. |
| Affine combination of reference equations | 2,656 | Sparse elimination followed by independent replay of the recorded combination. |
| Constant PC lookup is a valid program row | 2,380 | Exact row membership in the hash-verified base instruction table. |
| Constant bitwise lookup is valid | 1,208 | Concrete byte bounds and XOR/range-row predicate. |
| Constant variable-range lookup is valid | 948 | Concrete value is below the supported power-of-two bound. |
| Conditional recipe is Boolean-valued | 9 | Both branches return 0/1; Boolean polynomial reduction closes the goal. |

The first four categories total **136,018**. They need no new gadget-specific
range assumptions. Polynomial normalization is therefore the largest measured
opportunity, not additional quotient pattern recognition.

Examples (column suffixes abbreviated below):

- `2099512 002->003`, completeness constraint 137: `t1 - (t0 + 3)` and
  `-t0 + t1 - 3` are the same polynomial, but have different current canonical keys.
- `2099532 013->014`, soundness constraint 31: mapped expression `t0 - t0`
  is identically zero.
- `2099532 012->013`, completeness constraint 33: the goal is `a`, while
  the reference equation is `-a = 0`.
- `2099512 000->001`, completeness constraint 136: the PC-step goal is
  reference constraint 58 minus reference constraint 23.
- `2099532 002->003`, completeness bitwise row 0: `(3,3,0,1)` is the valid
  XOR row `3 XOR 3 = 0`.
- `2099512 005->006`, soundness range row 56: checking 32 against an
  8-bit bound is a concrete true fact.
- `2106368 016->017`, soundness constraint 10: after substitution,
  `q*(q-1)=0` with `q=IfEqZero(a,0,1)`. Either branch makes it zero.

## Further reasoning needed: 41,833

| Category | Count | What the classification establishes |
|---|---:|---|
| Affine context unresolved | 17,050 | Linear goal not matched or derived by the bounded affine-only analysis. |
| Nonlinear context unresolved | 4,316 | Polynomial goal not closed by the implemented diagnostic rules. |
| Same lookup payload, different activation | 10,596 | Payload matches; enabledness/multiplicity still differs. |
| Bitwise table semantics unresolved | 5,439 | No exact row match or concrete table evaluation closed it. |
| Variable-range semantics unresolved | 4,366 | Symbolic range implication remains. |
| PC lookup semantics unresolved | 21 | Symbolic instruction fields remain. |
| Tuple-range semantics unresolved | 5 | Symbolic tuple membership remains. |
| Recognized zero gadget without bound evidence | 30 | Existing pattern checked, but no-cancellation premises are unavailable in this run. |
| Other symbolic quotient recipes | 10 | Quotient-containing goals outside the closed categories. |

These are conservative diagnostic categories, not assertions that SMT is
necessary, that a particular optimizer rule caused the issue, or that an
optimization is incorrect. Classification uses an ordered first-match policy;
recipe tags are also recorded as overlapping metadata.

Useful concentrations:

- **12,024 of the 17,050 affine-context goals occur in memory-pass completeness.**
  For example, `2099512 010->011` constraint 26 equates a previous-memory-value
  column with a data column. This points toward memory-semantic reasoning,
  rather than assuming every linear goal follows from algebraic premises alone.
- **All 10,596 activation mismatches** occur in `loop_iteration -> solver`
  completeness (7,096) or the final `trivial_simp -> unnamed snapshot` soundness
  checks (3,500). A representative goal has multiplicity `1`, while its matching
  reference row has multiplicity `is_valid`. An activation assumption must be
  justified, not silently supplied.
- The **30 known-gadget bound gaps** span six blocks at `008->009`:
  `2099672`, `2104736`, `2105000`, `2105468`, `2105476`, `2106332`.
  Each contributes one completeness and four soundness obligations. This sweep
  did not authorize the receive-byte contract.
- The **10 other quotient goals** are all completeness obligations. One example
  (`2103880 008->009`, constraint 22) uses `QuotientOrZero(1-cmp,S)`, not the
  current checker's `QuotientOrZero(cmp,S)` pattern. Eight occur in
  `trivial_simp -> rule_based`; two in `remove_disconnected -> rule_based`.
- The **9 Boolean conditional goals** occur in soundness for
  `2104736 016->017` (5) and `2106368 016->017` (4).

## Recommended implementation order

1. General bounded polynomial normalization for algebraic goals **and bus fields**,
   followed by nonzero-scalar equation matching. Measured opportunity: 136,018.
2. Concrete stateless table evaluation. Measured opportunity: 4,536.
3. Affine-combination certificates. Measured opportunity: 2,656.
4. Boolean-valued conditional recipe certificates and quotient-pattern extensions.
   The measured recipe-specific tail is much smaller than the normalization gap.
5. Audit activation/admissibility and memory-semantic obligations explicitly.

These are disjoint observed categories, not guaranteed integration performance
or coverage figures. Proof evidence, resource limits, and assumption reporting
must be preserved when introducing any production rule.

## Reproduction and evidence

The diagnostic script lives outside the production verifier:

```bash
uv run python ../research/diagnostics/redesign/classify_residuals.py \
  runs/m3-sweep.pyvgk4o7 \
  --output runs/residual-classification-new -j 2

uv run python -m pytest tests/test_residual_classification.py -q
```

The output directory must be new. The script checks saved task coverage,
source hashes, input hashes, reconstructed mapping agreement, and per-direction
and global residual counts. Base instruction/config tables are anchored to
input hashes already present in the source sweep. It refuses to reinterpret
the saved run with changed verifier source files.

Final artifacts: `runs/residual-classification-20260927-refined/`:

- `manifest.json`: input/source report and classifier hashes, budgets and scope.
- `summary.json`: disjoint categories, direction/pass breakdowns, confidence tags.
- `classified.jsonl`: one record per residual, with source indices and evidence.
- `examples.json`: up to five examples per category, including original/mapped expressions.
- `uncounted.json`: the 117 uncounted directions and mapping/error details.

The refined run took 50.29s with two workers, no SMT, and no extra memory cap
or per-direction timeout. Polynomial expansion is capped at 2,048 terms;
affine vectors/provenance at 128 entries and reductions at 512 steps. No
reference polynomial exceeded the polynomial budget; 991 reference-row
occurrences were skipped by the affine-basis budget. Therefore the unresolved
affine bucket is not evidence of non-derivability by a larger affine checker.

An earlier preliminary classification is retained in
`runs/residual-classification-20260927-retry/`; it did not yet evaluate constant
tables or Boolean conditional recipes. The initial sandbox-blocked attempt
left only partial artifacts in `runs/residual-classification-20260927/` and is
not a completed classification.

The subsequent behavior-preserving extraction of shared polynomial arithmetic
is documented in [POLYNOMIAL-NORMALIZATION.md](POLYNOMIAL-NORMALIZATION.md).
The historical results above remain the September 27 measurement; the fresh
post-extraction sweep/classification and record-by-record comparison have
separate artifact paths.
