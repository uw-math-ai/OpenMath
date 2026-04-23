# Cycle 367 Results

## Worked on
- `OpenMath/CollocationAlgStability.lean`
- mandatory one-pass Aristotle triage for:
  - `995901fc-98bc-4885-a95e-c5dc63a0cabb`
  - `ffe56f65-fcc6-4d9f-9040-b47ac4158f52`
- the new live helper immediately above
  `stabilityMatrix_quadForm_eq_neg_integral`
- the next seam inside `stabilityMatrix_quadForm_eq_neg_integral`

## Approach
- Read the required live context first:
  - `.prover-state/issues/cycle_366_358A_stabilityMatrix_top_degree_defect.md`
  - `.prover-state/task_results/cycle_366.md`
  - `OpenMath/CollocationAlgStability.lean`
- Per the cycle instructions, triaged only these Aristotle artifacts once:
  - `995901fc.../ARISTOTLE_SUMMARY.md`
  - `995901fc.../CollocationAlgStability.lean`
  - `ffe56f65.../ARISTOTLE_SUMMARY.md`
  - `ffe56f65.../CollocationAlgStability.lean`
- Rejected both bundles as transplant sources:
  - both are stale full-file rebuilds,
  - both create sidecar modules / alternate dependency chains,
  - `995901fc...` also rewrites the live `algStabilityBoundaryPoly` sign convention.
- Kept only the high-level proof idea that the later theta-sign lemma should be
  driven by testing against `shiftedLegendrePoly (s - 1)`.
- Added and proved the theorem-local mixed-monomial helper:

```lean
private lemma algStabMatrix_monomial_bilinear_zero
```

- The helper proof follows the live infrastructure route:
  1. expand `algStabMatrix`,
  2. rewrite one `A`-sum by `monomialVec_D_of_algStable`,
  3. rewrite the other `A`-sum by `C`,
  4. rewrite all moments by `B(2 * s - 1)`,
  5. solve the scalar identity explicitly with `field_simp` and `ring`.
- Rechecked the target file after the helper landed.
- Then attempted `stabilityMatrix_quadForm_eq_neg_integral` and wrote a focused
  blocker issue when the next seam was isolated.

## Result
- SUCCESS: the mixed-monomial infrastructure is now live in
  `OpenMath/CollocationAlgStability.lean`.
- SUCCESS: the target file rechecks with the helper in place; only the intended
  four theorem-level sorrys remain.
- PARTIAL SUCCESS: the next blocker in
  `stabilityMatrix_quadForm_eq_neg_integral` is now precise and documented.

## Dead ends
- Did not transplant either Aristotle bundle. Both are incompatible with the
  live repository state and one rewrites the boundary-polynomial sign.
- The planner’s suggested Nat-side helper bound
  `m + n ≤ 2 * s - 3` is not safe in Lean at `s = 1` because subtraction is
  truncated. The live private helper had to be stated using the nontruncated
  bound actually needed by the proof:

```lean
m + n + 2 ≤ 2 * s - 1
```

- The planner’s suggested remainder

```lean
q - Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)
```

is only a valid top-term cancellation when `q.natDegree = s - 1`; it does not
reduce degree for genuinely low-degree `q`.

## Discovery
- The top-degree defect is no longer the first blocker.
- The real next seam is a safe reduction of the theorem’s full statement into:
  - a low-degree branch `q.natDegree < s - 1`, where both sides should be zero,
  - a top-degree branch `q.natDegree = s - 1`, where the degree-`2 * s - 1`
    defect of `(nodePoly t) * X^(s - 1)` remains.
- A likely next helper is a polynomial bilinear vanishing lemma obtained by
  expanding two low-degree polynomials into monomials and applying
  `algStabMatrix_monomial_bilinear_zero`.

## Suggested next approach
- Use the new focused blocker note:
  `.prover-state/issues/cycle_367_stabilityMatrix_general_q_reduction.md`
- First split `stabilityMatrix_quadForm_eq_neg_integral` into the low-degree and
  top-degree branches described there.
- Only after that reduction is live should the proof resume the planner’s
  top-degree defect computation.
