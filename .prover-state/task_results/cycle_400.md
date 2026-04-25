# Cycle 400 Results

## Worked on
Began the Taylor / smooth-solution bridge for `LMM.truncationOp` in
`OpenMath/LMMTruncationOp.lean`. Added five new declarations (definition +
four theorems) per the cycle 400 strategy.

## Aristotle triage (Step 1)
All six pre-existing Aristotle bundles rejected per strategy:
- `d418653c-…` (COMPLETE): cycle-398 cross-check diagnostic for the live
  `truncationOp_polyShiftDegSucc_eq_leading_of_HasOrder`. **Rejected** —
  already-incorporated cross-check, no merge.
- `4832d223-…`, `4701b7a2-…`, `d845dba2-…`, `d3079062-…`, `142ceb00-…`
  (all COMPLETE_WITH_ERRORS): cycle-399 stub-replacement bundles redefining
  live LMM infrastructure. **Rejected** — same reason as cycle 399.

## Approach
1. Added the sorry-first scaffold for T1–T5 after the existing
   `truncationOp_polynomial_evalShift_eq_leading_of_HasOrder`. Verified
   compile.
2. Submitted 5 Aristotle jobs (A–E) with focused scope.
3. Closed all four sorries manually before the Aristotle refresh window —
   the proofs are short and the dependencies are already in
   `LMMTruncationOp.lean`.

## Result
SUCCESS — all five targets landed and compile:

- `LMM.taylorPoly` (definition): `∑ k ∈ range (n+1), C (y k t / k!) * X^k`.
- `LMM.taylorPoly_natDegree_le`: degree ≤ `n`. Proof uses
  `Polynomial.natDegree_sum_le_of_forall_le` +
  `Polynomial.natDegree_C_mul_X_pow_le`.
- `LMM.taylorPoly_coeff`: for `k ≤ n`, `coeff k = y k t / k!`. Proof:
  `Polynomial.finset_sum_coeff`, `Finset.sum_eq_single`,
  `Polynomial.coeff_C_mul`, `Polynomial.coeff_X_pow`, Kronecker collapse.
- `LMM.truncationOp_taylorPoly_eq_zero_of_HasOrder`: degree-`p` Taylor
  polynomial is annihilated. One-liner via
  `truncationOp_polynomial_evalShift_eq_zero_of_HasOrder` +
  `taylorPoly_natDegree_le`.
- `LMM.truncationOp_taylorPoly_eq_leading_of_HasOrder` (headline T4): for an
  order-`p` LMM and a degree-`p+1` Taylor polynomial of `y` about `t`, the
  truncation operator at `t` equals
  `y^(p+1)(t) · errorConstant p · h^(p+1)`. Proof composes
  `truncationOp_polynomial_evalShift_eq_leading_of_HasOrder` with
  `taylorPoly_coeff`, then `field_simp` cancels the factorial.

`lake env lean OpenMath/LMMTruncationOp.lean` is clean (no warnings, no
errors, no sorry). `lean_verify` on T4 and T5 reports only the standard
axioms `propext, Classical.choice, Quot.sound`.

## Aristotle window
Submitted 5 jobs (job IDs `d5418d04`, `ba8f3583`, `16f00570`, `7d3c9d2a`,
`22966343`) at the start of the cycle. Manual proofs landed before the
30-minute refresh. After the wakeup the queue will be re-checked; any
returned bundles will be triaged but the live file already has zero
sorries, so no merge is expected — same reject pattern as in cycles
398–399. Submitted scaffolds live under
`.prover-state/aristotle_scaffolds/cycle_400/`.

## Dead ends
- Initial T4 attempt ended with `rw [hpoly, hcoeff]; field_simp; ring`,
  which left a "no goals" error because `field_simp` already closes the
  goal once the factorial is cleared. Dropped the trailing `ring`.

## Discovery
- The shifted polynomial-eval wrappers from cycle 399 compose cleanly with a
  derivative-sample-indexed Taylor polynomial without needing any
  `ContDiff` hypothesis. This keeps the polynomial layer (cycle 400) and
  the smooth-`y` bridge (cycle 401) decoupled, as the strategy intended.
- `Polynomial.natDegree_sum_le_of_forall_le` is the right shape for
  uniformly-bounded summands; `Polynomial.natDegree_sum_le` returns a
  `Finset.fold max` expression that is harder to manipulate.

## Suggested next approach (cycle 401)
The headline target is the smooth-`y` Taylor-with-remainder truncation
error bound:
```
‖m.truncationOp h y y' t  -  y^(p+1)(t) · errorConstant p · h^(p+1)‖
  ≤  C · h^(p+2)
```
for `y` that is `(p+2)`-times continuously differentiable on a
neighborhood of `[t, t + s·h]`. Proof outline:
1. Set `Q := taylorPoly (fun k u => iteratedDeriv k y u) t (p+1)` (so the
   derivative samples are honest derivatives of `y`).
2. Apply the cycle-400 headline `truncationOp_taylorPoly_eq_leading_of_HasOrder`
   with `y` interpreted as `iteratedDeriv k y`.
3. Bound the residual `m.truncationOp h y y' t - m.truncationOp h Q.eval Q.derivative.eval t`
   using Taylor's theorem with remainder
   (`Polynomial.taylor_mean_remainder_lagrange` or the integral form),
   pointwise at each shifted abscissa `t + j·h`. Each pointwise residual
   is `O(h^(p+2))`; finite-sum gives the global bound.

The factorization `errorConstant_zero_of_HasOrder_succ` from
`MultistepMethods.lean` may be useful for the consistency-direction
remainder.

Open seams unaffected this cycle:
- `theorem_351B_hypothesis_gap` — textbook lookup.
- `lake_cache_glibc_mismatch` — environment, not blocking.
- `cycle_375_radauIA_collocation_counterexample` — not blocking.

## File size note
`OpenMath/LMMTruncationOp.lean` grew from 437 → ~503 lines, well under the
3000-line cap. No split needed.
