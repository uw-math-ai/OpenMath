# Cycle 616 Results

## Worked on
Butcher §521 — stability-order predicate for general linear methods.
Modified `OpenMath/GeneralLinearMethod.lean` (added the
matrix-level predicate `IsStabilityOrder` and the monotonicity lemma)
and `OpenMath/RKAsGLM.lean` (added the scalar predicate
`IsStabilityFunctionOrder` and the bridge from the scalar predicate
to the matrix one for RK methods).

## Approach
Sorry-first per the strategy:

1. Added the three theorem shells (`IsStabilityOrder` def, `.mono`,
   `isStabilityOrder_zero`) to `GeneralLinearMethod.lean`, and the
   two on the RK side. Hit a `Norm (Matrix _ _ ℂ)` synthesis failure
   because Mathlib's `Matrix.normedAddCommGroup` is opt-in; resolved
   with `attribute [local instance] Matrix.normedAddCommGroup` placed
   inside `namespace GeneralLinearMethod` before the §521 block.
2. Verified the sorry-first scaffold compiles in both files
   (the second only after `lake build OpenMath.GeneralLinearMethod`
   to refresh the `.olean` for the downstream RK file).
3. Closed `IsStabilityOrder.mono` directly: shrink `δ` to `min δ 1`,
   use `pow_le_pow_of_le_one` to compare `‖z‖ ^ (p+1)` to
   `‖z‖ ^ (q+1)`, then `mul_le_mul_of_nonneg_left`.
4. Closed `toGLM_isStabilityOrder_of_stabilityFunctionOrder` directly:
   use `Matrix.norm_le_iff` (Mathlib `Analysis.Matrix.Normed`) to
   reduce the matrix-norm bound to entrywise; rewrite each entry of
   `t.toGLM.stabilityMatrix z - exp z • t.toGLM.Vℂ` to
   `t.stabilityFunction z - exp z` via `toGLM_stabilityMatrix`,
   `toGLM_Vℂ`, `Matrix.sub_apply`, `Matrix.smul_apply`,
   `smul_eq_mul`; the bound is then exactly the scalar hypothesis.
5. Attempted `isStabilityOrder_zero` analytically (needs the
   matrix-version of "f(0) = 0 + analytic at 0 ⇒ f = O(z)"); chose
   to honor the strategy's stall protocol and write a focused issue
   file rather than rush an incomplete attempt.

## Result
SUCCESS on the four sorry-free deliverables; PARTIAL with a
documented stall on the fifth.

* `GeneralLinearMethod.IsStabilityOrder` — definition landed.
* `GeneralLinearMethod.IsStabilityOrder.mono` — sorry-free.
* `ButcherTableau.IsStabilityFunctionOrder` — definition landed.
* `ButcherTableau.toGLM_isStabilityOrder_of_stabilityFunctionOrder`
  — sorry-free.
* `GeneralLinearMethod.isStabilityOrder_zero` — left as `sorry`,
  per the strategy's permitted partial-cycle outcome. A focused
  issue file
  `.prover-state/issues/glm_stability_order_zero_analytic_gap.md`
  records the proof obstruction, the searched Mathlib hooks
  (`Asymptotics.IsBigO.bound`,
  `Complex.exp_sub_sum_range_isBigO_pow`,
  `continuousAt_matrix_inv`, `Matrix.norm_le_iff`,
  `Differentiable.inverse`), and three concrete solution paths
  with Solution A (explicit ε-δ assembly via two private helpers)
  recommended for a follow-up cycle.
* `plan.md` updated: the §52 chapter line for §521 is now `[~]` with
  the new surface; the Active Frontier has a one-line entry for
  cycle 616.

## Dead ends
* Default `import Mathlib` does not register a `Norm` instance on
  `Matrix _ _ _`; the instance is `Matrix.normedAddCommGroup` and
  must be opted-in via `attribute [local instance]`. Without this
  the §521 predicates fail synthesis with `failed to synthesize Norm
  (Matrix (Fin r) (Fin r) ℂ)`.
* Trying to resolve the `Norm` synthesis with `open Matrix` does
  not work — the instance is `def` (not `instance`), so it must be
  opted in with `attribute [local instance]`.
* For the bridge proof, naive `simp` without naming
  `Matrix.sub_apply` and `Matrix.smul_apply` leaves the goal in a
  shape where `smul_eq_mul` cannot fire; explicitly listing them
  closes the entry rewrite.

## Discovery
* `attribute [local instance] Matrix.normedAddCommGroup` placed
  inside the namespace before the §521 block is the right scope:
  the L∞ matrix norm is what `Matrix.norm_le_iff` is phrased
  against, and is the right norm for the §521 predicate (it agrees
  with `‖f‖_∞` after the `Matrix.norm_def` unfolding).
* The strategy's "Path B" (Taylor-expand the resolvent to extract
  `M(z) = V + z B U + z² B A (I-zA)⁻¹ U`) is genuinely cleaner than
  Path A on paper but still bottoms out on the same continuity-of-
  matrix-inverse step (`continuousAt_matrix_inv`) since it needs
  the residual `(I-zA)⁻¹` factor to be bounded near `0`.
* The cleanest Mathlib hook for the analytic step is
  `continuousAt_matrix_inv` (`Topology.Instances.Matrix`). It
  threads through `Ring.inverse` of the determinant rather than
  `Inv.inv` directly; the determinant is `1` at `z = 0`, where
  `Ring.inverse` is continuous.

## Suggested next approach
Open cycle 617 with `isStabilityOrder_zero` as the sole target.
Use Solution A from the issue file: write two private helpers
(`norm_exp_sub_one_le_of_norm_le_one`,
`norm_resolvent_factor_bound`), each ~30 lines, then close the main
theorem in a 10-line `calc`. Treat this as one cycle's work, not a
parenthetical inside a broader §521 push. Once it lands, the §521
section can move to fully closed and the planner can rotate to
backlog item #2 (§515 Dahlquist-style equivalence) or extend §521
to a Padé-condition theorem on `M(z)` matching `exp(z) • V` to
order `p+1` in the rational-approximation sense.
