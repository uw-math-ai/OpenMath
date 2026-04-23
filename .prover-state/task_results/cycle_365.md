# Cycle 365 Results

## Worked on
- `OpenMath/CollocationAlgStability.lean`
- Mandatory one-pass Aristotle triage for:
  - `f298bb43-ff28-4047-aba4-00f6d9bc1692`
  - `9ff6bd72-65af-4a9c-9fb3-36c9bd0f14a8`
  - `04dc25b1-f231-437c-b2e4-7bb394171735`
  - `6ef314f0-9928-498f-90c6-23644b5496e7`
- The `(358c)` zero-theorem route behind `nodePoly_interval_zero_aux_of_algStable`
- Fresh Aristotle batch for:
  - `monomialVec_D_of_algStable`
  - `moment_upgrade_from_D`
  - `satisfiesB_two_mul_sub_one_of_algStable`
  - `stabilityMatrix_quadForm_eq_neg_integral`
  - `boundary_theta_nonneg_of_algStable`

## Approach
- Read the cycle strategy, the live blocker issue
  `.prover-state/issues/cycle_364_358A_zero_helper_antiderivative_collapse.md`,
  and only the permitted files from the four ready Aristotle bundles:
  `ARISTOTLE_SUMMARY.md` and `CollocationAlgStability.lean`.
- Confirmed the planner’s triage:
  - `f298bb43...`: use only for the `B(2*s - 1)` proof shape
  - `9ff6bd72...`: keep only for the later theta-sign route
  - `04dc25b1...`: keep only as later proof shape for the orthogonal-degree lemma;
    do not adopt its theorem-statement change
  - `6ef314f0...`: reject as a live patch because it introduces stub infrastructure
- Deleted the dead antiderivative/remainder scaffold from
  `OpenMath/CollocationAlgStability.lean`:
  - `antiderivativePoly`
  - its endpoint/node-evaluation lemmas
  - the `modByMonic nodePoly` helpers
  - `algStabMatrix_quadForm_eq_antiderivativePoly`
  - `antiderivative_remainder_exact`
- Replaced that route with theorem-local B-upgrade infrastructure:
  - `algStabMatrix_monomial_inner_eq`
  - `algStabMatrix_monomial_quadForm_eq`
  - `algStabMatrix_monomial_quadForm_zero`
  - `algStabMatrix_row_eq_col`
  - `algStabMatrix_quadForm_shift_single`
  - `algStabMatrix_mulVec_zero_of_psd_of_quadForm_zero`
  - theorem-local scaffolds `monomialVec_D_of_algStable`,
    `moment_upgrade_from_D`, and
    `satisfiesB_two_mul_sub_one_of_algStable`
- Rewrote `nodePoly_interval_zero_aux_of_algStable` to the intended short proof:
  use `t.SatisfiesB (2 * s - 1)`, exactness of quadrature on
  `((nodePoly t) * q)`, and `quadEvalPoly_nodePoly_mul_eq_zero`.
- Verified both:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/CollocationAlgStability.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.CollocationAlgStability`
- Submitted the fresh focused Aristotle batch after the new scaffold compiled.
- After the single allowed wait + refresh:
  - inspected only the completed result bundles for `ffda8780...` and `9c1a6e55...`
  - rejected the `ffda8780...` `monomialVec_D_of_algStable` body as not live-safe
  - incorporated the `9c1a6e55...` proof body for `moment_upgrade_from_D`

## Result
- SUCCESS: the zero theorem is now genuinely rewritten around the quadrature-order
  upgrade route, not the dead antiderivative decomposition.
- SUCCESS: the file and module build both verify after the rewrite.
- SUCCESS: three live local helper steps are now proved in the new route:
  - monomial quadratic-form expansion
  - vanishing of that quadratic form from a high-enough `B` condition
  - PSD quadratic-form zero implies kernel (`Mv = 0`)
- SUCCESS: `moment_upgrade_from_D` is now live from the fresh Aristotle batch.
- PARTIAL SUCCESS: the remaining blockers are isolated to the finite-sum
  normalizations needed for:
  - `monomialVec_D_of_algStable`
  - the induction theorem `satisfiesB_two_mul_sub_one_of_algStable`
- Aristotle status after the single allowed refresh:
  - `ffda8780-21da-427d-8ea0-3d168ade76b3` (`monomialVec_D_of_algStable`): `COMPLETE_WITH_ERRORS`
  - `9c1a6e55-7847-4b67-9d36-b68bce89bd85` (`moment_upgrade_from_D`): `COMPLETE_WITH_ERRORS`
  - `5b7e7ec3-2e8f-45dc-b3b2-9528c102e2ab` (`satisfiesB_two_mul_sub_one_of_algStable`): `IN_PROGRESS` at 19%
  - `4f3ee601-6534-4991-b802-4c99623bec7f` (`stabilityMatrix_quadForm_eq_neg_integral`): `IN_PROGRESS` at 17%
  - `28f20c33-a2cc-48ed-807e-e184fecdee2d` (`boundary_theta_nonneg_of_algStable`): `IN_PROGRESS` at 24%

## Dead ends
- The cycle-364 antiderivative route was deleted rather than repaired, because
  the active blocker issue was correct: it collapses before reaching
  `nodePoly t * q`.
- Manual proof attempts after the rewrite showed that the hard part is no longer
  PSD-to-kernel itself; it is the theorem-local algebra turning the row-action
  identity into the exact `D(k+1)` formula, and then summing that formula into
  the `B` upgrade.
- The completed Aristotle proof for `monomialVec_D_of_algStable` had the right
  strategy, but its large `convert` / `simp_all` normalization does not port
  directly to the live file without introducing new reshaping lemmas.

## Discovery
- The live blocker has moved forward. The generic kernel fact
  “PSD + zero quadratic form implies `Mv = 0`” is now available in the file.
- The new seam is narrower and more useful than the cycle-364 blocker:
  finite-sum normalization from
  `∑ i, algStabMatrix j i * c_i^k = 0`
  to the explicit `D(k+1)` moment identity, followed by the scalar
  `D + C -> B` upgrade.
- Fresh Aristotle submissions created:
  - `ffda8780-21da-427d-8ea0-3d168ade76b3` for `monomialVec_D_of_algStable`
  - `9c1a6e55-7847-4b67-9d36-b68bce89bd85` for `moment_upgrade_from_D`
  - `5b7e7ec3-2e8f-45dc-b3b2-9528c102e2ab` for `satisfiesB_two_mul_sub_one_of_algStable`
  - `4f3ee601-6534-4991-b802-4c99623bec7f` for `stabilityMatrix_quadForm_eq_neg_integral`
  - `28f20c33-a2cc-48ed-807e-e184fecdee2d` for `boundary_theta_nonneg_of_algStable`
- Recorded the remaining blocker in:
  `.prover-state/issues/cycle_365_358A_monomialVec_D_row_action_normalization.md`

## Suggested next approach
- If Aristotle returns a usable fragment, first try to close
  `monomialVec_D_of_algStable`; that is the earliest remaining seam on the new route.
- If `monomialVec_D_of_algStable` closes but `moment_upgrade_from_D` still fails,
  keep the blocker focused on the scalar `D + C -> B` algebra and do not reopen
  any antiderivative scaffolding.
- Only after the B-upgrade route is fully live should the cycle return to
  `stabilityMatrix_quadForm_eq_neg_integral` and the theta-sign stage.
