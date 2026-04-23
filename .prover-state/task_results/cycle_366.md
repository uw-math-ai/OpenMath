# Cycle 366 Results

## Worked on
- `OpenMath/CollocationAlgStability.lean`
- mandatory one-pass Aristotle triage for:
  - `ffda8780-21da-427d-8ea0-3d168ade76b3`
  - `5b7e7ec3-2e8f-45dc-b3b2-9528c102e2ab`
- the live seam `monomialVec_D_of_algStable`
- downstream triage of the next blocker `stabilityMatrix_quadForm_eq_neg_integral`

## Approach
- Read the required live context first:
  - `.prover-state/issues/cycle_365_358A_monomialVec_D_row_action_normalization.md`
  - `.prover-state/task_results/cycle_365.md`
  - `OpenMath/CollocationAlgStability.lean`
- Inspected only the permitted Aristotle artifacts:
  - `ffda8780.../ARISTOTLE_SUMMARY.md`
  - `ffda8780.../CollocationAlgStability.lean`
  - `5b7e7ec3.../ARISTOTLE_SUMMARY.md`
  - `5b7e7ec3.../CollocationAlgStability.lean`
- Kept the Aristotle material as proof-shape only and rejected all bundled stub
  modules / build-file edits.
- Added a theorem-local reshaping lemma
  `algStabMatrix_monomial_row_action` immediately above
  `monomialVec_D_of_algStable`.
- Proved `monomialVec_D_of_algStable` in the strategy order:
  1. set `v i := t.c i ^ k`
  2. use `algStabMatrix_mulVec_zero_of_psd_of_quadForm_zero`
  3. rewrite the row action with the new helper
  4. rewrite the `A`-sum by `C(k + 1)`
  5. rewrite the `b`-moment by `B(k + 1)`
  6. finish the scalar identity with `field_simp` and `nlinarith`
- Rechecked the file and the module build after the proof landed.
- Then analyzed the next blocker and wrote a focused issue instead of reviving
  the rejected antiderivative / `%ₘ nodePoly` route.

## Result
- SUCCESS: `monomialVec_D_of_algStable` is now proved in the live file.
- SUCCESS: the B-upgrade chain is now live end-to-end:
  - `monomialVec_D_of_algStable`
  - `moment_upgrade_from_D`
  - `satisfiesB_two_mul_sub_one_of_algStable`
  - `nodePoly_interval_zero_aux_of_algStable`
- SUCCESS: both required verification commands passed:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/CollocationAlgStability.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.CollocationAlgStability`
- PARTIAL SUCCESS: the next seam is now isolated to
  `stabilityMatrix_quadForm_eq_neg_integral`.

## Dead ends
- Did not transplant the completed Aristotle proof bodies directly. They still
  depend on broad `simp_all` / `convert` normalization and bundled stub modules,
  which is not live-safe for this repository.
- Did not reopen the old antiderivative or quotient-by-`nodePoly` route; the
  strategy was explicit that this branch is dead.

## Discovery
- The cycle-365 blocker is resolved exactly as planned: the row-action
  normalization was the missing infrastructure.
- The live blocker has moved to the top-degree defect identity in
  `stabilityMatrix_quadForm_eq_neg_integral`.
- The likely next proof shape is:
  - prove monomial bilinear vanishing for all pairs below the top degree,
  - isolate the `X^(s - 1)` contribution,
  - recover the right-hand side from the degree-`2 * s - 1` defect of
    `nodePoly t * X^(s - 1)`.

## Suggested next approach
- Start the next cycle directly at
  `stabilityMatrix_quadForm_eq_neg_integral`.
- Use the focused blocker note
  `.prover-state/issues/cycle_366_358A_stabilityMatrix_top_degree_defect.md`.
- Do not inspect `409155c2...` or move to the theta-sign stage until the
  stability-matrix identity and `orthogonal_degree_eq_boundaryPoly` are live.
