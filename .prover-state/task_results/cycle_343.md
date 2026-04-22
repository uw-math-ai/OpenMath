# Cycle 343 Results

## Worked on
- `OpenMath/PadeOrderStars.lean`
- Odd-wedge slice seam:
  `oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst`
- Odd-wedge projection seam:
  `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst`
- New helper targets introduced this cycle:
  - `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`

## Approach
- Read:
  - `.prover-state/task_results/cycle_342.md`
  - `.prover-state/issues/pade_odd_wedge_projection_no_stop_gap.md`
  - the two live `sorry` regions in `OpenMath/PadeOrderStars.lean`
- Followed the planner’s refactor order exactly inside
  `OpenMath/PadeOrderStars.lean`.
- Added a true-wedge endpoint-sign helper immediately above
  `oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst`.
- Rewrote the slice-zero theorem so it now:
  - keeps the `r = 0` branch via
    `mem_oddDownArrowRadiusPhaseZeroSet_zero`
  - keeps the continuity + IVT argument on `Set.Icc (-r) r`
  - uses the new helper instead of re-instantiating the strip theorem with
    `η = r`
- Moved the exact quantitative blocker into a named local target `hgapTarget`
  inside the new helper:

  ```lean
  K * r < (-padePhiErrorConst n d) * Real.sin (((↑(n + d) + 1) : ℝ) * r) / 2
  ```

- Added the fixed-radius slice helper immediately above
  `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst`.
- Rewrote the final projection theorem so its remaining contradiction is exactly
  the fixed-radius slice helper, not a theorem-level monolithic `sorry`.
- Verified the sorry-first scaffold with:
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
- Submitted a fresh 5-job Aristotle batch on the live file:
  - `c3160f50-9736-432f-8a49-3c422c7603cc`
  - `ee966484-4a7c-4cec-bfd7-e0571355ca08`
  - `fb99a47e-1f05-4adb-9cb2-e44462435db7`
  - `ec9a08b7-4ed5-419d-afd5-9974589af9f1`
  - `6ad5578f-fa4a-42ec-96eb-4c85673cad17`
- Slept once for 30 minutes (`sleep 1800`) and refreshed once.
- After Aristotle stayed queued, used Lean search for likely missing library
  lemmas:
  - sine lower bounds (`Real.mul_lt_sin`, `Real.mul_le_sin`)
  - interval/zero-set connectivity searches

## Result
- SUCCESS (code progress): both original theorem-level `sorry`s in
  `OpenMath/PadeOrderStars.lean` were refactored into theorem-local helper
  seams matching the planner’s requested surfaces.
- SUCCESS (slice theorem): `oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst`
  now compiles without its own direct `sorry`; it depends only on the new
  true-wedge endpoint-sign helper.
- SUCCESS (projection theorem): `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst`
  now compiles without its own direct `sorry`; it depends only on the new
  fixed-radius slice helper.
- SUCCESS (verification): the file compiles with exactly 2 helper `sorry`s.
- PARTIAL: no live proof was closed, because the remaining seams are sharper but
  still blocked.
- PARTIAL: Aristotle produced no usable output because all five cycle-343 jobs
  remained `QUEUED` even after the single allowed 30-minute wait and single
  refresh.

## Dead ends
- Repeating the old `η = r` strip route would have recreated the cycle-342
  `r < δstrip` mismatch, so that route was removed instead of retried.
- The new direct true-wedge endpoint-sign proof still reduces to the exact
  comparison
  `K * r < (-padePhiErrorConst n d) * Real.sin (((↑(n + d) + 1) : ℝ) * r) / 2`
  for the `K` returned by `padeR_exp_neg_local_bound n d`.
- Lean search confirmed that available sine lower bounds only turn this into a
  constant comparison against `K`; they do not produce the missing bound on `K`.
- The final fixed-radius contradiction still lacks a theorem showing that the
  true odd zero slice at one radius cannot meet both sides of a clopen split.
  Current live inputs give existence of slice zeros, but not uniqueness or
  connectedness of the slice zero set.

## Discovery
- The odd-wedge blocker is now localized to two precise analytic seams:
  1. a same-order coefficient comparison in the true-slice endpoint-sign proof
  2. a missing fixed-radius slice theorem for the clopen contradiction
- The true-slice endpoint seam is not just “small radius” generically:
  because `sin (((↑(n + d) + 1) : ℝ) * r) ~ ((↑(n + d) + 1) : ℝ) * r`,
  the main term at the endpoints is also order `r ^ (n + d + 2)`, exactly the
  same order as the current error bound from `padeR_exp_neg_local_bound`.
- Therefore the present `O(r ^ (n + d + 2))` bound is too coarse unless one
  controls its coefficient sharply enough.
- The file now exposes the exact handoff surfaces a future cycle should attack,
  instead of broader strip/topology scaffolding.

## Suggested next approach
- Do not reopen strip-only or selector/path infrastructure.
- Attack the endpoint helper with stronger asymptotics:
  either prove a sharper remainder theorem than `padeR_exp_neg_local_bound`, or
  extract an explicit upper bound on its `K` that is strong enough to dominate
  the true-slice main term.
- For the final helper, target one concrete fixed-radius theorem on the live
  wedge:
  uniqueness of the zero on `Set.Icc (-ρ) ρ`, connectedness of the fixed-radius
  zero slice, or monotonicity of the imaginary-part function along the slice.
- Reuse the current helper surfaces and keep the theorem interfaces unchanged.
