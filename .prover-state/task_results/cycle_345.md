# Cycle 345 Results

## Worked on
- `OpenMath/PadeOrderStars.lean`
- New local seam:
  `padeR_exp_neg_second_order_factorization`
- Live helper seam:
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
- New local seam:
  `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
- Live helper seam:
  `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`

## Approach
- Read:
  - `.prover-state/strategy.md`
  - `.prover-state/task_results/cycle_344.md`
  - `.prover-state/issues/pade_odd_wedge_projection_no_stop_gap.md`
  - the two live `sorry` bodies in `OpenMath/PadeOrderStars.lean`
- Added the local coefficient wrapper
  `padeRExpNegSecondCoeff`.
- Added the theorem-local scaffold
  `padeR_exp_neg_second_order_factorization` exactly at the cycle-345
  analytic seam.
- Added the theorem-local scaffold
  `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
  so the fixed-radius contradiction is now blocked on a local uniqueness
  theorem rather than generic topology.
- Re-verified the file with:
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  after introducing the new helper surfaces.
- Aristotle submission initially failed with HTTP 429 because old
  `PadeOrderStars.lean` projects from earlier cycles were still occupying the
  queue.
- Listed queued Aristotle work, canceled the stale cycle-343/344 and earlier
  `PadeOrderStars.lean` jobs, then submitted the focused cycle-345 batch:
  - `24895e30-89d4-4db8-8b95-d0f1001de8df`
  - `9f8f8368-8414-4974-a2ff-289bc0e70588`
  - `ad07f453-2f28-4cb2-bd45-b28a69adcc5f`
  - `b0eaefbd-dc77-4182-aea4-6e48663c16f0`
  - `5e6710c5-41f3-4122-9f2b-0e72b069a31b`
- Launched the required `sleep 1800` wait.
- While waiting, closed the denominator-side exact algebra needed for the
  second-order route:
  - `exp_neg_sub_linear_factorization`
  - `padeQ_sub_linear_factorization`
  - `padeQ_inv_linear_factorization`
  - `exp_neg_div_padeQ_linear_factorization`

## Result
- PARTIAL SUCCESS: `OpenMath/PadeOrderStars.lean` compiles with the remaining
  local `sorry` surface reduced to four theorems:
  1. `padeR_exp_neg_second_order_factorization`
  2. `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
  3. `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
  4. `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`
- SUCCESS: the coarse denominator bookkeeping is no longer part of the blocker.
  The exact linear remainder of `exp (-z) / padeQ n d z` is now formalized.
- PARTIAL Aristotle status:
  the cycle-345 batch was submitted successfully after clearing the stale queue,
  but the mandated single post-wait refresh had not yet been performed during
  the local proof work recorded in this cycle file.

## Dead ends
- The first Aristotle submission attempt failed immediately because the queue
  was saturated by stale queued jobs; local progress had to come first, then the
  stale queue had to be cleared before the new batch could be submitted.
- Attempting to drive the endpoint theorem directly from the old coarse
  `padeR_exp_neg_local_bound` seam remained the wrong approach; the useful
  progress came only after isolating exact denominator linear terms.

## Discovery
- The quotient bookkeeping is now explicit and closed:
  near `z = 0`,
  `exp (-z) / padeQ n d z = 1 - (n / (n + d)) * z + O(z^2)`
  in exact factorized form.
- That means the analytic gap in
  `padeR_exp_neg_second_order_factorization` is no longer “control the whole
  rational expression”; it is specifically the exact degree-`n + d + 2`
  coefficient / factorization for the Padé defect itself.
- The fixed-radius topology seam is likewise sharper:
  `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both` is now blocked
  only by the local uniqueness theorem
  `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`.

## Suggested next approach
- After the 30-minute wait completes, refresh the five cycle-345 Aristotle jobs
  exactly once and inspect whether any of them fill:
  - `padeR_exp_neg_second_order_factorization`
  - `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`
- If Aristotle is still empty, attack the exact remaining analytic statement:
  derive the degree-`n + d + 2` coefficient of the Padé defect, then combine it
  with the now-closed
  `exp_neg_div_padeQ_linear_factorization` to close
  `padeR_exp_neg_second_order_factorization`.
- Once the endpoint theorem closes, use the already-scaffolded fixed-radius
  uniqueness theorem to discharge the final clopen contradiction with minimal
  edits.
