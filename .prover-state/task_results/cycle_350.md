# Cycle 350 Results

## Worked on
- Triaged the ready Aristotle bundle `cb77fe5d-ccd3-4aa2-8117-bbb74c00798c`.
- Refactored the analytic seam around `padeR_exp_neg_second_order_factorization`
  in `OpenMath/PadeOrderStars.lean`.
- Closed the defect-side second-order factorization helper.
- Closed the truncated-exponential second-order factorization helper.
- Closed `padeR_exp_neg_second_order_factorization` itself around the new helper seam.

## Approach
- Read `.prover-state/task_results/cycle_349.md`.
- Read `.prover-state/issues/padeR_exp_neg_second_order_factorization_heartbeat_blowup.md`.
- Read the live theorem block around the four original `sorry`s in
  `OpenMath/PadeOrderStars.lean`.
- Diffed the Aristotle `PadeAsymptotics.lean` bundle against the live file and
  inspected `ARISTOTLE_SUMMARY.md`.
- Added the following local second-order helper seam directly above
  `padeR_exp_neg_second_order_factorization`:
  - `padeDefectSecondCoeff`
  - `expTaylorExpNegSecondCoeff`
  - `padeDefect_sub_second_factorization`
  - `expTaylor_exp_neg_second_order_factorization`
  - `padeR_exp_neg_second_coeff_identity`
- Proved `padeDefect_sub_second_factorization` from
  `PadeAsymptotics.padeDefect_poly_coeff_lt`,
  `..._succ`, and `..._succ_succ` via `X^(n+d+3)` divisibility.
- Proved `expTaylor_exp_neg_second_order_factorization` by combining
  `expTaylor_exp_neg_leading_term (m + 1)` with the linear factorization of
  `exp (-z)`.
- Assembled `padeR_exp_neg_second_order_factorization` from the two new helpers
  plus `exp_neg_div_padeQ_linear_factorization`, using a piecewise witness to
  handle `padeQ n d z = 0`.
- Submitted one new Aristotle job for `padeDefect_sub_second_factorization`;
  four further submissions were rejected immediately by Aristotle with `429`
  (“too many requests in progress”).
- Per workflow, slept for 1800 seconds and then performed exactly one refresh on
  the accepted new project.

## Result
- SUCCESS: Aristotle triage for
  `cb77fe5d-ccd3-4aa2-8117-bbb74c00798c` confirmed the bundle is stale for this
  cycle.
  - It only extracted the already-known helper split for
    `padeQ_mul_expTaylor_coeff_succ_succ`.
  - The Aristotle `PadeAsymptotics.lean` still contains downstream `sorry`s.
  - No live changes from that bundle were incorporated.
- SUCCESS: closed these declarations in `OpenMath/PadeOrderStars.lean`:
  - `padeDefect_sub_second_factorization`
  - `expTaylor_exp_neg_second_order_factorization`
  - `padeR_exp_neg_second_order_factorization`
- SUCCESS: the main analytic seam is now decomposed into small local helpers
  instead of one monolithic proof.
- SUCCESS: `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  succeeds with four `sorry` warnings.
- SUCCESS: `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`
  succeeds.
- PARTIAL: new Aristotle submission
  `b8f45bec-d404-4ef4-98a8-9ea5a87b6ff9`
  remained `QUEUED` after the required sleep and single refresh.
- PARTIAL: only one new Aristotle submission was accepted this cycle; the other
  four attempted submissions were rejected by the service with `429 too many
  requests in progress`.

## Dead ends
- The exact coefficient helper
  `padeR_exp_neg_second_coeff_identity`
  still resists the final in-file normalization step, even though a standalone
  `lean_run_code` version of the same proof shape succeeds.
- I did not force the downstream endpoint-sign or fixed-radius arguments before
  the analytic seam was refactored and the main second-order theorem reassembled.

## Discovery
- The heartbeat problem really was organizational: once the defect side and the
  truncated-exponential side were split into tiny local helpers, the main theorem
  could be reassembled without reintroducing the monolithic blow-up.
- The live sorry count in `OpenMath/PadeOrderStars.lean` is back to 4, but the
  set has changed. The remaining `sorry`s are now:
  - `padeR_exp_neg_second_coeff_identity`
  - the local `hgapTarget` inside
    `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`

## Suggested next approach
- First close `padeR_exp_neg_second_coeff_identity` with a literal-coefficient
  lemma and only then `simpa` back to the named defs.
- Once that helper is sorry-free, replace the old first-order `hgapTarget`
  argument in the endpoint-sign theorem with the new second-order expansion.
- After endpoint signs are rebuilt, attack the fixed-radius uniqueness theorem
  before the clopen contradiction.
