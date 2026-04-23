# Cycle 349 Results

## Worked on
- Closed the remaining local `hsub` inside `PadeAsymptotics.padeQ_mul_expTaylor_coeff_succ_succ`.
- Restored `OpenMath/PadeOrderStars.lean` to the live four-sorry seam after an unsuccessful second-order factorization attempt.
- Checked the Aristotle batch requested by the planner after the required single 30-minute wait.

## Approach
- Read the prior cycle report, the live blocker issue, and the theorem bodies around the remaining sorries in `OpenMath/PadeAsymptotics.lean` and `OpenMath/PadeOrderStars.lean`.
- Proved `hsub` by converting `Finset.Icc 2 q` to `Finset.Ico 2 (q + 1)`, splitting `q = 0` versus `0 < q`, isolating the `j = 0,1` subtraction from the full `Finset.range (q + 1)` sum, and normalizing the small terms with separate lemmas `hsmall0`, `hsmall1`, and `hrange2`.
- Submitted 5 Aristotle jobs after the local scaffold phase:
  - `967abc64-8cdd-4e9a-a6ea-de2d12f968fd` for the local `hsub`
  - `cc01c469-a8ee-4b34-8f3f-dbb278794b1c` for `padeR_exp_neg_second_order_factorization`
  - `914fbab1-59ce-42be-a7f0-8adf8ecbdcde` for `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
  - `a1c26af3-db00-4cf5-9b34-9d800c6a6ee7` for `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
  - `0e8898de-afd8-446f-b21d-d72dee25c92a` for `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`
- Per instructions, slept once for 1800 seconds and then did exactly one refresh on each project.
- Tried to assemble the second-order Padé factorization locally, but reverted that draft when it caused heartbeat blow-ups and left `PadeOrderStars` non-compiling.

## Result
- SUCCESS: `OpenMath/PadeAsymptotics.padeQ_mul_expTaylor_coeff_succ_succ` is now fully proved, so the total live sorry count dropped from 5 to 4.
- SUCCESS: `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeAsymptotics.lean`
  completed with only linter warnings.
- SUCCESS: `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  completed with the expected four `sorry` warnings.
- SUCCESS: `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`
  completed successfully.
- FAILED: No Aristotle result was incorporable this cycle. After the single refresh, all five submitted projects were still `QUEUED`.
- FAILED: `padeR_exp_neg_second_order_factorization` remains open; a focused blocker issue was written at `.prover-state/issues/padeR_exp_neg_second_order_factorization_heartbeat_blowup.md`.

## Dead ends
- A monolithic local proof of `padeR_exp_neg_second_order_factorization` caused heartbeat blow-ups in `OpenMath/PadeOrderStars.lean`.
- Moving the same argument into a new helper file did not relieve the elaboration pressure enough to keep the file usable.
- Leaving that draft in place broke local compilation, so it was reverted to the original `sorry` scaffold.

## Discovery
- The coefficient bottleneck in `PadeAsymptotics` was genuinely local to `hsub`; once the small-term subtraction was isolated, the theorem closed without reopening `padeDefect_poly_coeff_succ_succ`.
- The next blocker is not obviously mathematical content anymore; it is proof organization and elaboration pressure in the second-order factorization.
- The live `PadeOrderStars` seam now consists of exactly these four remaining declarations:
  - `padeR_exp_neg_second_order_factorization`
  - `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`

## Suggested next approach
- Refactor `padeR_exp_neg_second_order_factorization` into 2-3 very small private lemmas inside `PadeOrderStars.lean` instead of one theorem with large local definitions.
- Separate the defect-side factorization, the `expTaylor * exp(-z)` factorization, and the degree-`n + d + 2` coefficient identity before recombining them.
- Do not spend another cycle polling the current Aristotle jobs unless the planner explicitly wants that; this cycle’s required single refresh produced nothing usable.
