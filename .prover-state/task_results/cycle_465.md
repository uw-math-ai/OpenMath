# Cycle 465 Results

## Worked on
BDF7 vector truncation chain in `OpenMath/LMMBDF7VectorConvergence.lean`, plus promotion of the AB7 vector eighth-order Taylor helpers.

## Approach
Promoted `iteratedDeriv_eight_bounded_on_Icc_vec`, `y_eighth_order_taylor_remainder_vec`, and `derivY_seventh_order_taylor_remainder_vec` from private declarations in `OpenMath/LMMAB7VectorConvergence.lean`.

Created the BDF7 vector sorry-first scaffold, verified it compiled, then attempted the required Aristotle batch. The first batch attempt hit 429 because older Aristotle jobs were already queued. After the required wait, one job was accepted:

- `a4e7b36c-1723-40d7-97be-7294cd86f68f` for `bdf7Vec_localTruncationError_eq`

The other four requested submissions (`bdf7Vec_one_step_lipschitz`, `bdf7Vec_pointwise_residual_alg`, `bdf7Vec_pointwise_residual_bound`, `bdf7Vec_local_residual_bound`) were rejected with 429. After another 30-minute wait, the accepted job was still `QUEUED`, so no Aristotle proof was available to incorporate.

Manual close mirrored the BDF6 vector and BDF7 scalar chains:

- vector trajectory predicate and residual
- one-step Lipschitz defect estimate with `norm_smul`/`norm_sub_le`
- pure residual algebra with exact coefficient `17914498/49005`, slacked to `366`
- pointwise eighth-order Taylor residual bound using the now-public AB7 vector helpers and `clear_value`
- finite-horizon local residual bound

## Result
SUCCESS. `OpenMath/LMMBDF7VectorConvergence.lean` compiles with zero `sorry`.

Also updated `plan.md` to list the BDF7 vector truncation chain and add the new module to the current target file list.

## Dead ends
Aristotle was not usable for this cycle beyond accepting one queued job. The queue remained saturated by older queued requests, and the accepted BDF7 job did not complete after the required wait.

## Discovery
The AB7 vector file already had the needed eighth-order Taylor helpers; only the `private` qualifier blocked downstream reuse. Rebuilding `OpenMath.LMMAB7VectorConvergence` after promotion was necessary before the new module could import them reliably.

## Suggested next approach
Do not add a BDF7 global theorem: BDF7 is zero-unstable. The next planner cycle should choose a new target from `plan.md`; the BDF4-BDF6 Lyapunov/global path remains blocked by `.prover-state/issues/bdf4_lyapunov_gap.md`.
