# Cycle 459 Results

## Worked on
Created `OpenMath/LMMBDF4VectorConvergence.lean`, the finite-dimensional vector BDF4 truncation chain.

## Approach
Mirrored the BDF3 vector truncation pattern and copied the BDF4 scalar coefficients by hand. Used the public AB4 vector fifth-order Taylor helpers:
- `iteratedDeriv_five_bounded_on_Icc_vec`
- `y_fifth_order_taylor_remainder_vec`
- `derivY_fourth_order_taylor_remainder_vec`

Wrote the sorry-first file surface and verified it compiled, then closed all proof placeholders manually. Extracted `bdf4Vec_pointwise_residual_alg` as a private helper and used `clear_value` on the Taylor remainder variables before applying it.

Aristotle was skipped entirely per the cycle 459 planner policy. No Aristotle jobs were submitted or polled.

## Result
SUCCESS. Landed:
- `LMM.IsBDF4TrajectoryVec`
- `LMM.bdf4VecResidual`
- `LMM.bdf4Vec_localTruncationError_eq`
- `LMM.bdf4Vec_one_step_lipschitz`
- private `LMM.bdf4Vec_pointwise_residual_alg`
- `LMM.bdf4Vec_pointwise_residual_bound`
- `LMM.bdf4Vec_local_residual_bound`

Also updated `plan.md` with the new BDF4 vector truncation chain and rolled the active frontier forward to the generic BDF Lyapunov framework.

Verification:
```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMBDF4VectorConvergence.lean
```
completed cleanly with 0 sorrys.

## Dead ends
None. The direct BDF3-vector/BDF4-scalar port worked once the residual algebra was separated into a private helper.

## Discovery
The AB4 vector fifth-order Taylor helpers are already public, so no promotion cycle was needed. The vector BDF4 pointwise residual closes with the same exact coefficient `6724/375`, slackened to `18`, as the scalar chain.

## Suggested next approach
Prioritize a generic BDF Lyapunov framework using a quadratic discrete Lyapunov equation `A^T P A - P = -Q`. This is option 1 in `.prover-state/issues/bdf4_lyapunov_gap.md` and should unblock BDF4-BDF6 global theorems uniformly, including methods with irreducible cubic-or-higher characteristic factors.
