# Cycle 447 Results

## Worked on
BDF1 (backward Euler) vector quantitative convergence chain — new file
`OpenMath/LMMBDF1VectorConvergence.lean`.

## Approach
1. Built the required sorry-first scaffold and verified it compiled before
   proof work.
2. Submitted the planned 5-job Aristotle batch:
   - `6f4b6b26-0a2d-46ac-b2d1-90ac5905a0d2`:
     `LMM.bdf1Vec_one_step_lipschitz`
   - `490ca706-902b-4e2f-af85-da1f64778607`:
     `LMM.bdf1Vec_one_step_error_bound`
   - `69bf9d4a-9a60-4489-a1df-d5d5f033db43`:
     `y_second_order_taylor_remainder_vec`
   - `ce43dc44-40ea-46d1-ba07-269a42d5845d`:
     `bdf1Vec_pointwise_residual_bound`
   - `d39fc2e8-943d-43f8-801d-3ed64d6330f6`:
     `LMM.bdf1Vec_local_residual_bound`
3. Slept 30 minutes and checked those Aristotle jobs exactly once. All five
   were still `QUEUED`, so no Aristotle proof output was incorporated.
4. Proved the chain manually by porting the scalar BDF1 proof and the private
   forward-Euler vector Taylor pattern locally:
   - `LMM.IsBDF1TrajectoryVec`
   - `LMM.bdf1VecResidual` and `LMM.bdf1Vec_localTruncationError_eq`
   - `LMM.bdf1Vec_one_step_lipschitz`
   - `LMM.bdf1Vec_one_step_error_bound`
   - private vector helpers for bounded `iteratedDeriv 2`, first-order
     derivative Taylor, second-order value Taylor, and the BDF1 residual split
   - `LMM.bdf1Vec_local_residual_bound`
   - `LMM.bdf1Vec_global_error_bound`

## Result
SUCCESS. `OpenMath/LMMBDF1VectorConvergence.lean` compiles under
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/LMMBDF1VectorConvergence.lean` with zero errors and zero sorries.

`plan.md` now records BDF1 vector as complete and moves the active §1.2
frontier to BDF2 scalar quantitative convergence.

## Dead ends
- The planner wording mentioned `backwardEuler.localTruncationError` for the
  vector unfolding, but the live `LMM.localTruncationError` API is scalar-only.
  The existing vector convergence chains all use method-specific vector
  residual definitions, so this cycle followed that convention with
  `LMM.bdf1VecResidual`.
- No stale Aristotle bundles were incorporated.

## Discovery
- The scalar BDF1 implicit-substitution pattern ports directly to vector spaces
  with `conv_lhs => rw [hstep]`, `norm_sub_le`, `norm_add_le`, and `norm_smul`.
- The vector BDF1 residual split
  `R_BDF1 = R_FE - h • (y'(t+h) - y'(t))` works cleanly with the forward-Euler
  interval-integral residual proof plus
  `norm_image_sub_le_of_norm_deriv_le_segment'` for the derivative difference.
- Keeping the Taylor helpers private avoided upstream API churn in
  `OpenMath/LMMTruncationOp.lean`.

## Suggested next approach
BDF2 scalar quantitative convergence. Use the scalar AM2 implicit template but
adapt to BDF2 weights `α = ![1/3, -4/3, 1]`, `β = ![0, 0, 2/3]`; the implicit
division should factor out `(2/3)·h·L`, and the residual analysis should be
third order, producing an `O(h²)` global bound.
