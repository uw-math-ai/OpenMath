# Cycle 467 Results

## Worked on
AB8 vector quantitative convergence in `OpenMath/LMMAB8VectorConvergence.lean`,
plus the corresponding `plan.md` frontier update.

## Approach
I mirrored the AB7 vector chain at order 8, reusing the scalar AB8 generic
coefficient bridge from `OpenMath/LMMAB8Convergence.lean` and the public
ninth-order vector Taylor helpers from `OpenMath/LMMAM7VectorConvergence.lean`.
The new file was first scaffolded sorry-first and checked with Lean, then the
proofs were closed manually using extracted residual algebra helpers and the
generic AB vector global theorem.

I attempted the required five Aristotle submissions immediately after the
scaffold for:

- `LMM.ab8Vec_localTruncationError_eq`
- `LMM.ab8Vec_one_step_lipschitz`
- the AB8 vector residual algebra helpers
- `LMM.ab8VecResidual_eq_abResidualVec`
- `LMM.ab8Vec_global_error_bound`

All five `submit_file` calls were rejected with HTTP 429 because the Aristotle
queue already had too many in-progress requests. I still slept for 1800 seconds
as required and then checked Aristotle once; the queue contained only older
BDF/AM jobs, so there were no cycle-467 results to incorporate.

## Result
SUCCESS. `OpenMath/LMMAB8VectorConvergence.lean` now contains the full AB8 vector
quantitative convergence chain with no `sorry`s:

- `LMM.ab8IterVec`
- `LMM.ab8VecResidual` and `LMM.ab8Vec_localTruncationError_eq`
- `LMM.ab8Vec_one_step_lipschitz` and `LMM.ab8Vec_one_step_error_bound`
- private residual algebra/triangle helpers and `LMM.ab8Vec_pointwise_residual_bound`
- `LMM.ab8Vec_local_residual_bound`
- `LMM.ab8IterVec_eq_abIterVec` and `LMM.ab8VecResidual_eq_abResidualVec`
- `LMM.ab8Vec_global_error_bound`

Verification completed:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAB8VectorConvergence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.LMMAB8VectorConvergence`

## Dead ends
The Aristotle batch could not be queued because existing projects saturated the
service limit. Manual proof work was therefore load-bearing for this cycle.

The one-step vector Lipschitz and error-bound lemmas were routed through a small
generic pointwise vector AB Lipschitz helper, which requires the finite-dimensional
instance already needed by the global vector theorem.

## Discovery
The generic pointwise AB vector Lipschitz helper avoids writing and maintaining
an 8-term hand triangle proof for the explicit Adams-Bashforth recurrence.
The existing `LMM.ab8GenericCoeff` and `LMM.abLip_ab8GenericCoeff` bridge cleanly
to `LMM.ab_global_error_bound_generic_vec` once the AB8 vector iteration and
residual equalities are in place.

The cycle-450/451 `clear_value` pattern remains important in the ninth-order
vector residual proof; using it after set aliases kept the proof kernel-friendly.

## Suggested next approach
If more Adams-Bashforth vector ports are planned, consider moving the generic
pointwise AB vector Lipschitz helper into `OpenMath/LMMABGenericConvergence.lean`
so AB9 and later vector files can share it. AB9 scalar still appears to need a
higher-order Taylor ladder before the same convergence pattern can proceed.
