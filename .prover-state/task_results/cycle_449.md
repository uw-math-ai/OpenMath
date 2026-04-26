# Cycle 449 Results

## Worked on
BDF2 finite-dimensional vector quantitative convergence chain in
`OpenMath/LMMBDF2VectorConvergence.lean`.

## Approach
Archived the stale BDF1 vector Aristotle bundles after confirming
`OpenMath/LMMBDF1VectorConvergence.lean` had no active `sorry`.

Created the BDF2 vector scaffold, verified the sorry-first file compiled, and
submitted five Aristotle jobs:

- `3ca115f3-00d7-4efa-a7e4-9af696d13024`
- `e0dc83ae-0729-473b-aabd-7c1fdd2c1a00`
- `5c1c18c7-056e-42c5-aa3f-7e241ab431d9`
- `45dcf66e-51c9-4f72-a9f4-8814268db8d7`
- `7f5e43af-31c0-471d-82db-5653b21508ea`

After the required 30-minute wait, the single refresh pass found all five still
`QUEUED`, so no Aristotle output was incorporated.

Manually ported the scalar BDF2 Lyapunov proof to vector norms, using
method-specific vector residuals as in the BDF1 vector file.

## Result
SUCCESS. Added a sorry-free `OpenMath/LMMBDF2VectorConvergence.lean` with:

- `IsBDF2TrajectoryVec`
- `bdf2VecResidual`
- `bdf2Vec_localTruncationError_eq`
- `bdf2Vec_pointwise_residual_bound`
- `bdf2Vec_local_residual_bound`
- `bdf2Vec_one_step_lipschitz`
- `bdf2Vec_one_step_error_pair_bound`
- `bdf2Vec_global_error_bound`

Also made the AB2 vector third-order Taylor helpers public, because the current
tree still had them marked `private` despite the planner expecting public reuse.

## Dead ends
The planned `localTruncationErrorVec` and
`lmm_error_bound_from_local_truncation_vec` symbols are not present in the
current `OpenMath/LMMTruncationOp.lean`. The BDF2 vector chain therefore follows
the existing BDF1 vector pattern: a method-specific residual and the scalar
Grönwall bridge applied to a real-valued Lyapunov sequence.

## Discovery
The Lyapunov coordinate proof ports cleanly to vector norms:
`u_n = (3/2) • e_{n+1} - (1/2) • e_n`,
`v_n = (3/2) • e_n - (3/2) • e_{n+1}`, and
`W_n = ‖u_n‖ + ‖v_n‖`.

The small-step hypothesis `(2/3) * h * L ≤ 1/4` is enough to solve the forcing
term exactly as in the scalar proof, yielding residual coefficient `6` and
effective growth `4L`.

## Suggested next approach
If future vector LMM work wants a generic truncation operator, add
`localTruncationErrorVec` and a vector-facing wrapper around the scalar
Grönwall bridge. Otherwise, continue using method-specific residuals for
implicit vector methods.
