# Cycle 433 Results

## Worked on
AM2 scalar quantitative convergence scaffold in `OpenMath/LMMAM2Convergence.lean`.

## Approach
Archived the four superseded Aristotle result directories from cycles 432/AB3 into `.prover-state/aristotle_archive/`.
Created `LMM.IsAM2Trajectory` to parameterize the implicit AM2 recurrence and added the fixed-point existence placeholder `am2Trajectory_exists`.
Wrote the five AM2 theorem declarations in order, verified the sorry-first file, submitted the mandated five Aristotle jobs, waited 30 minutes, and refreshed each job once.

## Result
SUCCESS.

The command
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAM2Convergence.lean`
passes.  The file contains the AM2 trajectory predicate and all five planned theorem statements.

Closed:
- `LMM.am2_localTruncationError_eq` by unfolding `localTruncationError` / `truncationOp` and simplifying the live AM2 coefficients.
- `LMM.am2_one_step_lipschitz` by decomposing the implicit-step error and moving the `5/12 hL` new-point term to the left.
- `LMM.am2_one_step_error_bound` by canceling the positive factor `1 - 5/12 hL` under `5/12 hL ≤ 1/2`, with slack effective constant `3L` and residual multiplier `2`.

`lean_verify` on `LMM.am2_one_step_error_bound` reported only standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Aristotle jobs
- `3cd99dae-1218-491e-acf8-089da5b7023d` (`am2_localTruncationError_eq`): `COMPLETE_WITH_ERRORS`.  Rejected as a bundle because it created stub replacement `OpenMath` dependency files; the live proof was closed manually with the same unfold/simp/ring idea.
- `e4871950-7568-4e59-96f3-dd57c701138e` (`am2_one_step_lipschitz`): `IN_PROGRESS` at the single post-wait refresh (7%).
- `87950b69-d5b8-4b85-a779-f58e1d0ccdd6` (`am2_local_residual_bound`): `IN_PROGRESS` at the single post-wait refresh (7%).
- `9c685e01-0dc4-4a2a-8b32-ee19874f6a9c` (`am2_one_step_error_bound`): `COMPLETE_WITH_ERRORS`.  Rejected as a bundle because it created stub replacement `OpenMath` dependency files; the live proof was closed manually against the actual preceding Lipschitz theorem.
- `710cc7e8-eb91-4136-83a7-4d0fd495b1fd` (`am2_global_error_bound`): `IN_PROGRESS` at the single post-wait refresh (6%).

## Remaining sorrys
- `am2Trajectory_exists`: fixed-point existence for the implicit AM2 step needs a Banach contraction argument under the `5/12 hL < 1` condition and was explicitly out of scope for this cycle.
- `am2_local_residual_bound`: requires the fourth-order Taylor remainder proof and pointwise AM2 residual algebra; the Fraction coefficient check gives `11/8`, but the imported AB3 bounded-derivative helper is private and cannot be reused directly.
- `am2_global_error_bound`: depends on the local residual bound before the final `lmm_error_bound_from_local_truncation` assembly can be completed.

## Dead ends
The completed Aristotle bundles were not incorporated because both terminal results replaced live OpenMath dependencies with stub modules, which violates the cycle acceptance rule.

## Discovery
The AM2 pointwise Taylor-remainder coefficient computed by exact `Fraction` arithmetic is `11/8`.
`OpenMath/LMMAB3Convergence.lean` contains the desired fourth-derivative bounded-on-compact helper, but it is declared `private`, so a future cycle must expose or duplicate a public helper before the AM2 residual proof can use it.

## Suggested next approach
Promote a public compact-bound helper for fourth derivatives, then prove a pointwise AM2 residual helper with coefficient `11/8` before closing `am2_local_residual_bound` and the headline global theorem.
