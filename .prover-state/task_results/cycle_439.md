# Cycle 439 Results

## Worked on
AM3 vector quantitative convergence chain in `OpenMath/LMMAM3VectorConvergence.lean`, plus public promotion of the AB4 vector fifth-order Taylor helpers in `OpenMath/LMMAB4Convergence.lean`.

## Approach
Removed `private` from `iteratedDeriv_five_bounded_on_Icc_vec`, `y_fifth_order_taylor_remainder_vec`, and `derivY_fourth_order_taylor_remainder_vec`, then rebuilt `OpenMath.LMMAB4Convergence`.

Wrote the AM3 vector file sorry-first and verified it compiled. Submitted five Aristotle jobs:
- `4887ae5b`: `am3Vec_localTruncationError_eq`, `COMPLETE_WITH_ERRORS`; proved only the `rfl` step but commented unavailable OpenMath imports in the artifact, so only the idea was used.
- `f33885a0`: `am3Vec_one_step_lipschitz`, `COMPLETE`; produced a brittle generated one-step proof, not integrated directly.
- `36794c4c`: one-step divided/pair bounds, `COMPLETE_WITH_ERRORS`; artifact switched to `import Mathlib`, so not integrated directly.
- `2f036517`: pointwise residual, still `IN_PROGRESS` at the single refresh after the mandated wait.
- `8ac738ff`: global bound, still `IN_PROGRESS` at the single refresh after the mandated wait.

After the single refresh, manually ported the scalar AM3 chain using the AM2 vector norm proof style and the promoted AB4 vector Taylor helpers.

## Result
SUCCESS. Added:
- `LMM.IsAM3TrajectoryVec`
- `LMM.am3VecResidual`
- `LMM.am3Vec_localTruncationError_eq`
- `LMM.am3Vec_one_step_lipschitz`
- `LMM.am3Vec_one_step_error_bound`
- `LMM.am3Vec_one_step_error_pair_bound`
- `LMM.am3Vec_pointwise_residual_bound`
- `LMM.am3Vec_local_residual_bound`
- `LMM.am3Vec_global_error_bound`

The headline theorem gives `||yseq N - y(t0 + N*h)|| <= exp(3*L*T)*eps0 + K*h^4` under `(N+2)*h <= T` and `(9/24)*h*L <= 1/2`.

## Dead ends
The first manual one-step Lipschitz proof timed out when large expanded vector expressions were left directly in triangle/norm goals. Introducing local abbreviations for the error pieces (`A`, `B9`, `B19`, `B5`, `B1`) and replacing tiny `nlinarith` arithmetic closes with explicit `calc ... = ... by ring` resolved the heartbeat issue without raising `maxHeartbeats`.

Aristotle artifacts were not copied directly because completed-with-errors runs altered the import environment, and the complete one-step proof was less maintainable than the established local template.

## Discovery
For implicit vector AM proofs, even small scalar arithmetic inside norm-smul bounds can trigger `linarith`/`nlinarith` heartbeats if the surrounding vector terms remain expanded. Abbreviating the smul error terms before triangle estimates keeps the kernel work predictable.

The promoted AB4 vector helpers are enough for the AM3 vector fifth-order residual; the module identity closes with `simp only [smul_sub, smul_add, smul_smul]; module`.

## Suggested next approach
Continue the Adams-Moulton vector frontier with AM4 vector, following the same pattern: first promote any needed AB5 vector sixth-order helpers, then port scalar AM4 through compact vector remainder abbreviations to avoid heartbeat blowups.
