# Cycle 457 Results

## Worked on
BDF3 vector quantitative convergence chain in `OpenMath/LMMBDF3VectorConvergence.lean`.

## Approach
Created the sorry-first vector scaffold mirroring `LMMBDF3Convergence.lean`, then verified it with:

`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMBDF3VectorConvergence.lean`

Submitted five Aristotle jobs after the scaffold compiled:

- `8303e116-f1af-4f1f-bf63-e11568c402a6`: `bdf3Vec_one_step_lipschitz`
- `30089745-7998-46c0-b750-ee34f97c3db1`: three Lyapunov successor recurrences
- `f3701dca-5054-4323-8540-8db30a271f69`: `bdf3Vec_pointwise_residual_bound`
- `9ae09f0d-b411-40ba-85e0-18600a88895a`: `bdf3VecLyapW_initial_bound`
- `60407b4a-3099-40ad-a6d4-de741689ffd5`: `bdf3Vec_eIdx2_le_W`

Slept 30 minutes, then refreshed each job once. All five were still `QUEUED`, so no Aristotle proofs were available to incorporate. Closed the goals manually by porting the scalar BDF3 Lyapunov proof and the BDF2/AB3 vector norm patterns.

## Result
SUCCESS. Added a sorry-free BDF3 vector chain:

- `LMM.IsBDF3TrajectoryVec`
- `LMM.bdf3VecResidual` and `LMM.bdf3Vec_localTruncationError_eq`
- `LMM.bdf3Vec_one_step_lipschitz`
- `LMM.bdf3VecLyapU`, `LMM.bdf3VecLyapSigma`, `LMM.bdf3VecLyapTau`, `LMM.bdf3VecLyapW`
- `LMM.bdf3VecLyapU_succ_eq`, `LMM.bdf3VecLyapSigma_succ_eq`, `LMM.bdf3VecLyapTau_succ_eq`
- `LMM.bdf3Vec_pointwise_residual_bound` and `LMM.bdf3Vec_local_residual_bound`
- `LMM.bdf3Vec_one_step_error_bound`
- `LMM.bdf3VecLyapW_initial_bound`
- `LMM.bdf3Vec_eIdx2_le_W`
- `LMM.bdf3Vec_global_error_bound`

Verification:

- `lake env lean OpenMath/LMMBDF3VectorConvergence.lean` passed cleanly.
- `rg -n "sorry|admit" OpenMath/LMMBDF3VectorConvergence.lean` found no matches.
- `lean_verify` on `LMM.bdf3Vec_global_error_bound` reported no axioms and no warnings.

## Dead ends
The first scaffold import tried to import `OpenMath.LMMBDF3Convergence`, but the scalar module's `.olean` was not present for a direct `lake env lean` check. The vector file does not need that import, so I narrowed imports to `MultistepMethods`, `LMMTruncationOp`, and `LMMAB3Convergence`.

Aristotle did not produce usable output because all five jobs remained queued after the mandated 30-minute wait.

## Discovery
The scalar BDF3 pure-algebra helper was private, so the vector module carries a vector-norm version of the same algebra core. The direct port stays within the heartbeat budget when kept separate from the trajectory context.

The vector pointwise residual closes cleanly with the public AB3 vector Taylor helpers and the identity
`R = R_y(3) - (18/11)R_y(2) + (9/11)R_y(1) - (6h/11)R_y'(3)`.

## Suggested next approach
Continue the BDF quantitative frontier with BDF4 scalar convergence. Expect more eigenstructure work than BDF3 because the BDF4 characteristic polynomial has a degree-3 non-principal block.
