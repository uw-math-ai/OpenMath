# Cycle 414 Results

## Worked on
Pure mechanical refactor: extracting the entire Adams–Bashforth 2-step
(AB2) convergence chain out of `OpenMath/LMMTruncationOp.lean` into a
new module `OpenMath/LMMAB2Convergence.lean`. Triggered by the cycle 414
strategy: the core file was 3089 lines, just over the 3000-line cap.

REFACTOR_COMMIT — net repo line count is roughly preserved; the cycle is
a split, not new content.

## Approach
1. Read the import header and the full AB2 block (lines 1771–3088 of
   the live `OpenMath/LMMTruncationOp.lean`).
2. Created `OpenMath/LMMAB2Convergence.lean` with the same Mathlib
   imports (`Taylor`, `Integrals.Basic`) plus
   `import OpenMath.MultistepMethods`, `import OpenMath.AdamsMethods`,
   `import OpenMath.LMMTruncationOp`, opened `namespace LMM`, and pasted
   the AB2 block verbatim.
3. Deleted lines 1771–3088 from `OpenMath/LMMTruncationOp.lean` with
   `sed`. The single original `end LMM` (was line 3089) remains as the
   last line of the trimmed core file.
4. Ran `lake build OpenMath.LMMTruncationOp` to refresh the `.olean`
   (necessary so that the new file's `import OpenMath.LMMTruncationOp`
   resolved against the trimmed declarations rather than a stale cache).
5. Verified `OpenMath/LMMAB2Convergence.lean` compiles cleanly with the
   NVMe toolchain: `lake env lean OpenMath/LMMAB2Convergence.lean`.
6. Greppped `OpenMath/` for the moved AB2 names — only the new file
   matches; no other consumer needed an import update.

## Result
SUCCESS. Both files compile; only pre-existing simp-arg lints from the
original block survived the move (no proof modifications).

## Declarations moved (verbatim, no edits)
Scalar AB2:
- `LMM.ab2Iter`, `ab2Iter_zero`, `ab2Iter_one`, `ab2Iter_succ_succ`
- `LMM.ab2_localTruncationError_eq`
- `LMM.ab2_one_step_lipschitz`, `LMM.ab2_one_step_error_bound`
- private `iteratedDeriv_three_bounded_on_Icc`,
  `y_third_order_taylor_remainder`,
  `derivY_second_order_taylor_remainder`,
  `ab2_pointwise_residual_bound`
- `LMM.ab2_local_residual_bound`, `LMM.ab2_global_error_bound`

Vector AB2:
- `LMM.ab2IterVec`, `ab2IterVec_zero`, `ab2IterVec_one`,
  `ab2IterVec_succ_succ`
- `LMM.ab2VecResidual`, `LMM.ab2Vec_localTruncationError_eq`
- `LMM.ab2Vec_one_step_lipschitz`, `LMM.ab2Vec_one_step_error_bound`
- private `iteratedDeriv_three_bounded_on_Icc_vec`,
  `derivY_second_order_taylor_remainder_vec`,
  `y_third_order_taylor_remainder_vec`,
  `ab2Vec_pointwise_residual_bound`
- `LMM.ab2Vec_local_residual_bound`, `LMM.ab2Vec_global_error_bound`

## Final line counts
- `OpenMath/LMMTruncationOp.lean`: 1771 lines (was 3089) — under cap
- `OpenMath/LMMAB2Convergence.lean`: 1342 lines (new, under cap)

All public AB2 names retain their fully qualified paths
(`LMM.ab2Iter`, `LMM.ab2_global_error_bound`, etc.). No renames.

## Aristotle
Not used this cycle. The strategy explicitly authorises skipping
Aristotle for pure refactor cycles: there are no live sorrys, and
submitting already-closed theorems wastes free compute.

## Dead ends
None. The first compile attempt of the new file emitted spurious
"already declared" errors that were entirely an artifact of the
core file's stale `.olean` (which still contained the moved
declarations). After `lake build OpenMath.LMMTruncationOp` rebuilt
the cache, the new file compiled cleanly without any source changes.

## Discovery
When refactor splits move declarations between two files, `lake env
lean <new_file>` will fail with bogus "already declared" errors until
the source file's `.olean` is rebuilt. The `lake build <Module>`
target is the cheapest fix; running `lake env lean <source_file>`
on its own type-checks but does not always refresh the cached olean
that imports resolve against.

## Suggested next approach
- A future cycle can split off the forward-Euler scalar+vector chain
  from `OpenMath/LMMTruncationOp.lean` into
  `OpenMath/LMMForwardEulerConvergence.lean` if the file grows again.
  Right now it's at 1771 lines, comfortably under the cap, so this
  isn't urgent.
- `OpenMath/LMMAB2Convergence.lean` is the natural home for the
  follow-on Adams–Bashforth chains (AB3, AB4, ...) and could be
  renamed to `LMMABConvergence.lean` if/when AB3 is added — or each
  step can get its own module (`LMMAB3Convergence.lean`, ...).
- The active blocker issues (`thm_358A_if`,
  `reversed_poly_C3_corrected_identity`) remain untouched and
  unblocked by this refactor.
