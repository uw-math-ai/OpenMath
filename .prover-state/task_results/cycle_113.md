# Cycle 113 Results

## Worked on
- Verified the uncommitted `OpenMath/ANStability.lean` proof from cycle 112.
- Checked the harvested Aristotle outputs listed by the planner, especially the cycle-111 AN-stability artifacts.
- Tried two recovery paths for `norm_stabilityFn_imagBasis_gt_one`:
  1. repair the existing continuity/Cramer-style proof in place
  2. replace it with the determinant-based proof harvested from Aristotle

## Approach
- Ran `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ANStability.lean`.
- Inspected the failing region around the imaginary-basis proof and the harvested Aristotle files under `.prover-state/aristotle_results/`.
- Patched `ANStability.lean` locally to switch from the broken continuity argument to a determinant-based proof.
- When that produced many API/proof mismatches, tested the exact harvested Aristotle files (`ANStability.lean` plus `ImagBasisHelpers.lean`) against the live repo snapshot.

## Result
- FAILED.
- The current working-tree version of `OpenMath/ANStability.lean` does not compile.
- The direct in-place repair attempt produced many proof-script mismatches in finite-sum/matrix identities.
- The harvested Aristotle version is also not drop-in compatible with the current repo snapshot:
  `ImagBasisHelpers.lean` still contains unresolved `exact?` placeholders and older proof scripts that fail against the current environment.
- I restored `OpenMath/ANStability.lean` to the local pre-copy backup after the failed artifact import so the worktree reflects the narrower failure surface I had already analyzed.

## Dead ends
- The original continuity proof failed at:
  - `algStabMatrix_quadForm_eq` (`simp` no progress)
  - continuity/neighborhood extraction around `continuous_det_imagBasis`
  - `ext`/`fun_prop` failures in the adjugate-based `S_num` argument
- The determinant-based helper port failed because several scripts from the harvested artifact do not match current Mathlib elaboration:
  - matrix multiplication/`Matrix.diagonal` elaboration mismatches
  - `Matrix.det_add_mul` argument order mismatch
  - determinant-polynomial expansion proof no longer replaying cleanly
- The harvested `OpenMath/ImagBasisHelpers.lean` is not complete in this repo state; its `det_BV_sq_gt_det_AV_sq` theorem still contains `exact?` placeholders.

## Discovery
- The planner’s assumption that cycle 112 only needed a quick verification was incorrect: the saved `ANStability.lean` worktree proof is unfinished at the proof-script level.
- The most promising long-term route is still the determinant-based argument, but it should be rebuilt directly against the current repo rather than imported from the older Aristotle bundle.
- The helper theorem `det_BV_sq_gt_det_AV_sq_with_pos` is the right intermediate target; the current blocker is infrastructure around determinant expansions and the matrix determinant lemma.

## Suggested next approach
- Reconstruct the determinant-based proof in small checked lemmas directly in the repo:
  1. `Bmat`, `AVmat`, `BVmat`
  2. `trace_BV_sq_sub_AV_sq`
  3. `normSq_det_eq`
  4. `stabilityFnDiag_mul_det`
  5. a fresh proof of `det_BV_sq_gt_det_AV_sq_with_pos`
- Do not try to revive the continuity/adjugate proof; it is higher-friction than the determinant path.
- Before any BN-stability work, finish getting `OpenMath/ANStability.lean` compiling and then commit the cycle-112 closure.
