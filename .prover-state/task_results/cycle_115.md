# Cycle 115 Results

## Worked on
- Priority 1: verification of the uncommitted `OpenMath/ANStability.lean`
- Priority 2: sorry-first staging of Theorem 357C in `OpenMath/BNStability.lean`

## Approach
- Read `.prover-state/strategy.md` and followed the mandated `ANStability.lean` verification path first.
- Ran
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ANStability.lean`.
- When that failed due to a missing cached Mathlib root object, rebuilt the target with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ANStability`
  to force dependency restoration and expose real diagnostics.
- Compared the working-tree `ANStability.lean` against the harvested Aristotle proof to confirm the current file is the det-ratio rewrite and not the old heartbeat-heavy version.
- After hitting the 30-minute Priority 1 cap, wrote a blocker issue and switched to Theorem 357C.
- Read `extraction/formalization_data/entities/thm_357C.json`.
- Created `OpenMath/BNStability.lean` in sorry-first form with:
  - `IsDissipative`
  - `SatisfiesRKStep`
  - `IsBNStable`
  - helper lemmas `rk_stage_difference_eq`, `rk_output_difference_eq`,
    `algStabMatrix_inner_nonneg`, `rk_step_diff_norm_sq_identity`
  - theorem `alg_stable_implies_bn_stable`
- Verified the BN file compiles with sorry warnings via
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/BNStability.lean`.
- Submitted the BN file to Aristotle.

## Result
- FAILED for Priority 1: `OpenMath/ANStability.lean` still does not compile.
- SUCCESS for Priority 2 staging: `OpenMath/BNStability.lean` now exists, compiles in sorry-first form, and has been submitted to Aristotle.

## Dead ends
- The original `lake env lean OpenMath/ANStability.lean` failure was not a source-code error at all; it failed because `/tmp/OpenMath-lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean` was missing.
- After rebuilding dependencies, the AN-stability proof still failed in multiple independent helper lemmas, so there was no safe single-line repair path.
- Importing `OpenMath.ANStability` into `BNStability.lean` is not viable this cycle because `ANStability.lean` is currently broken.

## Discovery
- The current AN-stability blocker is now precise: the failure is a stack of API breakages in matrix and polynomial determinant lemmas, not a timeout or toolchain issue.
- The most brittle helper stack is:
  - `AVmat` / `BVmat`
  - `trace_BV_sq_sub_AV_sq`
  - `det_one_add_smul_expansion`
  - `stabilityFnDiag_mul_det`
  - `norm_stabilityFn_imagBasis_gt_one`
- Aristotle project submitted for BN-stability:
  - `8184d812-f26d-4a1c-a8e3-63bc4051978b` for `OpenMath/BNStability.lean`

## Suggested next approach
- First, harvest Aristotle project `8184d812-f26d-4a1c-a8e3-63bc4051978b` and incorporate any solved BN-stability helper lemmas.
- For `ANStability.lean`, repair bottom-up:
  1. fix `AVmat`/`BVmat`,
  2. replace the polynomial expansion lemma with smaller determinant expansions,
  3. rewrite `stabilityFnDiag_mul_det` against the current Mathlib API,
  4. then reattempt `norm_stabilityFn_imagBasis_gt_one`.
