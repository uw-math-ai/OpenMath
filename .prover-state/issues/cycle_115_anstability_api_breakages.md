# Issue: Cycle 115 ANStability API breakages after dependency rebuild

## Blocker
`OpenMath/ANStability.lean` still does not compile after restoring the `/tmp` lake toolchain and rebuilding Mathlib. The initial failure was environmental (`Mathlib.olean` missing), but once dependencies were rebuilt the file exposed multiple genuine proof/API breakages.

## Context
Command used:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ANStability
```

This rebuilt Mathlib successfully and then failed on `OpenMath/ANStability.lean`.

Main failing regions:
- `trace_BV_sq_sub_AV_sq`:
  - line 198: `HMul (Fin s → Fin s → ℝ) (Matrix (Fin s) (Fin s) ℝ) ...` from `AVmat`/`BVmat`
  - line 217: remaining algebraic goal after `simp`/`ring`
- `one_sub_mul_one_add`:
  - line 232: matrix identity not closed by current `simp [sub_mul, mul_add, ...]`
- `normSq_det_eq`:
  - line 244: coercion mismatch between determinant over `ℂ` and determinant over `ℝ`
- `det_one_add_smul_expansion`:
  - lines 267–272: old polynomial proof no longer matches current `Polynomial.derivative_prod`/`dvd_iff_isRoot` elaboration
  - line 288: parser error at `unexpected token 'in'`
- `Aℂ_mul_diag_imagBasis`:
  - line 307: unresolved goals after `by_cases hij`
- `stabilityFnDiag_mul_det`:
  - line 339: `Matrix.det_add_mul` argument order/API mismatch
  - line 346: remaining matrix-entry algebra goal in the determinant-ratio rewrite
- `norm_stabilityFn_imagBasis_gt_one`:
  - line 445: failed rewrite with `Aℂ_mul_diag_imagBasis`

## What was tried
- Verified PATH starts with `/tmp/lake-bin:/tmp/lean4-toolchain/bin`.
- Ran `lake env lean OpenMath/ANStability.lean`; this first failed because the cached Mathlib `.olean` root was missing.
- Rebuilt with `lake build OpenMath.ANStability` to get real diagnostics.
- Compared the working-tree file against the Aristotle `d535dc15...` version to confirm the current file is a local det-ratio rewrite rather than the older heartbeat-heavy proof.

## Why this is not a quick repair
- The file is failing in several independent helper lemmas, not just the final theorem.
- The breakages are mostly API-shape changes in matrix/polynomial determinant lemmas, so the path to repair is local re-engineering, not one-line edits.
- Finishing this responsibly would exceed the 30-minute cap for Priority 1.

## Possible solutions
- Repair the helper stack from the bottom up in this order:
  1. fix `AVmat`/`BVmat` definitions so they are genuine matrix products,
  2. replace the brittle `det_one_add_smul_expansion` proof with smaller determinant expansion lemmas,
  3. rewrite `stabilityFnDiag_mul_det` against the current `Matrix.det_add_mul` API,
  4. then return to `norm_stabilityFn_imagBasis_gt_one`.
- Use the Aristotle file only as a lemma-structure reference, not as a wholesale replacement, because it still relies on `maxHeartbeats 800000`.
