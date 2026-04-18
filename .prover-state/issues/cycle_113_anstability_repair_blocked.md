# Issue: Cycle 113 AN-stability repair blocked

## Blocker
`OpenMath/ANStability.lean` does not compile, so cycle 112 cannot be committed yet.

## Context
Running

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ANStability.lean
```

on the saved cycle-112 worktree exposed failures in the imaginary-basis proof for
`norm_stabilityFn_imagBasis_gt_one`.

Representative failures from the live file:
- `simp` made no progress in `algStabMatrix_quadForm_eq`
- continuity proof around `continuous_det_imagBasis` failed to instantiate correctly
- `ext` and `fun_prop` failed in the adjugate/Cramer setup
- the final `Continuous S_num` and norm-squared steps never close

I also tested the harvested Aristotle repair path from
`.prover-state/aristotle_results/95f3a6d4-c727-4482-9525-94f795041d07/`.
That path is not directly usable either:
- its helper file still contains unresolved `exact?` placeholders
- some matrix/determinant proofs no longer elaborate against the current repo/Mathlib state
- `Matrix.det_add_mul` usage appears to assume an older API shape

## What was tried
- Verified the saved cycle-112 file directly with `lake env lean`.
- Read the relevant region of `OpenMath/ANStability.lean`.
- Read the harvested Aristotle outputs for cycle 111 and the AN-stability helper bundle.
- Replaced the broken continuity proof with a determinant-based proof skeleton directly in `ANStability.lean`.
- Tested the exact harvested `ANStability.lean`/`ImagBasisHelpers.lean` pair from Aristotle.

## Possible solutions
- Rebuild the determinant-based argument locally in small lemmas rather than importing the old artifact wholesale.
- Start from these helper targets:
  - `trace_BV_sq_sub_AV_sq`
  - `normSq_det_eq`
  - `stabilityFnDiag_mul_det`
  - `det_BV_sq_gt_det_AV_sq_with_pos`
- Once `norm_stabilityFn_imagBasis_gt_one` compiles again, immediately re-run:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ANStability.lean
```

and only then commit the cycle-112 closure.
