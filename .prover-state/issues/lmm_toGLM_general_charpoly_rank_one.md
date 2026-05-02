# Issue: General LMM-to-GLM charpoly rank-one factorisation

## Blocker

Cycle 641 exposed the full `Matrix.fromBlocks` decomposition and the
rank-one update

```lean
m.toGLM.stabilityMatrix z =
  V_active_lift +
    (1 / (1 - z * (m.β (Fin.last s) : ℂ))) • rankOneCorrection
```

but the remaining charpoly bridge still needs a determinant identity for the
specific companion-shift matrix plus that rank-one update. Mathlib has useful
pieces (`Matrix.charpoly_reindex`, `Matrix.charpoly_fromBlocks_zero₁₂`,
`Matrix.charpoly_fromBlocks_zero₂₁`, `Matrix.det_one_add_smul`,
`Matrix.det_one_add_replicateCol_mul_replicateRow`), but not a direct theorem
for

```lean
(shiftCompanion + c • Matrix.vecMulVec u v).charpoly
```

with the nilpotent past-`h*f` shift rows contributing the spurious `X^s`
factor and the active factor matching `LMM.stabilityPoly`.

## Context

The useful cycle 641 lemmas are in `OpenMath/LMMAsGLM.lean`:

```lean
LMM.toGLM_stabilityMatrix_eq_fromBlocks
LMM.toGLM_stabilityMatrix_eq_V_active_plus_rank_one
```

The LMM-side target is currently a scalar function:

```lean
LMM.stabilityPoly (m : LMM s) (ξ z : ℂ) : ℂ
```

There is not yet a polynomial-valued `scaledStabilityPoly m z : ℂ[X]` with
evaluation theorem connecting its roots to `m.stabilityPoly · z`.

## What was tried

- Proved the block entries as four `s × s` matrices and reindexed them through
  `toGLM_stabilityBlockEquiv`.
- Proved the stability matrix is a rank-one update of the complex `V` block via
  `Matrix.vecMulVec`.
- Searched Mathlib for block charpoly and rank-one determinant tools. Existing
  tools cover triangular block matrices and `det(1 + r • M)`, but the current
  matrix needs a companion-shift determinant calculation before those tools can
  identify the LMM stability polynomial factor.

## Possible solutions

1. Define a polynomial-valued LMM stability polynomial
   `stabilityPolyPoly (m : LMM s) (z : ℂ) : ℂ[X]` and prove its evaluation
   agrees with `m.stabilityPoly ξ z`.
2. Reindex `charmatrix (m.toGLM.stabilityMatrix z)` using
   `toGLM_stabilityMatrix_eq_fromBlocks` and eliminate the nilpotent
   past-`h*f` shift block by repeated sparse-column/row expansion or a helper
   determinant lemma for the shift block.
3. Prove a local determinant lemma for the companion-shift-plus-rank-one shape,
   probably by induction on `s`, yielding
   `charpoly(M(z)) = X^s * scaledStabilityPoly m z` after denominator clearing.
4. Once the polynomial factorisation lands, `LMM.toGLM_isAStable_iff` should
   follow by `Matrix.charpoly_reindex` and the evaluation bridge for
   `stabilityPolyPoly`.

## Status as of cycle 658

Solution (1) landed: `stabilityPolyPoly` is defined and bridged to
`stabilityPoly`. The block-level charpolys (general PHF, general PY) for
each diagonal block have been computed without `hbdf`. The remaining gap
is the *full* assembly when both off-diagonal blocks PYHF and PHFY are
non-zero rank-one (true for general LMMs, false only under `hbdf`). See
`lmm_general_stability_charpoly_step3.md` for the next two recommended
lemmas (`toGLM_V_active_charpoly` and `Matrix.charpoly_add_smul_vecMulVec`)
and a route comparison.
