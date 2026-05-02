# Issue: LMM stability charpoly Step C adjugate contraction

## Status

**Step C.3 partially landed (cycle 664).** The past-`y` adjugate-row
entry now has a clean, sorry-free explicit form, and the §521 headline
`LMM.toGLM_stabilityMatrix_charpoly_explicit` lands sorry-free
(modulo the trivial existential placeholder for the past-`h*f`
entry). What remains is the past-`h*f` evaluation, which depends on
the block adjugate identity `Matrix.adjugate_fromBlocks_zero₂₁` (the
sole `sorry` left in this thread, in the new helper module
`OpenMath/Helpers/BlockAdjugate.lean`).

## Blocker (remaining)

The past-`h*f` entry `toGLM_stabilityCharpolyRowF` evaluates a
`vecMul`-against-adjugate at a *bottom-half* index
`Fin.cast _ (Fin.natAdd s ⟨s-1, _⟩)`. Substituting via
`Matrix.vecMul_adjugate_apply` (cycle 664) reduces this to the
determinant of the V active charmatrix with a *bottom-half row*
replaced by the rank-one row. That replacement destroys the
upper-block-triangular structure (the lower-left block becomes
nonzero in the updated row), so `Matrix.det_fromBlocks_zero₂₁` does
not apply.

The clean route is via the block adjugate identity:
```
Matrix.fromBlocks A B 0 D).adjugate =
  Matrix.fromBlocks
    (D.det • A.adjugate)
    (-(A.adjugate * B * D.adjugate))
    0
    (A.det • D.adjugate)
```
which is currently the sorry in `OpenMath/Helpers/BlockAdjugate.lean`.
Once landed, the past-`h*f` `vecMul` against the bottom-row of this
block adjugate yields the desired closed form:
- the diagonal contribution `A.det • D.adjugate` for the bottom block;
- the off-diagonal correction `-(A.adj * B * D.adj)` paired with the
  top half of the rank-one row (only the past-`y` rank-one entries
  contribute, and only at the last column, where `B` is non-zero).

## Sparse helpers landed (cycles 662-664)

```
LMM.toGLM_rankOneRow_castAdd
LMM.toGLM_rankOneRow_natAdd
LMM.toGLM_rankOneColumn_castAdd
LMM.toGLM_rankOneColumn_natAdd
LMM.toGLM_stabilityMatrix_charpoly_rankOne_contraction
LMM.toGLM_stabilityCharpolyRowY
LMM.toGLM_stabilityCharpolyRowF
LMM.sum_castAdd_selector_collapse
LMM.sum_natAdd_selector_collapse
LMM.toGLM_stabilityMatrix_charpoly_rankOne_contraction_explicit
-- Cycle 664:
Matrix.vecMul_adjugate_apply
LMM.toGLM_stabilityCharpolyRowY_eq_explicit
LMM.toGLM_stabilityCharpolyRowF_eq_explicit  -- trivial existential
LMM.toGLM_stabilityMatrix_charpoly_explicit
-- Sorry-first scaffold (Cycle 664):
Matrix.adjugate_fromBlocks_zero₂₁  -- the only outstanding sorry
```

## What was tried

Cycle 661 proved the headline rank-one charpoly identity. Cycle 662
packaged the four sparse-projection lemmas plus the focused
contraction reduction. Cycle 663 added the two named scalar entries
and collapsed the selector sums. Cycle 664 added
`Matrix.vecMul_adjugate_apply` (Cramer's-rule row form) and used it
to expose the past-`y` entry as a determinant of an updated PY
charmatrix. After pushing `updateRow` through `Matrix.reindex` and
`Matrix.charmatrix_fromBlocks`, the lower-left block stays zero
(top-half row update), so `det_fromBlocks_zero₂₁` closes the goal
directly. The same route does not apply to past-`h*f` because a
bottom-half row update destroys the upper-triangular structure.

## Possible solutions for past-`h*f`

1. **Block adjugate identity** (recommended): close
   `Matrix.adjugate_fromBlocks_zero₂₁` in
   `OpenMath/Helpers/BlockAdjugate.lean`. Cleanest argument: prove
   that `(claimed adjugate) * (fromBlocks A B 0 D) =
   (det) • 1` by block computation, and conclude via
   `Matrix.adjugate_unique` (or `mul_eq_one_iff_inv` analogues).
2. **Direct cofactor**: evaluate the bottom-row column of the V
   active charmatrix adjugate by Laplace expansion. The relevant
   column is `(natAdd s ⟨s-1, _⟩)`, whose deletion minor is mixed
   between the PY and PHF blocks.
3. **Pair-then-evaluate**: compute the `vecMul` of the rank-one row
   against the adjugate symbolically before unfolding, using
   `Matrix.adjugate_mulVec_eq_det_smul` or its transposed analogue.

Recommended: route (1). The block adjugate identity is reusable and
the proof obligation is well-scoped.

## Down-stream after past-`h*f`

Once `toGLM_stabilityCharpolyRowF_eq_explicit` is sorry-free, the
§521 LMM iff bridge `LMM.toGLM_isAStable_iff` follows by routine
root-location of the now-explicit
`LMM.toGLM_stabilityMatrix_charpoly_explicit`.
