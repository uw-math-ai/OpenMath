# Issue: LMM stability charpoly Step C adjugate contraction

## Status

**Block-adjugate infrastructure landed (cycle 664).** The reusable theorem

```
Matrix.adjugate_fromBlocks_zero₂₁
```

is now proved in `OpenMath/Helpers/BlockAdjugate.lean`. The past-`y`
entry and the rank-one contraction headline remain compiled in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

The remaining mathematical work is not a live proof placeholder: it is to
replace the current existential placeholder
`LMM.toGLM_stabilityCharpolyRowF_eq_explicit` with the actual scalar formula
obtained by applying the block-adjugate identity to the V-active
charmatrix.

## Remaining blocker

The past-`h*f` entry

```
toGLM_stabilityCharpolyRowF
```

is a `vecMul` of the rank-one row against the adjugate at a bottom-half
column:

```
Fin.cast _ (Fin.natAdd s ⟨s - 1, _⟩)
```

After reindexing by `toGLM_stabilityBlockEquiv`, the charmatrix has block
shape

```
fromBlocks
  (toGLM_stabilityMatrixPY m 0).charmatrix
  (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)
  0
  (toGLM_stabilityMatrixPHF m 0).charmatrix
```

The block-adjugate theorem now gives the bottom-column structure:

- bottom-right block:
  `(PY.charmatrix).det • (PHF.charmatrix).adjugate`;
- top-right correction:
  `-(PY.charmatrix).adjugate *
    (-(PYHF.map Polynomial.C)) *
    (PHF.charmatrix).adjugate`.

The residual obstruction is therefore bookkeeping, not missing linear
algebra: push `Matrix.adjugate_fromBlocks_zero₂₁` through
`Matrix.charmatrix_reindex` / `Matrix.adjugate_reindex`, then split
`Matrix.vecMul` over `Sum` and simplify the two row projections
`toGLM_rankOneRow_castAdd` and `toGLM_rankOneRow_natAdd`.

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
Matrix.vecMul_adjugate_apply
Matrix.adjugate_fromBlocks_zero₂₁
LMM.toGLM_stabilityCharpolyRowY_eq_explicit
LMM.toGLM_stabilityMatrix_charpoly_explicit
```

## What was tried

Cycle 661 proved the headline rank-one charpoly identity. Cycle 662
packaged the four sparse-projection lemmas plus the focused contraction
reduction. Cycle 663 added the two named scalar entries and collapsed the
selector sums.

Cycle 664 first exposed the past-`y` entry as a determinant of an updated
top block using `Matrix.vecMul_adjugate_apply`, then closed
`Matrix.adjugate_fromBlocks_zero₂₁` multiplicatively:

```
fromBlocks A B 0 D =
  fromBlocks 1 0 0 D * fromBlocks A B 0 1

fromBlocks A B 0 1 =
  fromBlocks 1 B 0 1 * fromBlocks A 0 0 1
```

The unipotent adjugate follows from the explicit inverse
`fromBlocks 1 (-B) 0 1`, and the diagonal-with-identity adjugates follow
from `Matrix.adjugate_apply`.

## Possible solutions for past-`h*f`

1. State the actual RowF formula in terms of the two block-row pairings:
   the top row paired with
   `(PY.charmatrix).adjugate *
    (PYHF.map Polynomial.C) *
    (PHF.charmatrix).adjugate`
   and the bottom row paired with
   `(PY.charmatrix).det • (PHF.charmatrix).adjugate`.
2. Add a small helper for splitting `Matrix.vecMul` over a
   `Matrix.fromBlocks` column at `Sum.inr q`.
3. Use the existing rank-one row projection lemmas to rewrite the top and
   bottom row functions to `-α ∘ Fin.castSucc` and `β ∘ Fin.castSucc`.

## Downstream after past-`h*f`

Once `toGLM_stabilityCharpolyRowF_eq_explicit` is a real closed form, the
§521 LMM iff bridge `LMM.toGLM_isAStable_iff` should be a root-location
argument over `LMM.toGLM_stabilityMatrix_charpoly_explicit`.
