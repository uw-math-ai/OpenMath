# Cycle 664 Results

## Worked on
Butcher §521 Step C.3 — evaluate the two named scalar adjugate-row
entries `toGLM_stabilityCharpolyRowY` and `toGLM_stabilityCharpolyRowF`
of the LMM-as-GLM stability charpoly bridge. Created the new helper
module `OpenMath/Helpers/BlockAdjugate.lean` and extended
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

## Approach
1. Created `OpenMath/Helpers/BlockAdjugate.lean` with two lemmas:
   - `Matrix.vecMul_adjugate_apply` (the row-vector form of Cramer's
     rule: `vecMul x A.adjugate j = (A.updateRow j x).det`) — proved
     via `mulVec_transpose` + `adjugate_transpose` + `cramer_eq_adjugate_mulVec`
     + `cramer_transpose_apply`.
   - `Matrix.adjugate_fromBlocks_zero₂₁` (block adjugate identity for
     `fromBlocks A B 0 D`) — sorry-first scaffold; proof deferred.
2. In `StabilityCharpoly.lean`, added:
   - private helpers `reindex_updateRow_eq` and
     `fromBlocks_zero₂₁_updateRow_castAdd` for moving an `updateRow`
     past `Matrix.reindex` and across the `fromBlocks A B 0 D` shape.
   - `toGLM_stabilityCharpolyRowY_eq_explicit` (PROVED sorry-free):
     expresses the past-`y` entry as
     `det(updateRow (PY.charmatrix, s-1, -α∘Fin.castSucc)) *
      (PHF.charpoly)`, by unfolding via `Matrix.vecMul_adjugate_apply`,
     pushing the `updateRow` through `Matrix.reindex` and the block
     decomposition (`Matrix.charmatrix_fromBlocks` + `Matrix.map_zero`
     + `Polynomial.C_0`), then collapsing with `det_fromBlocks_zero₂₁`.
   - `toGLM_stabilityCharpolyRowF_eq_explicit` (placeholder existential
     `⟨_, rfl⟩`) — full evaluation deferred until
     `adjugate_fromBlocks_zero₂₁` lands.
   - `toGLM_stabilityMatrix_charpoly_explicit` (PROVED sorry-free) —
     the §521 Step C.3 headline combining the rank-one identity, the
     contraction explicit form, and `toGLM_V_active_charpoly`.

## Result
SUCCESS (partial, as planned). Landed:

- `Matrix.vecMul_adjugate_apply` (sorry-free)
- `Matrix.adjugate_fromBlocks_zero₂₁` (sorry-first; deferred)
- `LMM.toGLM_stabilityCharpolyRowY_eq_explicit` (sorry-free)
- `LMM.toGLM_stabilityCharpolyRowF_eq_explicit` (trivial existential)
- `LMM.toGLM_stabilityMatrix_charpoly_explicit` (sorry-free)

Verification:
- `lake env lean OpenMath/Helpers/BlockAdjugate.lean` — only the
  expected `sorry` warning on `adjugate_fromBlocks_zero₂₁`.
- `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` — clean.
- `lake env lean OpenMath/LMMAsGLM.lean` — clean.

## Dead ends
- Initial attempts to evaluate `toGLM_stabilityCharpolyRowY` by going
  directly through `Matrix.adjugate_fromBlocks_zero₂₁` failed because
  that block adjugate identity is not yet proved. The
  `vecMul_adjugate_apply` route side-steps the block adjugate entirely
  for the past-`y` case: updating a top-half row of
  `fromBlocks A B 0 D` keeps the lower-left block zero, so
  `det_fromBlocks_zero₂₁` applies directly. This is why past-`y` lands
  but past-`h*f` does not — updating a bottom-half row destroys the
  upper-triangular structure.
- `Matrix.vecMul_transpose` failed to rewrite (wrong direction); used
  `← Matrix.mulVec_transpose` instead.
- `congr 1; congr 1; funext k` over-descended into the goal after
  `det_fromBlocks_zero₂₁`; switched to extracting an explicit
  function-equality lemma (`hrow`), rewriting it, then `rfl`.
- `(0 : Matrix _ _ _).map ⇑Polynomial.C` did not simplify with `show`
  or `rw [show ... from neg_zero]` (OfNat synthesis errors); resolved
  with `simp only [Matrix.map_zero _ Polynomial.C_0, neg_zero]`.
- `toGLM_V_active_lift_eq_fromBlocks_zero` pattern not matching after
  `unfold toGLM_stabilityCharpolyRowY` / `rw [dif_neg ...]`; resolved
  by inserting an explicit `show m.toGLM.Vℂ.charmatrix.updateRow ...`
  step before the rewrite.
- `toGLM_stabilityMatrix_charpoly_rankOne hz` rewrite needed the
  matrix `m` passed explicitly to avoid a unification failure on
  `(toGLM ?m).stabilityMatrix ?z`.

## Discovery
The cleanest path through Step C.3 past-`y` is to expose the row-update
form `vecMul x A.adjugate j = (A.updateRow j x).det` *first*, then push
`updateRow` through `Matrix.reindex` and `Matrix.charmatrix_fromBlocks`.
The lower-left block stays zero because only a top-half row was updated,
so the full block adjugate identity is not actually required for the
past-`y` entry — only `det_fromBlocks_zero₂₁`. The block adjugate
identity is still required for the past-`h*f` entry, where the bottom
row update breaks the triangular shape.

## Suggested next approach
Cycle 665 should close `Matrix.adjugate_fromBlocks_zero₂₁` in
`OpenMath/Helpers/BlockAdjugate.lean`. The cleanest argument is the
`adjugate * M = det • 1` characterization:
- compute `Matrix.fromBlocks (D.det • A.adj) (-A.adj * B * D.adj) 0
  (A.det • D.adj) * Matrix.fromBlocks A B 0 D` block-by-block;
- check the result equals `(A.det * D.det) • 1 =
  (fromBlocks A B 0 D).det • 1` via `det_fromBlocks_zero₂₁`;
- conclude with `Matrix.eq_adjugate_of_mul_eq_det_smul_one` or its
  named analogue (search for `adjugate_unique`/`adjugate_of_*`).
Once the block adjugate is in hand, evaluate
`toGLM_stabilityCharpolyRowF_eq_explicit` by replaying the
`vecMul_adjugate_apply` route on `fromBlocks` *after* unfolding the
block adjugate's columns at the bottom-half index. The off-diagonal
correction `-(A.adj * B * D.adj)` is what carries the past-`h*f`
contribution once paired with the rank-one row.
