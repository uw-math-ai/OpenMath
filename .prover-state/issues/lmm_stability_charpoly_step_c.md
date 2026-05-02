# Issue: LMM stability charpoly Step C adjugate contraction

## Status

**Step C.2 landed (cycle 663).** The rank-one column collapse, selector
collapse, and named scalar adjugate-row entries now live in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`. The contraction is packaged as
`LMM.toGLM_stabilityMatrix_charpoly_rankOne_contraction_explicit`.
What remains is **Step C.3** — evaluating the two named
`vecMul`-against-adjugate entries.

## Blocker (remaining)

Cycle 661 reduced the full LMM-as-GLM stability charpoly to one adjugate
dot-product term. Cycle 662's contraction lemma reduced that dot-product
to two selector sums. Cycle 663 collapsed those sums to:

```lean
Polynomial.C (1 / (1 - z β_s)) *
  (toGLM_stabilityCharpolyRowY m * Polynomial.C (z β_s)
   + toGLM_stabilityCharpolyRowF m * Polynomial.C z)
```

The remaining gap is to evaluate the named `vecMul` entries — i.e. the
`adjugate` columns of `(toGLM_V_active_lift m).charmatrix` at the
two indices `Fin.cast (Nat.two_mul s).symm (Fin.castAdd s ⟨s-1, _⟩)`
and `Fin.cast (Nat.two_mul s).symm (Fin.natAdd s ⟨s-1, _⟩)` — paired
against the rank-one row.

## Context

The active matrix `toGLM_V_active_lift m = m.toGLM.Vℂ` was shown
block-triangular at `z = 0` in cycle 659:
`toGLM_V_active_lift_eq_fromBlocks_zero` and
`toGLM_V_active_charpoly`. The `Vℂ` charmatrix inherits the same
block-upper-triangular structure (only the upper-right block has
non-zero off-diagonal entries in the polynomial-lifted form).

The PHF block at `z = 0` is the strict-shift companion (nilpotent of
order ≤ s), so `(toGLM_stabilityMatrixPHF m 0).charmatrix` has a
computable adjugate. The PY block at `z = 0` is the bottom-row
companion of `m.α` (cycle 658 / `toGLM_stabilityMatrixPYCompanion`).

## Sparse helpers landed (cycles 662-663)

```
LMM.toGLM_rankOneRow_castAdd            -- = -α (Fin.castSucc q)
LMM.toGLM_rankOneRow_natAdd             -- =  β (Fin.castSucc q)
LMM.toGLM_rankOneColumn_castAdd         -- = if q+1=s then z β_s else 0
LMM.toGLM_rankOneColumn_natAdd          -- = if q+1=s then z     else 0
LMM.toGLM_stabilityMatrix_charpoly_rankOne_contraction
LMM.toGLM_stabilityCharpolyRowY
LMM.toGLM_stabilityCharpolyRowF
LMM.sum_castAdd_selector_collapse
LMM.sum_natAdd_selector_collapse
LMM.toGLM_stabilityMatrix_charpoly_rankOne_contraction_explicit
```

## What was tried

Cycle 661 proved `Matrix.charpoly_add_vecMulVec` and
`LMM.toGLM_stabilityMatrix_charpoly_rankOne` (the headline rank-one
charpoly identity). Cycle 662 packaged the four sparse-projection
simp lemmas above plus the focused contraction reduction lemma. Cycle
663 added the two named scalar entries and collapsed the two selector
sums with `Finset.sum_eq_single`, keeping all new work in the sibling
module `OpenMath/LMMAsGLM/StabilityCharpoly.lean` to avoid growing
`OpenMath/LMMAsGLM.lean`.

One Aristotle job was submitted for the four new sorry-first goals, but
the proofs were closed manually before waiting on the queued result.

## Possible solutions for Step C.3

1. Block-triangular adjugate identity: prove a self-contained helper
   for the adjugate of `Matrix.fromBlocks A B 0 D` (the relevant case
   here is the block charmatrix of `toGLM_V_active_lift`). The
   resulting adjugate has block-upper-triangular shape with diagonal
   blocks `D.det • A.adjugate` and `A.det • D.adjugate`, plus a known
   off-diagonal correction.
2. Direct cofactor: evaluate the two needed columns of
   `(toGLM_V_active_lift m).charmatrix.adjugate` by Laplace expansion.
   The `castAdd s ⟨s-1, _⟩` column is the (PY-row, PY-col) deletion
   minor — a charmatrix of the shifted PY companion. The
   `natAdd s ⟨s-1, _⟩` column is mixed.
3. Pair-then-evaluate: compute the `vecMul` of the rank-one row against
   the adjugate before evaluating the adjugate itself, using
   `Matrix.adjugate_mulVec_eq_det_smul` or its transposed analogue.

Recommended starting point is route (1): the block-triangular adjugate
helper is reusable and the Mathlib gap (if any) is well-scoped.

## Down-stream after Step C.3

Once the `vecMul` entries are evaluated, the contracted scalar can be
combined with `toGLM_V_active_charpoly` (cycle 659) to land
`LMM.toGLM_stabilityMatrix_charpoly_explicit`, then the §521 LMM iff
bridge `LMM.toGLM_isAStable_iff` follows by routine root-location.
