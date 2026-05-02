# Issue: LMM stability charpoly Step C adjugate contraction

## Blocker

Cycle 661 landed the rank-one charpoly assembly
`LMM.toGLM_stabilityMatrix_charpoly_rankOne`, reducing the full
`m.toGLM.stabilityMatrix z` characteristic polynomial to the active
`Vℂ` characteristic polynomial minus one adjugate dot-product term.

The remaining Step C blocker is the adjugate contraction:

```lean
dotProduct (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
  (((toGLM_V_active_lift m).charmatrix).adjugate.mulVec
    (fun i => Polynomial.C
      (((1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) •
        toGLM_rankOneColumn m z) i)))
```

This must be rewritten to the LMM `α`/`β` polynomial data and combined with
`toGLM_V_active_charpoly`.

## Context

The sparse inputs are explicit but not yet packaged as simp lemmas:

```lean
toGLM_rankOneRow m l = m.toGLM.Uℂ 0 l
toGLM_rankOneColumn m z k = z * m.toGLM.Bℂ k 0
```

On the block reindexing, the row contributes the past-`y` coefficients
`-α (Fin.castSucc q)` and the past-`h*f` coefficients
`β (Fin.castSucc q)`. The column is supported only on rows satisfying
`(q : ℕ) + 1 = s`; in those rows it contributes `z * β_s` in the
past-`y` half and `z` in the past-`h*f` half, scaled by
`1 / (1 - z * β_s)` in the theorem.

Thus the next proof should first collapse the `mulVec` against this sparse
column, then evaluate the resulting adjugate entries of
`(toGLM_V_active_lift m).charmatrix`. Cycle 659 gives the determinant of
that active block, but not the needed cofactor/adjugate-column identities.

## What was tried

Cycle 661 proved:

```lean
Matrix.charpoly_add_vecMulVec
LMM.toGLM_stabilityMatrix_charpoly_rankOne
```

No Aristotle jobs were submitted, per cycle strategy. The Step C algebra was
not forced into the same patch because it needs new adjugate/cofactor
infrastructure rather than another direct rewrite of the determinant lemma.

## Possible solutions

1. Add local simp lemmas for `toGLM_rankOneRow` and `toGLM_rankOneColumn` on
   `Fin.castAdd` and `Fin.natAdd`, phrased with the existing
   `(q : ℕ) + 1 = s` tests so the `s = 0` case stays harmless.
2. Prove a focused lemma for the contraction of
   `(toGLM_V_active_lift m).charmatrix.adjugate.mulVec` against the sparse
   column, probably after reindexing by `toGLM_stabilityBlockEquiv s`.
3. Use `Matrix.adjugate` as cofactors of deleted rows/columns if the direct
   adjugate API is too weak; the relevant minors should inherit the same
   companion/shift triangular structure used in `toGLM_V_active_charpoly`.
4. Finish `LMM.toGLM_stabilityMatrix_charpoly_explicit` by combining the
   contracted term with `toGLM_V_active_charpoly` and
   `stabilityPolyPoly`.
