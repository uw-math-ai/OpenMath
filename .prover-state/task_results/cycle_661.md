# Cycle 661 Results

## Worked on

Butcher §521 — Step 4 rank-one characteristic polynomial assembly for
`m.toGLM.stabilityMatrix z` in `OpenMath/LMMAsGLM.lean`.

## Approach

Followed the planner target directly. First packaged the cycle-660
determinant identity as a polynomial-ring charpoly corollary:

```lean
Matrix.charpoly_add_vecMulVec
```

Then specialised it to the cycle-641 LMM-as-GLM rank-one decomposition:

```lean
LMM.toGLM_stabilityMatrix_charpoly_rankOne
```

Aristotle was not used, per strategy. The proof was local/LSP-driven and
uses `Matrix.det_add_vecMulVec` rather than reproving any determinant
multilinearity.

## Result

SUCCESS for Steps A+B.

Added `Matrix.charpoly_add_vecMulVec` with no `IsUnit` or `Invertible`
hypothesis. The proof rewrites the charmatrix of
`M + Matrix.vecMulVec u v` as
`M.charmatrix + Matrix.vecMulVec (-Polynomial.C ∘ u) (Polynomial.C ∘ v)`,
then applies `Matrix.det_add_vecMulVec`.

Added `LMM.toGLM_stabilityMatrix_charpoly_rankOne`, which rewrites
`m.toGLM.stabilityMatrix z` by
`toGLM_stabilityMatrix_eq_V_active_plus_rank_one` and absorbs the scalar
prefactor into the rank-one column.

Verification:

```bash
lake env lean OpenMath/LMMAsGLM.lean
```

completed successfully.

## Dead ends

Step C was not completed this cycle. The remaining term is not another
determinant rewrite; it requires a new adjugate/cofactor calculation for
`(toGLM_V_active_lift m).charmatrix` against the sparse rank-one column and
row.

## Discovery

The polynomial-ring corollary is short once the sign is placed on the lifted
column:

```lean
u' := fun i => -Polynomial.C (u i)
v' := fun j => Polynomial.C (v j)
```

The LMM specialisation also needs only the matrix-level identity

```lean
c • Matrix.vecMulVec col row =
Matrix.vecMulVec (c • col) row
```

which is pointwise `simp` plus associativity.

## Suggested next approach

Work from `.prover-state/issues/lmm_stability_charpoly_step_c.md`.
Start by adding block-index simp lemmas for `toGLM_rankOneRow` and
`toGLM_rankOneColumn`, then prove a focused adjugate contraction lemma after
reindexing `toGLM_V_active_lift m` by `toGLM_stabilityBlockEquiv s`.
