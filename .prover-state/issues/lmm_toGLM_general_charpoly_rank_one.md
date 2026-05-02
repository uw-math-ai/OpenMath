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

## Cycle 642 update

Items 1 and the BDF-case half of item 2 landed sorry-free in
`OpenMath/LMMAsGLM.lean`:

- `LMM.stabilityPolyPoly` and `LMM.stabilityPolyPoly_eval`
- `LMM.toGLM_stabilityMatrixPHF_charpoly_of_explicit_past`

Two important corrections to the strategy's plan:

1. **PHF is not nilpotent in general.** The strategy claimed
   `toGLM_stabilityMatrixPHF` is nilpotent so its charpoly is `X^s`, but the
   bottom row of PHF (when `j+1 = s`) carries entries
   `z β_l / (1 - z β_s)`. For BDF methods these vanish (`β_l = 0` for past
   slots), but for trapezoidal / Adams-Moulton they do not. Cycle 642's
   helper is therefore conditioned on `∀ l, m.β l.castSucc = 0` (BDF
   shape). For the general case, PHF's charpoly is the charpoly of a
   transposed companion matrix, namely
   `X^s - (z β_{s-1}/(1-z β_s)) X^{s-1} - … - (z β_0/(1-z β_s))`.

2. **Neither off-diagonal block of the cycle-641 fromBlocks is zero.** The
   strategy suggested using `Matrix.charpoly_fromBlocks_zero₁₂` /
   `_zero₂₁`, but `toGLM_stabilityMatrixPYHF` and
   `toGLM_stabilityMatrixPHFY` are only zero in their first `s − 1` rows;
   row `s − 1` carries the resolvent contribution. They are however
   rank-≤1 (each is a single nonzero row times an indicator). The headline
   step 3 should exploit this rank-≤1 structure directly, e.g. via
   `Matrix.det_one_add_replicateCol_mul_replicateRow` after a
   denominator-clearing rescale.

3. **Headline shape adjustment.** The cleaned headline statement that
   matches BDF2 / trapezoidal hand calculations is
   ```
   (1 - z * β_s) • (m.toGLM.stabilityMatrix z).charpoly
       = Polynomial.X ^ s * m.stabilityPolyPoly z
   ```
   not the uncleared
   `(m.toGLM.stabilityMatrix z).charpoly = X^s * m.stabilityPolyPoly z`
   originally suggested in the strategy. The scalar `(1 - z β_s)` on the
   LHS absorbs the natural denominator on the active block charpoly so the
   identity is well-defined as a polynomial relation in `ℂ[X]` even at the
   singular value `z β_s = 1`.

## Suggested next cycle (643) plan

1. Generalize `toGLM_stabilityMatrixPHF_charpoly` to drop the
   `hβ : ∀ l, m.β l.castSucc = 0` hypothesis. The general charpoly of PHF
   is the transposed-companion-matrix charpoly (see correction 1 above).
   For Mathlib, search around `Matrix.charpoly_companion` /
   `Matrix.companionMat`. If absent, prove sparse-row determinant
   expansion for the specific PHF shape.
2. Close `LMM.toGLM_stabilityMatrix_charpoly` using cycle 641's
   `toGLM_stabilityMatrix_eq_fromBlocks` plus the rank-≤1 off-diagonal
   structure noted in correction 2 above. Try
   `Matrix.det_one_add_smul` after denominator clearing.
3. Once the headline lands, `LMM.toGLM_isAStable_iff` follows from
   `Polynomial.eval_pow`, `stabilityPolyPoly_eval`, and the LMM-side
   `IsAStable` definition.
