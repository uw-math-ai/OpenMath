# Issue: General LMM-to-GLM charpoly rank-one factorisation

## Blocker

The cycle 641 `Matrix.fromBlocks` decomposition and rank-one update are still
the right structural entry point, but cycle 642 showed that the earlier
"nilpotent past-`h*f` block gives an automatic `X^s` factor" plan is false
for general LMMs.

The past-`h*f` block is only nilpotent in the BDF-shaped case

```lean
∀ l : Fin s, m.β l.castSucc = 0
```

For a concrete counterexample, the trapezoidal rule has `s = 1` and
`PHF[0,0] = z / (2 - z)`, so the single past-`h*f` block is not nilpotent
unless `z = 0`.

## Context

The useful cycle 641 lemmas are in `OpenMath/LMMAsGLM.lean`:

```lean
LMM.toGLM_stabilityMatrix_eq_fromBlocks
LMM.toGLM_stabilityMatrix_eq_V_active_plus_rank_one
```

Cycle 643 landed the BDF-only block helper:

```lean
LMM.toGLM_stabilityMatrixPHF_charpoly_of_bdf
```

It proves that under `∀ l : Fin s, m.β l.castSucc = 0`, the
`toGLM_stabilityMatrixPHF` block is upper-triangular with zero diagonal and
has charpoly `Polynomial.X ^ s`.

## What was tried

- Cycle 641 proved the four block entries for the `s × s` block split and
  reindexed them through `toGLM_stabilityBlockEquiv`.
- Cycle 641 also proved the full stability matrix is a rank-one update of the
  complex `V` block via `Matrix.vecMulVec`.
- Cycle 642 tried to define a polynomial-valued LMM stability polynomial and
  prove a general charpoly factorisation. That attempt was reverted because
  it introduced a live sorry and rested on false general nilpotency.
- Cycle 642 also showed that neither off-diagonal block in the cycle 641
  `fromBlocks` decomposition is zero. Both off-diagonal blocks are rank at
  most one but have a nonzero row at `j = s - 1`, so
  `Matrix.charpoly_fromBlocks_zero₁₂` and
  `Matrix.charpoly_fromBlocks_zero₂₁` do not apply.

## Possible solutions

1. First prove the scaffolded BDF headline
   `LMM.toGLM_stabilityMatrix_charpoly_of_bdf`. The intended reduction is:
   use `LMM.toGLM_stabilityMatrixPHF_charpoly_of_bdf`, then expand the
   `fromBlocks` charmatrix along the rank-one right block row/column.
2. Keep the BDF factorisation existential at first:
   `∃ q, (m.toGLM.stabilityMatrix z).charpoly = Polynomial.X ^ s * q`.
   Do not identify `q` with the LMM stability polynomial until the determinant
   route is stable.
3. For the later general non-BDF theorem, expect a scalar prefactor on the
   left, with a `(1 - z * β_s)`-style denominator-clearing term. The naive
   unscaled shape
   `(m.toGLM.stabilityMatrix z).charpoly = X^s * stabilityPolyPoly z`
   is structurally wrong.
4. Do not use the zero-block charpoly lemmas on the cycle 641 block matrix.
   A direct determinant calculation for the companion-shift-plus-rank-one
   charmatrix is still needed.
