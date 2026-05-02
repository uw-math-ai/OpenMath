# Cycle 641 Results

## Worked on

Butcher §521 LMM-as-GLM A-stability bridge infrastructure in
`OpenMath/LMMAsGLM.lean`: the general-`s` stability matrix block
decomposition and rank-one resolvent update needed before the charpoly
factorisation.

## Approach

Followed sorry-first:

- Added the four explicit `s × s` block definitions
  `toGLM_stabilityMatrixPY`, `toGLM_stabilityMatrixPYHF`,
  `toGLM_stabilityMatrixPHFY`, and `toGLM_stabilityMatrixPHF`.
- Added four scalar projection lemmas from `m.toGLM.stabilityMatrix z` into
  those blocks, using cycle 638/639 shift-row lemmas and cycle 640 last-row
  closed forms.
- Added `toGLM_stabilityMatrix_eq_fromBlocks`, reindexing the `2*s` matrix by
  `toGLM_stabilityBlockEquiv`.
- Added the rank-one update lemma
  `toGLM_stabilityMatrix_eq_V_active_plus_rank_one`, expressed through
  `Matrix.vecMulVec`.
- Submitted the six-sorry scaffold to Aristotle as project
  `ec11e97b-ba0b-4c0f-aa4e-83cdeeac7aec`. After the mandated 30-minute
  wait, the project was still `IN_PROGRESS` at 9%, so there was no Aristotle
  output to incorporate this cycle.

## Result

SUCCESS for strategy steps 1 and 2:

- `LMM.toGLM_stabilityMatrix_eq_fromBlocks` is sorry-free.
- `LMM.toGLM_stabilityMatrix_eq_V_active_plus_rank_one` is sorry-free.
- `OpenMath/LMMAsGLM.lean` remains below the 3000-line split guard
  (`2352` lines after this cycle).

Step 3 did not land this cycle. I wrote
`.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md` for the missing
general determinant/charpoly bridge.

## Dead ends

The main proof friction was not algebraic; it was the `Fin (s+s)` versus
`Fin (2*s)` reindexing. The right-half constructor simplified sometimes as
`Fin.natAdd` and sometimes as `Fin.addNat`, so the `fromBlocks` proof needed
two small simp lemmas:

- `toGLM_stabilityBlockEquiv_symm_natAdd`
- `toGLM_stabilityBlockEquiv_symm_addNat`

For the charpoly step, Mathlib has useful pieces
(`Matrix.charpoly_reindex`, `Matrix.charpoly_fromBlocks_zero₁₂`,
`Matrix.charpoly_fromBlocks_zero₂₁`, `Matrix.det_one_add_smul`,
`Matrix.det_one_add_replicateCol_mul_replicateRow`), but no direct lemma for
the companion-shift-plus-rank-one determinant shape needed here.

## Discovery

The one-stage LMM-as-GLM stability matrix admits the clean identity

```lean
M(z) = Vℂ + (1 / (1 - z * β_s)) • Matrix.vecMulVec (z • B-column) U-row
```

This avoids separately reasoning about the last past-`y` and last
past-`h*f` rows in the rank-one theorem; the scalar cycle 640 row forms are
still captured in the explicit `fromBlocks` decomposition.

## Suggested next approach

Define a polynomial-valued LMM stability polynomial over `ℂ[X]` with an
evaluation theorem back to `LMM.stabilityPoly`. Then prove a determinant lemma
for the reindexed block matrix/charmatrix shape, likely by induction on `s` or
by repeated sparse row/column expansion, to isolate the nilpotent `X^s` factor
and the active LMM stability factor.
