# Cycle 660 Results

## Worked on
Butcher §521 — Step 2 of the LMM-to-GLM A-stability iff bridge: the
rank-one charpoly update lemma. Specifically, the underlying
matrix-determinant-lemma form for `vecMulVec`, with no `IsUnit M.det`
hypothesis. Active file: `OpenMath/LMMAsGLM.lean`.

## Approach
Followed the cycle plan steps 1-3 in order. Statement: pick the
`vecMulVec` form

```lean
(M + Matrix.vecMulVec u v).det
  = M.det + dotProduct v (M.adjugate.mulVec u)
```

valid for any `CommRing R`. This sidesteps the Mathlib TODO at
`Mathlib.LinearAlgebra.Matrix.SchurComplement.det_add_replicateCol_mul_replicateRow`
which records exactly this generalisation as still open in Mathlib.

Sorry-first scaffolding was kept inline in `OpenMath/LMMAsGLM.lean`
following the strategy default. The proof was prototyped in
`.prover-state/scratch/cycle_660_charpoly_rank_one.lean` against
`Mathlib`'s `MultilinearMap.map_add_univ` and `map_piecewise_smul`,
then transferred.

Aristotle was not attempted — recent cycles have shown sustained 429
behaviour, and the multilinearity proof was already converging
locally inside the Lean LSP.

## Result
SUCCESS.

Added in `OpenMath/LMMAsGLM.lean`:

- `Matrix.sum_finset_le_one_eq` (private helper, cardinality split for
  `Finset n`-indexed sums whose terms vanish at `|S| ≥ 2`).
- `Matrix.det_add_vecMulVec` (the main statement, proved without any
  invertibility hypothesis on `M.det`).

The proof is multilinearity-driven, in seven steps:

1. Recast `(M + vecMulVec u v).det` as a sum over `Finset n` via
   `MultilinearMap.map_add_univ` applied to `detRowAlternating`.
2. Factor `∏_{i ∈ S} u i` out of each subset term using
   `MultilinearMap.map_piecewise_smul`.
3. Show that subset terms with `|S| ≥ 2` vanish (two rows equal `v`
   under the alternating map).
4. Collapse the sum to the `S = ∅` and `S = {k}` contributions via
   `Finset.sum_subset` plus a manual partition into
   `insert ∅ (univ.image fun k => {k})`.
5. Identify the `S = ∅` term as `M.det` and each `S = {k}` term as
   `u k * (M.updateRow k v).det`.
6. Replace `(M.updateRow k v).det` by `∑ j, v j * adjugate M j k`
   using Cramer's rule (`cramer_transpose_apply` +
   `cramer_eq_adjugate_mulVec` + `adjugate_transpose`).
7. Re-pack the resulting double sum as `dotProduct v (adjugate M *ᵥ u)`
   by swapping summation order.

Verification: `lake env lean OpenMath/LMMAsGLM.lean` returns no
errors; `lake build OpenMath.LMMAsGLM` rebuilds with only the
pre-existing simp-arg lints in `BDF.lean`.

File is `3005` lines after the edit (well under the 6000-line hard
cap; just past the 3000 soft target — accepted to keep the helper
local per the cycle 660 strategy default).

## Dead ends
- The `Finset.card_eq_one`-based partition of `Finset n` into
  `insert ∅ (univ.image fun k => {k})` initially failed when phrased
  with a 3-field anonymous constructor on the `mem_image` existential.
  The shape after `simp only [..., Finset.mem_image]` is
  `∃ a, ({a} : Finset n) = S` (after `mem_univ` is rewritten to
  `True`), so the constructor takes 2 fields, not 3.
- Initial smul-factoring tried `map_smul_univ`, but that needs `c i`
  on every coordinate. The piecewise variant `map_piecewise_smul` is
  the correct lemma; it requires showing
  `S.piecewise (fun i => u i • v) M = S.piecewise (fun i => u i • m' i) m'`
  for `m' := S.piecewise (fun _ => v) M`, which is a routine
  case-split on `i ∈ S`.

## Discovery
- Mathlib's `Matrix.det_add_replicateCol_mul_replicateRow` carries an
  in-source TODO: "show the more general version without
  `hA : IsUnit A.det`". The lemma added this cycle is exactly that
  generalisation, in `vecMulVec` form. A potential upstreaming target
  for a future Mathlib PR.
- Used a paired application of `← cramer_transpose_apply` +
  `← adjugate_transpose` to convert `(M.updateRow k v).det` to
  `∑ j, v j * adjugate M j k` cleanly. Avoids the temptation to
  re-prove the cofactor expansion identity from scratch.

## Suggested next approach
- Step 4 of the strategy (assemble the closed form for
  `(m.toGLM.stabilityMatrix z).charpoly`): apply `det_add_vecMulVec`
  in the polynomial ring `(Polynomial ℂ)`, with
  `M := Matrix.charmatrix (toGLM_V_active_lift m)`,
  `u := -Polynomial.C ∘ ((1 / (1 - z * β_last)) • toGLM_rankOneColumn m z)`,
  `v := Polynomial.C ∘ toGLM_rankOneRow m`. The challenge is mapping
  the `Polynomial.C`-lift through `vecMulVec` and matching
  `(M + vecMulVec u v).map Polynomial.C`. A small `charpoly_add_vecMulVec`
  corollary specialised to `R[X]` would be the right packaging.
- Once the explicit charpoly closed form lands, combine with the
  cycle 659 active-`Vℂ` factorisation
  (`toGLM_V_active_charpoly`) to derive a single named identity
  `toGLM_stabilityMatrix_charpoly_explicit` that is the actual
  step-3 deliverable for the iff bridge.
- After step 4, the headline §521 iff theorem
  `toGLM_isAStable_iff` (no BDF assumption) should follow.
