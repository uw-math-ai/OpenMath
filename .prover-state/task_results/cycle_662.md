# Cycle 662 Results

## Worked on

Butcher §521 — Step C: adjugate contraction for the LMM-as-GLM
stability charpoly. Per planner, all new content lands in the new
sibling module `OpenMath/LMMAsGLM/StabilityCharpoly.lean`, not in
`OpenMath/LMMAsGLM.lean` (3062 lines, near soft cap).

## Approach

1. Made `toGLM_V_active_lift`, `toGLM_rankOneColumn`, `toGLM_rankOneRow`,
   `toGLM_rankOneCorrection` non-`private` in `OpenMath/LMMAsGLM.lean`
   so the new sibling module can refer to them. (Strategy permits this
   one-token edit.)
2. Created `OpenMath/LMMAsGLM/StabilityCharpoly.lean` and landed
   Subtask 1 sparse-projection simp lemmas through the past-`y` /
   past-`h*f` block reindex:

   - `LMM.toGLM_rankOneRow_castAdd` and `LMM.toGLM_rankOneRow_natAdd`
   - `LMM.toGLM_rankOneColumn_castAdd` and `LMM.toGLM_rankOneColumn_natAdd`

3. Landed Subtask 2's named helper:
   `LMM.toGLM_stabilityMatrix_charpoly_rankOne_contraction`. It pulls
   out the resolvent prefactor `Polynomial.C (1 / (1 - z β_s))`,
   converts `dotProduct (Polynomial.C ∘ row) (adjugate.mulVec
   (Polynomial.C ∘ (c • col)))` to `dotProduct (vecMul ...) (...)`,
   reindexes the dot-product into the past-`y` and past-`h*f` halves
   via `Equiv.sum_comp` plus `Fin.sum_univ_add`, and rewrites both
   halves with the Subtask-1 sparse column simp lemmas.

   The result expresses the contraction as a sum over `q : Fin s` of
   four structurally explicit terms with the column entries collapsed
   to `if (q : ℕ) + 1 = s then ⋯ else 0`, ready for further evaluation
   of the `vecMul` against the block-triangular adjugate.

## Result

SUCCESS for Subtasks 1 and 2 (named-helper form per planner fallback).

Both files compile cleanly:

```bash
lake env lean OpenMath/LMMAsGLM.lean
lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean
lake build OpenMath.LMMAsGLM.StabilityCharpoly
```

No new sorries on `main`. The new module is sorry-free; Subtask 3
`toGLM_stabilityMatrix_charpoly_explicit` is **not** landed this
cycle (it requires the adjugate-evaluation step recorded in the
updated `lmm_stability_charpoly_step_c.md`).

## Dead ends

- A first attempt to use `Finset.map_univ_equiv` to reindex
  `Finset.univ : Finset (Fin (2*s))` through `Fin.cast (Nat.two_mul s).symm`
  failed because the resulting goal had a raw `Function.Embedding`
  rather than `Equiv.toEmbedding`. Replaced with
  `(finCongr (Nat.two_mul s).symm).sum_comp` — much cleaner.
- The Subtask 1 `toGLM_rankOneRow_natAdd` lemma did **not** close with
  a single `simp [toGLM_rankOneRow]` because of an `addNat` vs
  `natAdd` mismatch in the goal after simp. Replaced with explicit
  `unfold toGLM_rankOneRow; rw [toGLM_Uℂ_natAdd]`.

## Discovery

- The `Matrix.dotProduct_mulVec` swap from
  `dotProduct row (M.mulVec v)` to `dotProduct (vecMul row M) v` is
  the cleanest route for reducing sparse-vector contractions: it
  moves the sparsity onto the `dotProduct` side directly, where
  `Finset.sum_eq_single` / sparse-projection simp lemmas can act.
- For the resolvent prefactor pull-out, the chain
  `Polynomial.C_mul → Pi.smul_def → Matrix.mulVec_smul → dotProduct_smul`
  factors `Polynomial.C c` cleanly out of the entire contraction.
- Removing `private` from `toGLM_rankOneColumn`, `toGLM_rankOneRow`,
  `toGLM_V_active_lift` did not require any other edits inside
  `LMMAsGLM.lean` — the existing proofs continued to elaborate.

## Suggested next approach

Tackle Step C.2 (route 1 in the updated issue):

1. Prove a self-contained Mathlib-style helper for the adjugate of a
   block-upper-triangular matrix `Matrix.fromBlocks A B 0 D`,
   expressed in terms of `A.adjugate`, `D.adjugate`, `A.det`, `D.det`,
   and the off-diagonal correction.
2. Apply it to `(toGLM_V_active_lift m).charmatrix` after
   `toGLM_V_active_lift_eq_fromBlocks_zero`.
3. Combine with `toGLM_stabilityMatrixPYCompanion_charpoly` (cycle
   658) and the cycle-662 contraction lemma to land
   `LMM.toGLM_stabilityMatrix_charpoly_explicit`.

This should be one focused cycle, possibly two if the block adjugate
identity needs a Mathlib-side companion lemma.
