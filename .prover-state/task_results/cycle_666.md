# Cycle 666 Results

## Worked on

§521 Step C.4 — replacing the existential placeholder
`LMM.toGLM_stabilityCharpolyRowF_eq_explicit` with a real closed form,
landing the last piece needed before the §521 iff bridge is a
root-location argument.

## Approach

Followed the strategy template:

1. Added two generic helpers in `OpenMath/Helpers/BlockAdjugate.lean`:

   ```
   Matrix.vecMul_fromBlocks_apply_inr
   Matrix.vecMul_fromBlocks_apply_inl
   ```

   Both proved by
   `simp only [Matrix.vecMul, dotProduct, Matrix.fromBlocks_apply_*,
       Fintype.sum_sum_type, Function.comp_apply]`.

2. Replaced the placeholder
   `toGLM_stabilityCharpolyRowF_eq_explicit (m) : ∃ R, ... = R`
   with the real statement requiring `(hs : 0 < s)`, matching the cycle
   664 RowY shape, expressing `RowF` as the sum of two `Matrix.vecMul`
   entries:

   - top half: `vecMul (-α ∘ castSucc) (-(PY.charmatrix.adjugate) *
       (-(PYHF.map Polynomial.C)) * PHF.charmatrix.adjugate) ⟨s-1, _⟩`
   - bottom half: `vecMul (β ∘ castSucc)
       (PY.charmatrix.det • PHF.charmatrix.adjugate) ⟨s-1, _⟩`

3. Proof recipe:
   - `unfold toGLM_stabilityCharpolyRowF; rw [dif_neg ...]`
   - `show ... m.toGLM.Vℂ ...` to expose the underlying `Vℂ`
     (`toGLM_V_active_lift` is `m.toGLM.Vℂ` by `def`).
   - `rw [toGLM_V_active_lift_eq_fromBlocks_zero, charmatrix_reindex,
       adjugate_reindex, reindex_apply, submatrix_vecMul_equiv]`.
   - `simp only [Equiv.symm_symm, Function.comp_apply,
       toGLM_stabilityBlockEquiv_symm_natAdd]` to collapse
     `e.symm.symm = e` and resolve the bottom-half index.
   - `rw [Matrix.charmatrix_fromBlocks]` then
     `simp only [Matrix.map_zero _ Polynomial.C_0, neg_zero]` to clear
     the bottom-left `-(0).map C` to `0`.
   - `rw [Matrix.adjugate_fromBlocks_zero₂₁]` then
     `rw [Matrix.vecMul_fromBlocks_apply_inr]` to split the row vector
     across `Sum`.
   - `have hrow_inl, hrow_inr` — pointwise rewrites of the row vector
     restricted to `Sum.inl`/`Sum.inr`, using the existing
     `toGLM_rankOneRow_castAdd` and `toGLM_rankOneRow_natAdd` simp
     lemmas, with a small inline `simp [toGLM_stabilityBlockEquiv]`
     bridge.
   - Final cleanup: rewrite `-(A * B * D) = (-A) * B * D` (matrix
     `Matrix.neg_mul` twice) to match the strategy form's leading minus
     placement on `(-A.adjugate)`.

## Result

SUCCESS.

`OpenMath/LMMAsGLM/StabilityCharpoly.lean` (now 428 lines) and
`OpenMath/Helpers/BlockAdjugate.lean` (251 lines) compile sorry-free,
and `lake build` is green.

`toGLM_stabilityMatrix_charpoly_explicit` (the §521 headline) was already
written against `RowF_eq_explicit` parametrically; no consumer changes
were needed once the placeholder was replaced.

## Dead ends

- A multi-line `show` to pin the goal's shape after
  `submatrix_vecMul_equiv` was initially mis-parenthesised. Replaced
  with a `simp only [Equiv.symm_symm, Function.comp_apply,
  toGLM_stabilityBlockEquiv_symm_natAdd]` step that lets Lean reduce
  `e.symm.symm = e` and resolve the bottom-half index without an
  explicit goal-shape annotation.
- First draft of `vecMul_fromBlocks_apply_inr` used
  `Matrix.dotProduct` — the qualified name does not exist (the function
  lives in the root namespace, with infix `⬝ᵥ`). Switched to bare
  `dotProduct` plus explicit `Matrix.fromBlocks_apply_*` lemmas.
- The strategy form's top-right matrix
  `(-A.adjugate) * (-(B.map C)) * D.adjugate`
  differs from the literal `Matrix.adjugate_fromBlocks_zero₂₁` output
  `-(A.adjugate * (-(B.map C)) * D.adjugate)` only by the placement of
  the leading sign. Closed via two applications of `Matrix.neg_mul`
  rather than a heavier `ring`-style proof.

## Discovery

- `Matrix.submatrix_vecMul_equiv` plus `Equiv.symm_symm` is the clean
  path through a `reindex e e M` that avoids any explicit
  cast-and-Sum bookkeeping. The two new helpers
  `vecMul_fromBlocks_apply_{inl,inr}` are tiny, generic, and reusable
  for any future block-vecMul split — adding them is far cheaper than
  inlining `Fintype.sum_sum_type` plus `Sum.elim` unfolds at every
  call site.
- `toGLM_V_active_lift = m.toGLM.Vℂ` definitionally, so a `show`
  rewrite is sufficient to expose `m.toGLM.Vℂ` for
  `toGLM_V_active_lift_eq_fromBlocks_zero` to match. No extra
  `unfold toGLM_V_active_lift` is needed.

## Suggested next approach

The §521 iff bridge `LMM.toGLM_isAStable_iff` is now unblocked. The
roadmap from `toGLM_stabilityMatrix_charpoly_explicit`:

1. Show that `RowY` and `RowF`, as the named scalar adjugate-row
   entries, each carry a factor of `Polynomial.X^s` (or that the
   correction term in `toGLM_stabilityMatrix_charpoly_explicit` does).
   Concretely: spelled out, the active charpoly is
   `PY.charpoly * PHF.charpoly = X^s * <active poly of degree s>`
   under reasonable BDF/non-BDF generality, since `PHF.charpoly = X^s`
   when the past-`h*f` block is the shift (cycle 590-ish discovered
   the companion form for `PHF`).
2. Read off A-stability of the LMM as the root-location of the active
   polynomial, paralleling the existing concrete-method transports
   (`bdf1`, `bdf2`, etc.).

A scratch sorry-first scaffold for the spurious-`X^s` extraction would
fit under `.prover-state/scratch/`. Avoid landing it tracked until the
factorisation is concrete enough to close sorry-free.
