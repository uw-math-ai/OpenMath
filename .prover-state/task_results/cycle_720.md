# Cycle 720 Results

## Worked on
§521 Step D.13 + D.14a/b/c/d — `rowYQuot` cofactor expansion as
`∑ k, C(-α_k) * adjugate k ⟨s-1, _⟩` and its `eval ξ` follow-ups.

Append site: end of `OpenMath/LMMAsGLM/StabilityCharpoly.lean`, just
before `end LMM`. File grew from 2087 to 2138 lines (still under cap).

## Approach

### D.13 (`rowYQuot_eq_adjugate_sum`)
Followed the strategy's Cramer-via-transpose route, but with a
correction: the strategy claimed `Matrix.cramer_apply` lands in the
`∑ j, A.adjugate i j * b j` form, but the actual Mathlib lemma is

```
Matrix.cramer_apply : cramer A b i = (A.updateCol i b).det
```

i.e. the *column*-update form, not the adjugate sum. The adjugate
identity actually lives in

```
Matrix.cramer_eq_adjugate_mulVec : cramer A b = A.adjugate *ᵥ b
```

So the working pipeline is:

1. `unfold rowYQuot; rw [dif_neg hs.ne']` — drop the `s = 0` branch.
2. `rw [← Matrix.cramer_transpose_apply]` — recast
   `(A.updateRow i b).det` as `cramer Aᵀ b i`.
3. `rw [Matrix.cramer_eq_adjugate_mulVec]` — recast as
   `(Aᵀ.adjugate *ᵥ b) i`.
4. `rw [Matrix.mulVec_eq_sum]` — convert `mulVec` to `∑`.
5. `simp [Matrix.adjugate_transpose, mul_comm]` — `Aᵀ.adjugate = (A.adjugate)ᵀ`,
   then transpose-apply and `mul_comm` to match the `C(-α) * adjugate`
   shape on the RHS. Both `simp` lemmas are required (verified by
   testing without them); only `Matrix.transpose_apply` was unused.

### D.14a (`rowYQuot_eval_eq_sum`)
Verbatim from the strategy: `Polynomial.eval_finset_sum` then per-term
`Polynomial.eval_mul, Polynomial.eval_C`.

### D.14b/c (`rowYQuot_eval_zero_eq_sum`, `rowYQuot_eval_one_eq_sum`)
One-liners specialising D.14a at `ξ = 0` and `ξ = 1`.

### D.14d (`rowYQuot_eval_one_eq_sum_of_bdf`)
Stretch landed: BDF-named wrapper around D.14c; `_hbdf` is unused (per
strategy — pure naming bridge for downstream callers). Renamed to
`_hbdf` to silence the unused-arg linter.

## Result
SUCCESS — all five theorems landed; `lake env lean
OpenMath/LMMAsGLM/StabilityCharpoly.lean` is silent.

## Dead ends
- The strategy's literal proof skeleton uses `Matrix.cramer_apply`
  followed by `simp_rw [Matrix.adjugate_transpose, Matrix.transpose_apply,
  mul_comm]`. That sequence does not close the goal because
  `cramer_apply` produces the `updateCol` form, not the adjugate sum.
  Replacing with `cramer_eq_adjugate_mulVec` + `mulVec_eq_sum` works.
- Trying `simp [Matrix.mulVec, Matrix.dotProduct, ...]` fails:
  `Matrix.dotProduct` is not the qualified name (it lives at
  top-level `dotProduct` in scope, with the `⬝ᵥ` notation). Use
  `Matrix.mulVec_eq_sum` instead, which produces a literal `∑ x, ...`.

## Discovery
- `Matrix.cramer_eq_adjugate_mulVec` (Mathlib
  `LinearAlgebra/Matrix/Adjugate.lean`) is the right bridge between
  Cramer-determinant and adjugate-sum forms; it is more directly
  useful than `Matrix.cramer_apply` for cofactor-expansion proofs.
- `Matrix.mulVec_eq_sum` produces a literal `Finset.sum` (with a
  `MulOpposite.op` smul that `simp` collapses for commutative rings),
  saving an explicit `simp_rw [Matrix.mulVec, Matrix.dotProduct]`
  step that fails because `dotProduct` is not in the `Matrix`
  namespace.

## Suggested next approach
- Cycle 721 should attempt the next concrete seam: pushing
  `Polynomial.eval ξ` through the `vecMul ∘ adjugate ∘ map C` chain
  that defines `rowFAlphaResidual`. Cycle 716 / 718 task results
  flagged this as opaque to current tactics, but with D.13 in hand
  the analogous recipe should work: rewrite via
  `cramer_eq_adjugate_mulVec` after unfolding the `vecMul` to a sum.
- Concretely: state a `rowFAlphaResidual_eq_double_adjugate_sum`
  lemma that expands the `vecMul (-α) (adjugate ... * (-PYHF) *
  adjugate ...)` row into a double sum over `(k, j)`, then specialise
  at ξ ∈ {0, 1}. The BDF case will collapse half the sum via
  `toGLM_stabilityMatrixPYHF_eq_zero_of_bdf`.
- Once that lands, the iff bridge `toGLM_charpoly_eval_one_eq_zero_iff`
  becomes a `simp`-after-substitution lemma; that is the next major
  textbook headline.
