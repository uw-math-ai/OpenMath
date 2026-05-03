# Cycle 710 Results

## Worked on
§521 Steps D.4, D.5, D.3 of `OpenMath/LMMAsGLM/StabilityCharpoly.lean`:
- Target 1 (D.4): `rowFBetaPoly_eval_zero` — `(rowFBetaPoly m).eval 0`
  closed form as the bare `β 0` coefficient (s ≥ 1).
- Target 2 (D.5): `rowFBetaPoly_eval_one` — `(rowFBetaPoly m).eval 1`
  closed form as `∑ k, β(castSucc k)` (no `s ≥ 1` needed).
- Target 3 (D.3): `D_mul_toGLM_charpoly_eval_one_eq` — non-BDF
  `ξ = 1` specialisation of the cycle 698 textbook headline.

## Approach
Followed the strategy verbatim. Inserted all three theorems immediately
after `D_mul_toGLM_charpoly_eval_zero_eq_zero_of_bdf` (formerly the last
theorem before `end LMM`). The strategy templates compiled on first try
for all three targets:
- D.4: `Finset.sum_eq_single (⟨0, hs⟩ : Fin s)` plus `simp [zero_pow hk']`.
- D.5: `Finset.sum_congr rfl` plus inner `simp` (closed without needing
  the explicit `eval_*` rewrite fallback).
- D.3: `rw [h1] at h; simp only [one_pow, mul_one, one_mul] at h;
  linear_combination h`.

## Result
SUCCESS — all three targets land sorry-free. `lake env lean
OpenMath/LMMAsGLM/StabilityCharpoly.lean` compiles cleanly with no
errors and no warnings on the new code. File grew from 1777 to 1842
lines (well under the 3000-line cap).

## Dead ends
None this cycle — the strategy templates were correct as written.

## Discovery
- The strategy's primary template for D.4 (`Finset.sum_eq_single` with
  `(⟨0, hs⟩ : Fin s)` index) works directly; the `Fin.sum_univ_succ`
  alternative was not needed.
- D.5's inner `simp` closes after `eval_finset_sum` + `sum_congr rfl`
  without needing the explicit `rw [Polynomial.eval_mul, eval_pow,
  eval_X, eval_C, one_pow, mul_one]` fallback.
- D.3's `linear_combination h` closes after the `simp only [one_pow,
  mul_one, one_mul]` cleanup of `1^l` and `1^s` powers — `linarith`
  fallback was not needed and `ring_nf` was correctly avoided
  (cycle 696 dead end on `Polynomial.C` coercions).

## Suggested next approach
The strategy's "Suggested followup" section schedules D.6, D.7, D.8,
D.9. The natural next cycle target is **D.6**:
`((toGLM_stabilityMatrixPY m 0).charpoly).eval 0` closed form via
`toGLM_stabilityMatrixPY_zero_charpoly_eq` (line 1443). Strategy
predicts the value collapses to `((m.α 0 : ℝ) : ℂ)` for `s ≥ 1` (the
`X^s` term vanishes; only the `l = 0` summand of the corrective sum
survives, with sign `-(-α 0) = α 0`).

After D.6/D.7 land, **D.8** (combine D.4–D.7 to give a fully concrete
coefficient-form expression for `D · charpoly(0)` and `D · charpoly(1)`)
becomes mechanical. **D.9** (`rowFAlphaPoly` evaluations via
adjugate-at-0) is structurally harder because `rowFAlphaPoly` routes
through `Matrix.vecMul` against an adjugate, but it is the last
missing input for the unit-disk root-counting headline.

The eventual `LMM.toGLM_isAStable_iff` general (non-BDF) headline still
needs a degree-counting lemma not yet in place; D.4–D.9 only assemble
the concrete coefficient-form inputs.
