# Cycle 682 Results

## Worked on
Butcher §521 Step C.8 — name the β-summand polynomial of `RowF` and prove a
degree bound. All work landed in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`,
appended immediately before the closing `end LMM`.

## Approach
Followed the cycle-682 strategy verbatim. Three items, in order:

1. `noncomputable def rowFBetaPoly` — direct paste of the closed form
   factored out of cycle 680's `toGLM_stabilityCharpolyRowF_eq_summand_split`.
2. `theorem toGLM_stabilityCharpolyRowF_eq_alpha_plus_PY_beta` — restatement
   of the cycle 680 split with the second factor folded into `rowFBetaPoly`.
   Proof: `rw [toGLM_stabilityCharpolyRowF_eq_summand_split m hs]; rfl`.
3. `theorem rowFBetaPoly_degree_lt` — `Polynomial.degree`-form bound:
   `(rowFBetaPoly m).degree < (s : WithBot ℕ)`. Proof chain:
   `Polynomial.degree_sum_le` → `Finset.sup_lt_iff (WithBot.bot_lt_coe _)`
   → per-term `Polynomial.degree_C_mul_X_pow_le` → `k.isLt` cast to
   `WithBot ℕ`.

## Result
SUCCESS — all three items closed sorry-free. `lake env lean
OpenMath/LMMAsGLM/StabilityCharpoly.lean` exits 0; LSP `diagnostic_messages`
returns empty. File grew from 988 to 1024 lines (well under the 3000 cap).

## Dead ends
None this cycle — strategy was tight and the Mathlib lemmas matched the
sketch one-for-one. The only mild divergence from the strategy sketch:
`Finset.sup_lt_iff` needed `⊥ < (s : WithBot ℕ)`, which is
`WithBot.bot_lt_coe _` rather than a `Nat.pos_of_ne_zero` argument. This
also makes the bound work for `s = 0` (empty sum has degree `⊥`,
`(0 : WithBot ℕ) = some 0`, and `⊥ < some 0`).

## Discovery
The `Polynomial.degree` form (`WithBot ℕ`) plays nicely with the empty-sum
case via `WithBot.bot_lt_coe`, so no `0 < s` hypothesis was needed. This
keeps `rowFBetaPoly_degree_lt` clean for downstream consumers.

## Suggested next approach
The headline `LMM.toGLM_isAStable_iff` still needs a degree-counting
argument on the α-summand
`∑ l : Fin s, (vecMul (α-row) (-PY.adj * -PYHF.map C)) l * X^l`. The
α-summand is structurally a `vecMul` against `PY.adj` (dense) and `PYHF.map C`
(rank-one column-zero), so its per-`l` coefficient is a polynomial of
controlled degree. A natural next cycle:

* Define `noncomputable def rowFAlphaPoly (m : LMM s) (l : Fin s) : Polynomial ℂ`
  for the per-`l` row coefficient (the inner `vecMul` evaluated at `l`).
* State and prove `rowFAlphaPoly m l |>.degree ≤ ((s - 1 : ℕ) : WithBot ℕ)`
  (the adjugate of `PY.charmatrix` has degree-≤(s-1) entries).
* Combine with `rowFBetaPoly_degree_lt` to bound `RowF.degree` relative
  to `PY.charpoly.degree = s`.

That would be the third leg needed before the `toGLM_isAStable_iff`
characterization can be stated cleanly.
