# Cycle 500 Results

## Worked on
Butcher §382 raw `ButcherProduct` definition and block-structure / weights-sum
sanity lemmas in `OpenMath/ButcherGroup.lean`.

## Approach
Followed the cycle 500 strategy verbatim:
1. Appended `ButcherProduct {s t : ℕ} : ButcherTableau s → ButcherTableau t → ButcherTableau (s + t)`
   to `OpenMath/ButcherGroup.lean`. The matrix `A` is given by a literal
   nested `Fin.addCases` (block lower-triangular: `t₁.A` upper-left,
   `t₂.A` lower-right, `t₁.b` broadcast in the lower-left strip, `0`
   upper-right). `b` is the concatenation of `t₁.b` and `t₂.b`. `c` is
   `(t₁.c, 1 + t₂.c)`.
2. Added four `@[simp]` block-structure computation lemmas:
   `butcherProduct_b_castAdd`, `butcherProduct_b_natAdd`,
   `butcherProduct_c_castAdd`, `butcherProduct_c_natAdd`. All four close by
   `simp [ButcherProduct]` (the bare `simp` set already knows
   `Fin.addCases_left` / `_right` in this toolchain).
3. Added the weights-sum sanity lemma `butcherProduct_b_sum` showing
   `∑ i, (ButcherProduct t₁ t₂).b i = (∑ i, t₁.b i) + (∑ i, t₂.b i)`,
   which closes by `rw [Fin.sum_univ_add]; simp [ButcherProduct]`.

## Result
SUCCESS. `lake env lean OpenMath/ButcherGroup.lean` exits 0 with no output;
`rg -n "sorry" OpenMath/ButcherGroup.lean` reports no matches. Six new
sorry-free theorems plus one definition added, file grew from 302 to 379
lines.

## Aristotle
No Aristotle jobs submitted this cycle. As the strategy noted, the surface
is small (one definition + five lemmas, all definitional unfolding) and
prior cycles (495 / 497 / 498) showed Aristotle returns only stub-import
`COMPLETE_WITH_ERRORS` results on `ButcherGroup.lean`. Saved the queue.

## Dead ends
None. The `simp [ButcherProduct]` invocation worked on the first attempt for
all four block-structure lemmas; no need for the explicit
`Fin.addCases_left` / `_right` fallback or `unfold ButcherProduct; rfl`.

## Discovery
- `Fin.sum_univ_add` is the correct Mathlib name for the splitting lemma
  `∑ i : Fin (s + t), f i = ∑ i : Fin s, f (Fin.castAdd t i) + ∑ i : Fin t, f (Fin.natAdd s i)`.
- The bare `simp` set in this toolchain already unfolds `Fin.addCases` on
  `Fin.castAdd` / `Fin.natAdd` — no `simp only` whitelist needed.

## Suggested next approach
The natural next cycle is to lift `ButcherProduct` to a binary operation
`QuotEquiv s → QuotEquiv t → QuotEquiv (s + t)`. This requires a
well-definedness proof under simultaneous relabeling of both arguments
(i.e. if `t₁ ~ t₁'` via `σ : Equiv.Perm (Fin s)` and `t₂ ~ t₂'` via
`τ : Equiv.Perm (Fin t)`, then `ButcherProduct t₁ t₂ ~ ButcherProduct t₁' t₂'`
via the block permutation `Equiv.sumCongr σ τ` transported through
`finSumFinEquiv`). After that, associativity-modulo-relabel on
`QuotEquiv (s + t + u)` becomes attackable: `(t₁ ∘ t₂) ∘ t₃` and
`t₁ ∘ (t₂ ∘ t₃)` differ at the raw tableau by the natural Fin associator,
so the witnessing permutation is `Equiv.symm finAssoc` (or its image
through `finSumFinEquiv`). Both routes are documented in the §382
issue file at `.prover-state/issues/butcher_section382_composition.md`.

Associativity on `QuotEquiv` is intentionally deferred per the strategy;
this cycle was strictly the prerequisite definitional layer.
