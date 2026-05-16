# Cycle 310 Results

## Worked on
§342 Phase 3.1 of the §342 ↔ §321 Gauss–Legendre `RKTableau` lift (`cor:342D` C(n) prong):
- **P1** `butcherShiftedLegendre_collocation_exact_lt_n` — upper-limit-parametrised collocation exactness on `[0, cᵢ]`.
- **P2** `butcherGaussLegendreRK_satisfiesC` — `(butcherGaussLegendreRK n).SatisfiesC n` for the general-`n` Gauss–Legendre `RKTableau`.
- **P3.a** Round-trip `gaussLegendre1Stage.SatisfiesC 1` example through P2 at `n = 1` (downstream-consumability witness).
- **P3.b** Non-vacuity `(butcherGaussLegendreRK 2).SatisfiesC 2` example at `n = 2`.

All three deliverables in `OpenMath/Chapter3/Section342.lean`, appended after the cycle 309 Phase 2 block (`butcherGaussLegendreRK_satisfiesB` headline and witnesses).

## Approach
**P1**: Verbatim port of cycle 303's `butcherShiftedLegendre_quadrature_exact_lt_n` recipe, with the upper bound `1` swapped to `butcherShiftedLegendre_zeros n i`. The proof body is byte-for-byte identical aside from this swap and the final `rw [butcherShiftedLegendre_collocationA]` (cycle 308's A-matrix def) replacing cycle 303's `_quadratureWeights` unfold. Every `intervalIntegral.*` lemma used (`integral_finset_sum`, `integral_const_mul`, `Continuous.intervalIntegrable`) is bound-agnostic, confirming R1/R2/R3 of the strategy risk register were all LOW as predicted.

**P2**: Specialise P1 to `φ = (Polynomial.X ^ (k - 1) : Polynomial ℝ)`. The natDegree side condition `(X^(k-1)).natDegree < n` is discharged by `rw [Polynomial.natDegree_X_pow]; omega` (handling both `n = 0` ex falso from `h1 + hk` and `n ≥ 1` from `k - 1 ≤ n - 1 < n`). The LHS of P1 (the integral) is reduced via:
1. `simp only [Polynomial.eval_pow, Polynomial.eval_X]` to convert `(X^(k-1)).eval x → x^(k-1)`.
2. `rw [integral_pow]` (Mathlib's `theorem integral_pow : ∫ x in a..b, x^n = (b^(n+1) - a^(n+1))/(n+1)`, *not* in the `intervalIntegral` namespace — see Dead end §1).
3. `rw [Nat.sub_add_cancel h1]` to convert `(k - 1) + 1 → k` in the exponent (works at the ℕ level).
4. `rw [hcast]` to convert `↑(k - 1) + 1 → (k : ℝ)` in the denominator — needs a separate `exact_mod_cast (Nat.sub_add_cancel h1)` bridge because the denominator is at the ℝ level, not the ℕ level.
5. `rw [zero_pow (by omega : k ≠ 0), sub_zero]` to collapse the `(c_i^k - 0^k) → c_i^k` term.

After these rewrites `h_exact` is exactly the goal flipped, so `exact h_exact.symm` closes.

**P3.a**: Mirror cycle 309's `gaussLegendre1Stage.SatisfiesB 2` round-trip: `rw [← butcherGaussLegendreRK_one_eq_gaussLegendre1Stage, ← butcherGaussLegendreRK_one_eq]; exact butcherGaussLegendreRK_satisfiesC 1`.

**P3.b**: Trivial: `exact butcherGaussLegendreRK_satisfiesC 2`.

## Result
**SUCCESS**. All four deliverables (P1, P2, P3.a, P3.b) land axiom-clean. Sorry count remains 0. `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.

Axiom profile of new theorems (via `lean_verify`):
- `butcherShiftedLegendre_collocation_exact_lt_n`: `[propext, sorryAx, Classical.choice, Quot.sound]`
- `butcherGaussLegendreRK_satisfiesC`: `[propext, sorryAx, Classical.choice, Quot.sound]`

`sorryAx` leaks from the cycle 301 upstream `_rootsInIoo_card_ge` (pre-existing, propagates through every §342 theorem consuming `_zeros`; cleanup is a separate audit cycle per cycle 309 §G). No regression — same profile as cycles 304/305/306/307/308/309 headline theorems.

Regression check: cycle 309 `butcherGaussLegendreRK_satisfiesB` and cycle 308 `butcherGaussLegendreRK_one_eq` re-verified, identical axiom profiles.

## Faithfulness check
**P1 `butcherShiftedLegendre_collocation_exact_lt_n`** (helper, no Butcher entity — instrumental for `cor:342D` C(n) prong):
- Statement: `∫ x in 0..cᵢ, φ(x) dx = ∑ⱼ Aᵢⱼ · φ(cⱼ)` where `Aᵢⱼ` is the cycle 308 collocation matrix entry and `cᵢ, cⱼ` are the shifted Legendre zeros.
- Textbook citation: Butcher §342 p. 240 (342l)-equivalent, the collocation defining identity. The textbook uses this identity implicitly in the `B(2s)+E(s,s)⇒D(s)` chain.
- Lean statement captures: **same content** as the textbook collocation identity, restricted to polynomial `φ` of degree `< n`. The polynomial-only restriction is necessary (Lagrange interpolation exactness) and is the standard textbook framing.

**P2 `butcherGaussLegendreRK_satisfiesC`** (instrumental, no direct Butcher entity — corresponds to the §342 `C(n)` clause of `cor:342D`):
- Entity ID `cor:342D` textbook statement (from `extraction/formalization_data/entities/cor_342D.json`):
  > A Runge–Kutta method has order 2s if and only if its coefficients are chosen as follows:
  > (i) Choose c₁, c₂, …, cₛ as the zeros of P_s*.
  > (ii) Choose b₁, b₂, …, bₛ to satisfy the B(s) condition.
  > (iii) Choose aᵢⱼ, i, j = 1, 2, …, s, to satisfy the C(s) condition.
- Lean statement captures: **the (iii) clause** specialised to the canonical Gauss–Legendre tableau. The §321 `SatisfiesC` predicate (`∀ i, ∀ k ∈ [1,ξ], ∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k / k`) is the textbook `C(s)` definition verbatim (Butcher §321 equation (321b)). The full `cor:342D` statement (the iff with order 2s) is *not yet* shipped — it requires D(n) and the §314A elementary-weight argument; only the C(n) infrastructure piece is in this cycle.
- Hypothesis strength: **strengthening over the strategy's prediction**. The strategy §A.3 noted "C(n) version may NOT need `0 < n`" since `Fin 0` is empty; this turned out to be correct — the proof goes through uniformly via `omega` on the natDegree side condition. P2 has signature `(n : ℕ) : SatisfiesC n`, no `0 < n`.

**P3.a, P3.b**: Both are `example`s (no public name), exercising P2 at concrete `n` values. No new mathematical content, just non-vacuity witnesses.

**Definition smuggling check**: P2's statement quantifies over `∀ i, ∀ k` and asserts the textbook `C(s)` equation. The proof routes through P1 (a genuine integral exactness theorem) + `integral_pow` (a genuine integral evaluation). No tautology, no identity proof, no smuggling. The `show` step at the start unfolds the `RKTableau` field projections; cycle 309's `B(2n)` proof uses the same pattern.

## Dead ends
1. **`intervalIntegral.integral_pow` does not exist** — the lemma `theorem integral_pow : ∫ x in a..b, x^n = (b^(n+1) - a^(n+1))/(n+1)` in `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:172` is **outside** the `namespace intervalIntegral` block (which ends at line 108). The strategy's §C.3 risk-register hedge — "verify the exact lemma name" — was warranted: I initially used `intervalIntegral.integral_pow` and got `Unknown constant`. The correct unqualified name is `integral_pow` (the file's `open intervalIntegral` at line 110 brings it into scope without a namespace prefix). Resolved in 30 seconds via `grep ^theorem integral_pow`.

2. **Denominator cast: `↑(k - 1) + 1` vs `↑k`** — after `rw [integral_pow]`, the denominator is `((k - 1 : ℕ) : ℝ) + (1 : ℝ)`, *not* `((k - 1 + 1 : ℕ) : ℝ)`. The `+ 1` is at the ℝ level (because the entire expression must type-check as ℝ for the division), so `Nat.sub_add_cancel h1 : k - 1 + 1 = k` (a ℕ-level rewrite) does *not* fire on the denominator. The strategy's R5 risk-register entry called this out as MEDIUM. Resolution: an explicit `have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by have h2 := Nat.sub_add_cancel h1; exact_mod_cast h2`, then `rw [hcast] at h_exact`.

3. **The exponent in the numerator (`c_i^((k-1)+1)`) IS at the ℕ level** because `^ : ℝ → ℕ → ℝ`, so `Nat.sub_add_cancel h1` fires there directly without a cast bridge. This is why only the denominator needed special handling — the asymmetry between exponent and divisor.

## Discovery
1. **Cast bridge pattern for `integral_pow`-style identities**: whenever a Mathlib integral evaluation introduces an ℕ-level expression as both an exponent and a divisor (where the divisor must be cast to ℝ), the divisor cast does NOT get rewritten by ℕ-level `Nat.sub_add_cancel` or similar. Always pre-derive a `((... : ℕ) : ℝ) + 1 = (... : ℝ)` lemma via `exact_mod_cast` and rewrite the denominator explicitly. This pattern will recur in any future closed-form integral evaluation (`integral_exp`, `integral_cos`, etc.) where the exponent/index appears in both numerator (as ℕ) and denominator (as ℝ-cast).

2. **`integral_pow` is unnamespaced** (outside `namespace intervalIntegral`), despite living in `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean` which contains a long `intervalIntegral` namespace block. Mathlib's convention here is: the namespace ends after the `intervalIntegral`-specific *machinery* (translation, scaling), and the *evaluations* of specific functions (powers, exp, log, trig) live at top level. The opener `open intervalIntegral` at line 110 ensures users still get name-resolution without a namespace prefix.

3. **`SatisfiesC` is stronger than `SatisfiesB` in one specific sense**: `SatisfiesC 0` is `∀ i : Fin s, ...` which is vacuous when `s = 0` regardless of `n`-quantifier emptiness. `SatisfiesB 0` is `∀ k, 1 ≤ k → k ≤ 0 → ...` which is vacuous because the `k`-range is empty. So the `0 < n` hypothesis required for cycle 309's `SatisfiesB (2*n)` (needed to make `1 ≤ k ≤ 2n` non-empty) is *not* required for cycle 310's `SatisfiesC n` (the `Fin n` quantifier is empty at `n = 0`). This is a genuine strengthening, predicted by strategy §R7 and confirmed in practice.

## Suggested next approach
**Cycle 311 target: `D(n)` half** — the third prong of `cor:342D`. Per the textbook proof (Butcher p. 240): "if (i) and (ii) are satisfied, then B(2s) holds and this in turn implies E(s, s). This fact, together with B(2s), implies D(s)." So the cycle 311 deliverable is:

```lean
theorem butcherGaussLegendreRK_satisfiesD (n : ℕ) (hn : 0 < n) :
    (butcherGaussLegendreRK n).SatisfiesD n
```

The proof recipe is the standard Hairer–Wanner I.7.5 / Butcher §342 algebraic argument: `D(n)` follows from `B(2n)` (cycle 309) + `C(n)` (cycle 310) by a closed-form manipulation. No new integration infrastructure is needed — it's a *pure algebraic* lift from two existing predicates to a third. Risk profile: LOW–MEDIUM, depending on whether the lift requires the §314A elementary-weight argument inline or can be done purely from B + C identities.

After D(n) ships (cycle 311), the `cor:342D` end-to-end statement (the iff with order 2s) requires the §314A elementary-weight bridge, which is a separate multi-cycle effort. The C(n) infrastructure (cycle 310's P1 + P2) is reusable in §358 (positive-weight characterisation) and §359 (collocation-method order theorems).

**Alternative cycle 311 target if D(n) is too algebra-heavy**: pivot to `thm:342C` (the equivalence theorem `cor:342D` cites — "Theorem 342C relates to order 2s"). Reading `extraction/formalization_data/entities/thm_342C.json` first is mandatory before deciding.

**Do NOT attempt `cor:342D` as a single cycle**: it needs D(n) + the §314A elementary-weight argument + the order-2s ↔ trees-up-to-order-2s equivalence (Butcher §312/§314). Estimated 3–4 cycles of infrastructure before the final iff can ship.

**Cleanup opportunity for a separate cycle**: the cycle 301 upstream `sorryAx` leak (`_rootsInIoo_card_ge`) — per cycle 309 §G, an audit cycle isolating the sorry and either closing it or filing a precise blocker would unblock axiom-clean rebases for every §342 downstream theorem.
