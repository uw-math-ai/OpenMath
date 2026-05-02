import Mathlib

/-! # Cycle 076 Aristotle batch — §410C helpers

Self-contained submission for the §410C `(ρ, σ)`-form
order-condition cluster.

We submit five sub-lemmas (mirror of cycle 073's `expNegPS`
helpers, with `(-1)` replaced by general `k`):

1. `expPS_coeff` — `coeff n expPS = 1 / n!`.
2. `expKzPS_coeff` — `coeff n (expKzPS k) = k^n / n!`.
3. `expPS_pow` — closed form `expPS^m = mk fun n => m^n / n!`.
4. `coeff_aeval_C_X_pow_expPS` — `coeff j (aeval expPS (C c · X^m))
   = c · m^j / j!`.
5. `coeff_expKzPS_mul_eq_zero_iff` — multiplication by the unit
   `expKzPS k` (constant term 1) preserves vanishing of low
   coefficients.
-/

namespace AristotleCycle076

noncomputable def expPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => 1 / (Nat.factorial n : ℝ)

noncomputable def expKzPS (k : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => (k : ℝ) ^ n / (Nat.factorial n : ℝ)

theorem expPS_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℝ) n) expPS
      = 1 / (Nat.factorial n : ℝ) := by
  sorry

theorem expKzPS_coeff (k n : ℕ) :
    (PowerSeries.coeff (R := ℝ) n) (expKzPS k)
      = (k : ℝ) ^ n / (Nat.factorial n : ℝ) := by
  sorry

/-- `expPS^m = mk fun n => m^n / n!`. Mirror of cycle 073's
`expNegPS^m` proof; induction on `m` using `add_pow`,
`Nat.cast_choose`, and Cauchy product identification. -/
theorem expPS_pow (m : ℕ) :
    (expPS ^ m) =
      PowerSeries.mk (fun n => (m : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
  sorry

/-- The j-th formal power-series coefficient of
`(Polynomial.C c * X^m)` substituted at `expPS` is `c · m^j / j!`. -/
theorem coeff_aeval_C_X_pow_expPS (c : ℝ) (m j : ℕ) :
    (PowerSeries.coeff (R := ℝ) j)
        ((Polynomial.aeval expPS) (Polynomial.C c * Polynomial.X ^ m))
      = c * (m : ℝ) ^ j / (Nat.factorial j : ℝ) := by
  sorry

/-- **The §410C bridge lemma.** Multiplication by the unit
`expKzPS k` (constant term 1) preserves vanishing of the first
p+1 coefficients.

Forward direction: strong induction on `j ≤ p`. For `j = 0`,
`coeff 0 (expKzPS k * g) = (constantCoeff (expKzPS k)) * coeff 0 g
= 1 · coeff 0 g`. For `j+1`, `coeff (j+1) (expKzPS k * g)` is a
sum involving `coeff i g` for `i ≤ j+1`; the IH eliminates all
the `i < j+1` terms, leaving `coeff (j+1) g`.

Reverse direction: if all coefficients of `g` up to `p` vanish,
then in the Cauchy product `coeff j (expKzPS k * g) = Σ_{i+l=j}
coeff i (expKzPS k) · coeff l g`, every term has `l ≤ j ≤ p`,
hence `coeff l g = 0`. -/
theorem coeff_expKzPS_mul_eq_zero_iff {k : ℕ} (g : PowerSeries ℝ)
    (p : ℕ) :
    (∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (expKzPS k * g) = 0)
      ↔ (∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) g = 0) := by
  sorry

end AristotleCycle076
