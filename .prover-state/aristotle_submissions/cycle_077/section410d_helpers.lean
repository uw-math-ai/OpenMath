import Mathlib

/-! # Cycle 077 Aristotle batch — §410D log-form helpers

Self-contained submission for the §410D log-form
order-condition cluster.

We submit five sub-lemmas:

1. `onePlusX_mul_oneOverOnePlusPS_eq_one` — `(1+X) · (1+X)⁻¹ = 1`
   for the geometric series, via Cauchy product.
2. `coeff_subst_eq_zero_of_coeff_eq_zero` — substitution by
   `g` with `constantCoeff g = 0` preserves vanishing of low
   coefficients (forward direction).
3. `coeff_eq_zero_of_coeff_subst_eq_zero` — substitution by
   `g` with `constantCoeff g = 0` and `coeff 1 g = 1` reflects
   vanishing of low coefficients (reverse direction).
4. `subst_logOnePlusPS_expNegPS` — `subst logOnePlusPS expNegPS
   = oneOverOnePlusPS`. Says `exp(-log(1+w)) = (1+w)^{-1}`.
5. `subst_logOnePlusPS_expPS_eq_one_add_X` — `subst logOnePlusPS expPS
   = 1 + X`. Says `exp(log(1+w)) = 1+w`. Helper for #4.
-/

namespace AristotleCycle077

noncomputable def oneOverOnePlusPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => (-1 : ℝ) ^ n

noncomputable def logOnePlusPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1 : ℝ) ^ (n - 1) / (n : ℝ)

noncomputable def expPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => 1 / (Nat.factorial n : ℝ)

noncomputable def expNegPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => (-1 : ℝ) ^ n / (Nat.factorial n : ℝ)

@[simp] theorem oneOverOnePlusPS_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℝ) n) oneOverOnePlusPS = (-1 : ℝ) ^ n := by
  simp [oneOverOnePlusPS]

@[simp] theorem logOnePlusPS_constantCoeff :
    (PowerSeries.constantCoeff (R := ℝ)) logOnePlusPS = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logOnePlusPS]

@[simp] theorem logOnePlusPS_coeff_one :
    (PowerSeries.coeff (R := ℝ) 1) logOnePlusPS = 1 := by
  simp [logOnePlusPS]

theorem onePlusX_mul_oneOverOnePlusPS_eq_one :
    ((1 : PowerSeries ℝ) + PowerSeries.X) * oneOverOnePlusPS = 1 := by
  sorry

/-- Forward direction: substitution by `g` with constant term 0
preserves "first p+1 coefficients vanish". -/
theorem coeff_subst_eq_zero_of_coeff_eq_zero
    {g : PowerSeries ℝ} (hg : (PowerSeries.constantCoeff ℝ) g = 0)
    {f : PowerSeries ℝ} {p : ℕ}
    (h : ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) f = 0) :
    ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (PowerSeries.subst g f) = 0 := by
  sorry

/-- Reverse direction: substitution by unit-leading `g`
(constant term 0, linear coefficient 1) reflects "first p+1
coefficients vanish". -/
theorem coeff_eq_zero_of_coeff_subst_eq_zero
    {g : PowerSeries ℝ} (hg0 : (PowerSeries.constantCoeff ℝ) g = 0)
    (hg1 : (PowerSeries.coeff (R := ℝ) 1) g = 1)
    {f : PowerSeries ℝ} {p : ℕ}
    (h : ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (PowerSeries.subst g f) = 0) :
    ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) f = 0 := by
  sorry

/-- `subst logOnePlusPS expPS = 1 + X`. Says `exp(log(1+w)) = 1+w`. -/
theorem subst_logOnePlusPS_expPS_eq_one_add_X :
    PowerSeries.subst logOnePlusPS expPS
      = (1 : PowerSeries ℝ) + PowerSeries.X := by
  sorry

/-- `subst logOnePlusPS expNegPS = oneOverOnePlusPS`. Says
`exp(-log(1+w)) = (1+w)^{-1}`. -/
theorem subst_logOnePlusPS_expNegPS :
    PowerSeries.subst logOnePlusPS expNegPS = oneOverOnePlusPS := by
  sorry

end AristotleCycle077
