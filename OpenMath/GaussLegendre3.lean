import OpenMath.Collocation
import OpenMath.StiffEquations

/-!
# Gauss–Legendre 3-Stage Method (Section 2.2–2.3)

The **Gauss–Legendre 3-stage (GL3)** method is the 3-stage implicit Runge–Kutta method
based on Gauss–Legendre quadrature nodes. It achieves order 2s = 6, the maximum possible
for any s-stage RK method.

## Butcher Tableau

The nodes are the three Gauss–Legendre quadrature points on [0,1]:
  c₁ = 1/2 − √15/10,  c₂ = 1/2,  c₃ = 1/2 + √15/10

```
  c₁  | 5/36          2/9 − √15/15     5/36 − √15/30
  c₂  | 5/36 + √15/24  2/9             5/36 − √15/24
  c₃  | 5/36 + √15/30  2/9 + √15/15   5/36
  ----|--------------------------------------------
      | 5/18           4/9              5/18
```

## Key Properties

- **Order ≥ 4** (proven): via B(4) ∧ C(3) simplifying assumptions
- **A-stable**: stability function is the (3,3)-diagonal Padé approximant to eᶻ
- **NOT L-stable**: R(z) → −1 as z → −∞
- **Algebraically stable**: Gauss methods are always algebraically stable

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Sections 2.2–2.3 and Chapter 4; Hairer–Nørsett–Wanner, Chapter IV.
-/

open Finset Real Filter

/-! ## √15 helper -/

private theorem sqrt15_sq : Real.sqrt 15 ^ 2 = 15 :=
  Real.sq_sqrt (by norm_num : (15 : ℝ) ≥ 0)

private theorem sqrt15_pos : (0 : ℝ) < Real.sqrt 15 :=
  Real.sqrt_pos_of_pos (by norm_num)

/-! ## Butcher Tableau -/

/-- **Gauss–Legendre 3-stage (GL3)** RK method.
  Reference: Iserles, Section 2.2; Hairer–Nørsett–Wanner, Table 5.1. -/
noncomputable def rkGaussLegendre3 : ButcherTableau 3 where
  A := ![![5/36,                    2/9 - Real.sqrt 15 / 15,   5/36 - Real.sqrt 15 / 30],
         ![5/36 + Real.sqrt 15 / 24, 2/9,                      5/36 - Real.sqrt 15 / 24],
         ![5/36 + Real.sqrt 15 / 30, 2/9 + Real.sqrt 15 / 15,  5/36]]
  b := ![5/18, 4/9, 5/18]
  c := ![1/2 - Real.sqrt 15 / 10, 1/2, 1/2 + Real.sqrt 15 / 10]

/-! ## Basic Properties -/

theorem rkGaussLegendre3_consistent : rkGaussLegendre3.IsConsistent where
  weights_sum := by simp [rkGaussLegendre3, Fin.sum_univ_three]; ring
  row_sum := by
    intro i; fin_cases i <;> simp [rkGaussLegendre3, Fin.sum_univ_three] <;> ring

theorem rkGaussLegendre3_nonNegWeights : rkGaussLegendre3.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkGaussLegendre3] <;> norm_num

theorem rkGaussLegendre3_not_explicit : ¬rkGaussLegendre3.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkGaussLegendre3] at this

/-! ## Simplifying Assumptions -/

theorem rkGaussLegendre3_B4 : rkGaussLegendre3.SatisfiesB 4 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkGaussLegendre3, Fin.sum_univ_three] <;> nlinarith [sqrt15_sq]

theorem rkGaussLegendre3_C3 : rkGaussLegendre3.SatisfiesC 3 := by
  intro k hk1 hk2 i
  interval_cases k <;> fin_cases i <;>
    simp [rkGaussLegendre3, Fin.sum_univ_three] <;> nlinarith [sqrt15_sq]

theorem rkGaussLegendre3_order4 : rkGaussLegendre3.HasOrderGe4 :=
  ButcherTableau.HasOrderGe4_of_B4_C3 _ rkGaussLegendre3_B4 rkGaussLegendre3_C3

theorem rkGaussLegendre3_D1 : rkGaussLegendre3.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; fin_cases j <;>
    simp [rkGaussLegendre3, Fin.sum_univ_three] <;> nlinarith [sqrt15_sq]

/-! ## Stability Function

The GL3 stability function is the (3,3)-diagonal Padé approximant to eᶻ:
  R(z) = P(z)/Q(z) where (scaled by 120):
  P(z) = 120 + 60z + 12z² + z³
  Q(z) = 120 − 60z + 12z² − z³

We use the scaled (integer coefficient) form to avoid complex division issues
in the normSq proofs. -/

/-- Scaled numerator: P(z) = 120 + 60z + 12z² + z³ = 120 · N(z). -/
noncomputable def gl3P (z : ℂ) : ℂ := 120 + 60 * z + 12 * z ^ 2 + z ^ 3

/-- Scaled denominator: Q(z) = 120 − 60z + 12z² − z³ = 120 · D(z). -/
noncomputable def gl3Q (z : ℂ) : ℂ := 120 - 60 * z + 12 * z ^ 2 - z ^ 3

/-- GL3 stability function: R(z) = P(z)/Q(z). -/
noncomputable def gl3StabilityFn (z : ℂ) : ℂ := gl3P z / gl3Q z

/-- Q(z) = P(−z): the hallmark of diagonal Padé approximants. -/
theorem gl3Q_eq_P_neg (z : ℂ) : gl3Q z = gl3P (-z) := by
  simp [gl3P, gl3Q]; ring

/-- P(z) − Q(z) = 120z + 2z³ = 2z(60 + z²). -/
theorem gl3_P_sub_Q (z : ℂ) : gl3P z - gl3Q z = 2 * z * (60 + z ^ 2) := by
  simp [gl3P, gl3Q]; ring

/-- |P(z)|² ≤ |Q(z)|² for Re(z) ≤ 0.
  The difference factors as: |Q|² − |P|² = −48x(600 + 70x² + 30y² + (x²+y²)²). -/
theorem gl3_normSq_Q_ge_P (z : ℂ) (hz : z.re ≤ 0) :
    Complex.normSq (gl3P z) ≤ Complex.normSq (gl3Q z) := by
  suffices h : 0 ≤ Complex.normSq (gl3Q z) - Complex.normSq (gl3P z) by linarith
  set x := z.re
  set y := z.im
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  rw [hz_eq]; simp only [gl3P, gl3Q]
  have hfact : Complex.normSq (120 - 60 * (⟨x, y⟩ : ℂ) + 12 * (⟨x, y⟩ : ℂ) ^ 2 -
      (⟨x, y⟩ : ℂ) ^ 3) -
    Complex.normSq (120 + 60 * (⟨x, y⟩ : ℂ) + 12 * (⟨x, y⟩ : ℂ) ^ 2 +
      (⟨x, y⟩ : ℂ) ^ 3) =
    -48 * x * (600 + 70 * x ^ 2 + 30 * y ^ 2 + (x ^ 2 + y ^ 2) ^ 2) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im,
      Complex.sub_im, Complex.mul_re, Complex.mul_im,
      pow_succ, pow_zero, one_mul,
      show (120 : ℂ).re = (120 : ℝ) from by norm_num,
      show (120 : ℂ).im = (0 : ℝ) from by norm_num,
      show (60 : ℂ).re = (60 : ℝ) from by norm_num,
      show (60 : ℂ).im = (0 : ℝ) from by norm_num,
      show (12 : ℂ).re = (12 : ℝ) from by norm_num,
      show (12 : ℂ).im = (0 : ℝ) from by norm_num]
    ring
  rw [hfact]
  have h600 : (0 : ℝ) < 600 + 70 * x ^ 2 + 30 * y ^ 2 + (x ^ 2 + y ^ 2) ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  nlinarith

/-- Q(z) ≠ 0 for Re(z) ≤ 0. -/
theorem gl3_Q_ne_zero (z : ℂ) (hz : z.re ≤ 0) : gl3Q z ≠ 0 := by
  intro heq
  have h0 : Complex.normSq (gl3Q z) = 0 := by rw [heq]; simp
  have h1 : Complex.normSq (gl3P z) ≤ 0 := by linarith [gl3_normSq_Q_ge_P z hz]
  have hP0 : gl3P z = 0 := Complex.normSq_eq_zero.mp (le_antisymm h1 (Complex.normSq_nonneg _))
  -- P = Q = 0 implies P - Q = 0, i.e., 2z(60 + z²) = 0
  have h_diff : 2 * z * (60 + z ^ 2) = 0 := by
    have h := gl3_P_sub_Q z
    rw [hP0, heq, show (0 : ℂ) - 0 = 0 from by ring] at h
    exact h.symm
  -- Factor: z = 0 or 60 + z² = 0
  rcases mul_eq_zero.mp h_diff with h2z | hz60
  · rcases mul_eq_zero.mp h2z with h2 | hz0
    · norm_num at h2
    · rw [hz0] at hP0; simp [gl3P] at hP0
  · -- 60 + z² = 0 gives z² = -60, z³ = -60z
    have hzsq : z ^ 2 = -60 := by linear_combination hz60
    have hzcub : z ^ 3 = -60 * z := by linear_combination z * hz60
    -- P(z) = 120 + 60z + 12(-60) + (-60z) = 120 + 60z - 720 - 60z = -600
    have : gl3P z = -600 := by unfold gl3P; rw [hzsq, hzcub]; ring
    rw [this] at hP0; norm_num at hP0

/-- **A-stability of GL3**: |R(z)| ≤ 1 for Re(z) ≤ 0. -/
theorem gl3_aStable (z : ℂ) (hz : z.re ≤ 0) : ‖gl3StabilityFn z‖ ≤ 1 := by
  have hQ := gl3_Q_ne_zero z hz
  have hQ_pos : (0 : ℝ) < ‖gl3Q z‖ := norm_pos_iff.mpr hQ
  unfold gl3StabilityFn
  rw [norm_div, div_le_one hQ_pos]
  have h_sq_le : ‖gl3P z‖ ^ 2 ≤ ‖gl3Q z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    exact gl3_normSq_Q_ge_P z hz
  by_contra hlt; push_neg at hlt
  nlinarith [norm_nonneg (gl3P z), norm_nonneg (gl3Q z),
             mul_pos (by linarith : (0 : ℝ) < ‖gl3P z‖ - ‖gl3Q z‖)
                     (by linarith [norm_nonneg (gl3P z)] :
                       (0 : ℝ) < ‖gl3P z‖ + ‖gl3Q z‖)]

/-! ## NOT L-stable -/

/-- Helper: for real x ≤ -120, |R(x)| ≥ 1/2 because 2|P(x)| ≥ Q(x). -/
private theorem gl3_norm_ge_half (x : ℝ) (hx : x ≤ -120) :
    1/2 ≤ ‖gl3StabilityFn (↑x)‖ := by
  set P : ℝ := 120 + 60 * x + 12 * x ^ 2 + x ^ 3 with hP_def
  set Q : ℝ := 120 - 60 * x + 12 * x ^ 2 - x ^ 3 with hQ_def
  have hPeq : gl3P (↑x) = (P : ℂ) := by
    simp only [gl3P, hP_def]; push_cast; ring
  have hQeq : gl3Q (↑x) = (Q : ℂ) := by
    simp only [gl3Q, hQ_def]; push_cast; ring
  have hQ_pos : (0 : ℝ) < Q := by rw [hQ_def]; nlinarith [sq_nonneg x]
  have hP_neg : P < 0 := by rw [hP_def]; nlinarith [sq_nonneg x]
  -- Q + 2P = 360 + 60x + 36x² + x³ = x²(x+36) + 60(x+6) ≤ 0 for x ≤ -120
  have h2P_ge_Q : Q ≤ -2 * P := by
    rw [hP_def, hQ_def]
    nlinarith [sq_nonneg x,
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (show x + 36 ≤ 0 from by linarith)]
  -- ‖R(x)‖ = |P|/Q = (-P)/Q ≥ 1/2
  simp only [gl3StabilityFn, hPeq, hQeq, Complex.norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ_pos, abs_of_neg hP_neg]
  rw [le_div_iff₀ hQ_pos]
  linarith

/-- GL3 is NOT L-stable: |R(x)| → −1 as x ��� −∞, not 0. -/
theorem gl3_not_stiffDecay :
    ¬Tendsto (fun x : ℝ => gl3StabilityFn (↑x)) atBot (nhds 0) := by
  intro h
  have h_small : ∀ᶠ (x : ℝ) in atBot, ‖gl3StabilityFn ↑x‖ < 1/2 :=
    (NormedAddCommGroup.tendsto_nhds_zero.mp h) (1/2) (by norm_num)
  have h_big : ∀ᶠ (x : ℝ) in atBot, 1/2 ≤ ‖gl3StabilityFn ↑x‖ :=
    Filter.eventually_atBot.mpr ⟨-120, fun x hx => gl3_norm_ge_half x hx⟩
  obtain ⟨x, hx_small, hx_big⟩ := (h_small.and h_big).exists
  linarith

/-! ## Algebraic Stability -/

/-- **GL3 is algebraically stable**: M is positive semidefinite. -/
theorem rkGaussLegendre3_algStable : rkGaussLegendre3.IsAlgStable where
  nonneg_weights := rkGaussLegendre3_nonNegWeights
  posdef_M := by
    intro v; simp [ButcherTableau.algStabMatrix, rkGaussLegendre3, Fin.sum_univ_three]
    nlinarith [sq_nonneg (v 0 - v 2),
               sq_nonneg (v 0 - v 1),
               sq_nonneg (v 1 - v 2),
               sq_nonneg (v 0 + v 2 - 2 * v 1),
               sq_nonneg (Real.sqrt 15 * (v 0 - v 2)),
               sqrt15_sq, sqrt15_pos]
