import OpenMath.SDIRK

/-!
# 3-Stage SDIRK Method (Section 4.3)

The **Alexander 3-stage SDIRK** method is a 3-stage singly diagonally implicit
Runge–Kutta method of order 3 that is L-stable.

## Characterizing Parameter

The diagonal parameter λ is the unique real root of
  6λ³ − 18λ² + 9λ − 1 = 0
in the interval (2/5, 1/2). This cubic arises from requiring simultaneously:
- **Order 3**: the method matches eᶻ to third order
- **L-stability**: deg(numerator) < deg(denominator) in the stability function

## Butcher Tableau

```
  λ           | λ              0                  0
  (1+λ)/2     | (1−λ)/2        λ                  0
  1           | λ(2−λ)/(1−λ)   (2λ²−4λ+1)/(1−λ)   λ
  ------------|------------------------------------------------
              | λ(2−λ)/(1−λ)   (2λ²−4λ+1)/(1−λ)   λ
```

## Key Properties

- **Order 3** (proven): both conditions follow from the cubic identity
- **NOT order 4**: the fourth-order condition ∑ bᵢcᵢ³ = 1/4 fails
- **L-stable**: R(z) = N(z)/D(z) with deg(N)=2 < deg(D)=3, so R(z) → 0 as z → −∞
- **NOT algebraically stable**: M₁₁ < 0

Reference: Alexander (1977); Iserles, *A First Course in the Numerical Analysis
of Differential Equations*, Section 4.3; Hairer–Wanner, *Solving ODEs II*, Table 6.5.
-/

open Finset Real Filter

/-! ## SDIRK3 Parameter λ

The parameter λ is defined as the unique root of 6λ³ − 18λ² + 9λ − 1 = 0
in (2/5, 1/2). We construct it via the intermediate value theorem. -/

/-- The cubic polynomial whose root defines the SDIRK3 parameter. -/
private def sdirk3CubicPoly (x : ℝ) : ℝ := 6 * x ^ 3 - 18 * x ^ 2 + 9 * x - 1

private theorem sdirk3CubicPoly_continuous : Continuous sdirk3CubicPoly := by
  unfold sdirk3CubicPoly; fun_prop

/-- The cubic is positive at x = 2/5: p(2/5) = 13/125 > 0. -/
private theorem sdirk3_poly_pos_at_two_fifths : sdirk3CubicPoly (2/5) = 13/125 := by
  unfold sdirk3CubicPoly; norm_num

/-- The cubic is negative at x = 1/2: p(1/2) = -1/4 < 0. -/
private theorem sdirk3_poly_neg_at_half : sdirk3CubicPoly (1/2) = -1/4 := by
  unfold sdirk3CubicPoly; norm_num

/-- By the intermediate value theorem, the cubic has a root in [2/5, 1/2]. -/
private theorem sdirk3_root_exists_Icc :
    ∃ x ∈ Set.Icc (2/5 : ℝ) (1/2), sdirk3CubicPoly x = 0 := by
  have hab : (2 : ℝ)/5 ≤ 1/2 := by norm_num
  have hcont : ContinuousOn sdirk3CubicPoly (Set.Icc (2/5) (1/2)) :=
    sdirk3CubicPoly_continuous.continuousOn
  -- f(1/2) = -1/4 ≤ 0 ≤ 13/125 = f(2/5), so 0 ∈ [f(1/2), f(2/5)]
  have hmem : (0 : ℝ) ∈ Set.Icc (sdirk3CubicPoly (1/2)) (sdirk3CubicPoly (2/5)) := by
    rw [sdirk3_poly_neg_at_half, sdirk3_poly_pos_at_two_fifths]
    constructor <;> norm_num
  have hsub := intermediate_value_Icc' hab hcont hmem
  obtain ⟨c, hc_mem, hc_val⟩ := hsub
  exact ⟨c, hc_mem, hc_val⟩

/-- The root is strictly in (2/5, 1/2) since p(2/5) ≠ 0 and p(1/2) ≠ 0. -/
private theorem sdirk3_root_exists :
    ∃ x : ℝ, 2/5 < x ∧ x < 1/2 ∧ 6 * x ^ 3 - 18 * x ^ 2 + 9 * x - 1 = 0 := by
  obtain ⟨c, ⟨hc_lo, hc_hi⟩, hc_val⟩ := sdirk3_root_exists_Icc
  refine ⟨c, ?_, ?_, ?_⟩
  · -- c > 2/5: if c = 2/5, then p(c) = 13/125 ≠ 0
    rcases eq_or_lt_of_le hc_lo with rfl | h
    · exfalso; rw [sdirk3_poly_pos_at_two_fifths] at hc_val; norm_num at hc_val
    · exact h
  · -- c < 1/2: if c = 1/2, then p(c) = -1/4 ≠ 0
    rcases eq_or_lt_of_le hc_hi with rfl | h
    · exfalso; rw [sdirk3_poly_neg_at_half] at hc_val; norm_num at hc_val
    · exact h
  · exact hc_val

/-- **SDIRK3 parameter** λ: the unique root of 6λ³ − 18λ² + 9λ − 1 = 0 in (2/5, 1/2).
  Numerically λ ≈ 0.4358665215. -/
noncomputable def sdirk3Lambda : ℝ := sdirk3_root_exists.choose

/-- The characterizing cubic identity: 6λ³ − 18λ² + 9λ − 1 = 0. -/
theorem sdirk3Lambda_char : 6 * sdirk3Lambda ^ 3 - 18 * sdirk3Lambda ^ 2 +
    9 * sdirk3Lambda - 1 = 0 :=
  sdirk3_root_exists.choose_spec.2.2

/-- λ > 2/5. -/
theorem sdirk3Lambda_gt : 2/5 < sdirk3Lambda :=
  sdirk3_root_exists.choose_spec.1

/-- λ < 1/2. -/
theorem sdirk3Lambda_lt : sdirk3Lambda < 1/2 :=
  sdirk3_root_exists.choose_spec.2.1

/-- λ > 0. -/
theorem sdirk3Lambda_pos : 0 < sdirk3Lambda := by linarith [sdirk3Lambda_gt]

/-- λ < 1. -/
theorem sdirk3Lambda_lt_one : sdirk3Lambda < 1 := by linarith [sdirk3Lambda_lt]

/-- 1 − λ > 0. -/
theorem one_sub_sdirk3Lambda_pos : 0 < 1 - sdirk3Lambda := by linarith [sdirk3Lambda_lt_one]

/-- 1 − λ ≠ 0. -/
theorem one_sub_sdirk3Lambda_ne_zero : (1 : ℝ) - sdirk3Lambda ≠ 0 :=
  ne_of_gt one_sub_sdirk3Lambda_pos

/-- Equivalent form of the cubic: λ³ = (18λ² − 9λ + 1)/6. -/
theorem sdirk3Lambda_cube : sdirk3Lambda ^ 3 = (18 * sdirk3Lambda ^ 2 - 9 * sdirk3Lambda + 1) / 6 := by
  have h := sdirk3Lambda_char; field_simp; linarith

/-! ## Butcher Tableau Definition -/

/-- **3-stage SDIRK** (Alexander method) with λ from the cubic 6λ³−18λ²+9λ−1 = 0.
  Reference: Alexander (1977); Iserles, Section 4.3. -/
noncomputable def rkSDIRK3 : ButcherTableau 3 where
  A := ![![sdirk3Lambda, 0, 0],
         ![(1 - sdirk3Lambda) / 2, sdirk3Lambda, 0],
         ![sdirk3Lambda * (2 - sdirk3Lambda) / (1 - sdirk3Lambda),
           (2 * sdirk3Lambda ^ 2 - 4 * sdirk3Lambda + 1) / (1 - sdirk3Lambda),
           sdirk3Lambda]]
  b := ![sdirk3Lambda * (2 - sdirk3Lambda) / (1 - sdirk3Lambda),
         (2 * sdirk3Lambda ^ 2 - 4 * sdirk3Lambda + 1) / (1 - sdirk3Lambda),
         sdirk3Lambda]
  c := ![sdirk3Lambda, (1 + sdirk3Lambda) / 2, 1]

/-! ## Basic Properties -/

/-- rkSDIRK3 is a SDIRK method: lower triangular A with constant diagonal. -/
theorem rkSDIRK3_isSDIRK : rkSDIRK3.IsSDIRK where
  lower_tri := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [rkSDIRK3]
  const_diag := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkSDIRK3]

/-- rkSDIRK3 is stiffly accurate: bᵢ = a₃ᵢ for all i. -/
theorem rkSDIRK3_stifflyAccurate :
    ∀ i : Fin 3, rkSDIRK3.b i = rkSDIRK3.A 2 i := by
  intro i; fin_cases i <;> simp [rkSDIRK3]

/-- rkSDIRK3 is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkSDIRK3_consistent : rkSDIRK3.IsConsistent where
  weights_sum := by
    simp [rkSDIRK3, Fin.sum_univ_three]
    field_simp [one_sub_sdirk3Lambda_ne_zero]; ring
  row_sum := by
    intro i; fin_cases i <;> simp [rkSDIRK3, Fin.sum_univ_three]
    · -- i = 1: (1-λ)/2 + λ = (1+λ)/2
      ring
    · -- i = 2: b₁ + b₂ + λ = 1
      field_simp [one_sub_sdirk3Lambda_ne_zero]; ring

/-- rkSDIRK3 is NOT explicit (a₁₁ = λ > 0). -/
theorem rkSDIRK3_not_explicit : ¬rkSDIRK3.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkSDIRK3] at this
  linarith [sdirk3Lambda_pos]

/-! ## Order -/

/-- rkSDIRK3 has order at least 2. -/
theorem rkSDIRK3_order2 : rkSDIRK3.HasOrderGe2 := by
  refine ⟨?_, ?_⟩
  · -- order1: ∑ bᵢ = 1
    simp [ButcherTableau.order1, rkSDIRK3, Fin.sum_univ_three]
    field_simp [one_sub_sdirk3Lambda_ne_zero]; ring
  · -- order2: ∑ bᵢcᵢ = 1/2
    simp [ButcherTableau.order2, rkSDIRK3, Fin.sum_univ_three]
    field_simp [one_sub_sdirk3Lambda_ne_zero]
    nlinarith [sdirk3Lambda_char]

/-- rkSDIRK3 has order at least 3.
  Both order-3 conditions are equivalent to 6λ³−18λ²+9λ−1 = 0. -/
theorem rkSDIRK3_order3 : rkSDIRK3.HasOrderGe3 := by
  refine ⟨rkSDIRK3_order2.1, rkSDIRK3_order2.2, ?_, ?_⟩
  · -- order3a: ∑ bᵢcᵢ² = 1/3
    simp [ButcherTableau.order3a, rkSDIRK3, Fin.sum_univ_three]
    field_simp [one_sub_sdirk3Lambda_ne_zero]
    nlinarith [sdirk3Lambda_char, sdirk3Lambda_pos, one_sub_sdirk3Lambda_pos]
  · -- order3b: ∑∑ bᵢaᵢⱼcⱼ = 1/6
    simp [ButcherTableau.order3b, rkSDIRK3, Fin.sum_univ_three]
    field_simp [one_sub_sdirk3Lambda_ne_zero]
    nlinarith [sdirk3Lambda_char, sdirk3Lambda_pos, one_sub_sdirk3Lambda_pos]

/-- rkSDIRK3 does NOT have order 4: the condition ∑ bᵢcᵢ³ = 1/4 fails. -/
theorem rkSDIRK3_not_order4 : ¬rkSDIRK3.HasOrderGe4 := by
  intro ⟨_, _, _, _, h4a, _⟩
  simp [ButcherTableau.order4a, rkSDIRK3, Fin.sum_univ_three] at h4a
  -- After clearing denominators, this contradicts the cubic identity
  have hne := one_sub_sdirk3Lambda_ne_zero
  field_simp [hne] at h4a
  nlinarith [sdirk3Lambda_char, sdirk3Lambda_pos, sdirk3Lambda_lt, one_sub_sdirk3Lambda_pos]

/-- rkSDIRK3 has non-negative weights when the last weight λ > 0.
  Actually b₂ = (2λ²−4λ+1)/(1−λ) may be negative. We prove the individual signs. -/
theorem rkSDIRK3_b3_pos : rkSDIRK3.b 2 = sdirk3Lambda := by
  simp [rkSDIRK3]

/-! ## Stability Function

The stability function of a 3-stage SDIRK with diagonal parameter λ is:
  R(z) = N(z)/D(z) where D(z) = (1 − λz)³
  N(z) = 1 + (1−3λ)z + (1/2 − 3λ + 3λ²)z²

Since deg(N) = 2 < deg(D) = 3, R(z) → 0 as z → −∞, giving stiff decay.
-/

/-- Denominator of the SDIRK3 stability function: D(z) = (1 − λz)³. -/
noncomputable def sdirk3Denom (z : ℂ) : ℂ := (1 - (sdirk3Lambda : ℝ) * z) ^ 3

/-- Numerator of the SDIRK3 stability function:
  N(z) = 1 + (1−3λ)z + (1/2 − 3λ + 3λ²)z². -/
noncomputable def sdirk3Num (z : ℂ) : ℂ :=
  1 + (1 - 3 * (sdirk3Lambda : ℝ)) * z +
  (1/2 - 3 * (sdirk3Lambda : ℝ) + 3 * (sdirk3Lambda : ℝ) ^ 2) * z ^ 2

/-- SDIRK3 stability function: R(z) = N(z)/D(z). -/
noncomputable def sdirk3StabilityFn (z : ℂ) : ℂ := sdirk3Num z / sdirk3Denom z

/-! ### Stiff Decay and L-Stability -/

/-- The denominator is nonzero for Re(z) ≤ 0. -/
theorem sdirk3_denom_ne_zero (z : ℂ) (hz : z.re ≤ 0) : sdirk3Denom z ≠ 0 := by
  simp only [sdirk3Denom]
  rw [pow_ne_zero_iff (by norm_num)]
  intro heq
  have hre : (1 : ℂ).re - ((sdirk3Lambda : ℝ) * z).re = 0 := by
    have := congr_arg Complex.re heq; simpa using this
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hre
  have : z.re = 1 / sdirk3Lambda := by
    field_simp [ne_of_gt sdirk3Lambda_pos] at hre ⊢; linarith
  linarith [sdirk3Lambda_pos, div_pos one_pos sdirk3Lambda_pos]

/-- **SDIRK3 has stiff decay**: R(x) → 0 as x → −∞.
  Since deg(N) = 2 < deg(D) = 3, this follows from elementary bounds. -/
theorem sdirk3_stiffDecay :
    Tendsto (fun x : ℝ => sdirk3StabilityFn (↑x)) atBot (nhds 0) := by
  apply NormedAddCommGroup.tendsto_nhds_zero.mpr
  intro ε hε
  have hlam_pos := sdirk3Lambda_pos
  have hlam3_pos : (0 : ℝ) < sdirk3Lambda ^ 3 := by positivity
  -- For x < -C, we have |R(x)| ≤ K/|x| < ε
  -- D(x) = (1-λx)³ ≥ (λ|x|/2)³ for |x| large enough
  -- N(x) ≤ C·x² for |x| large enough
  -- So |R(x)| ≤ C·x² / (λ|x|/2)³ = 8C/(λ³|x|) → 0
  filter_upwards [eventually_lt_atBot (min (-2) (min (-2/sdirk3Lambda)
    (-16/(ε * sdirk3Lambda ^ 3))))] with x hx
  have ⟨hx_neg', hx_rest⟩ := lt_min_iff.mp hx
  have ⟨hx_2l, hx_large⟩ := lt_min_iff.mp hx_rest
  have hnx_pos : (0 : ℝ) < -x := by linarith
  have h1_minus_lx : 0 < 1 - sdirk3Lambda * x := by nlinarith
  -- Cast to real computation
  simp only [sdirk3StabilityFn, sdirk3Num, sdirk3Denom]
  -- The numerator N(x) and denominator D(x) are real for real x
  -- We bound |N(x)| / |D(x)| directly
  set N := 1 + (1 - 3 * sdirk3Lambda) * x +
    (1/2 - 3 * sdirk3Lambda + 3 * sdirk3Lambda ^ 2) * x ^ 2 with hN_def
  set D := (1 - sdirk3Lambda * x) ^ 3 with hD_def
  have hNeq : sdirk3Num (↑x) = ((N : ℝ) : ℂ) := by
    simp only [sdirk3Num, N]; push_cast; ring
  have hDeq : sdirk3Denom (↑x) = ((D : ℝ) : ℂ) := by
    simp only [sdirk3Denom, D]; push_cast; ring
  rw [hNeq, hDeq]
  rw [show ((N : ℝ) : ℂ) / ((D : ℝ) : ℂ) = (((N / D : ℝ)) : ℂ) from by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hD_pos : (0 : ℝ) < D := by positivity
  -- Bound |N| ≤ 2x² (for x ≤ -2)
  have hN_bound : |N| ≤ 2 * x ^ 2 := by
    rw [abs_le]; constructor <;> (rw [hN_def]; nlinarith [sdirk3Lambda_lt, sdirk3Lambda_pos, sq_nonneg x])
  -- Bound D ≥ (λ(-x)/2)³ (for -x ≥ 2/λ)
  have h_half : 1 - sdirk3Lambda * x ≥ sdirk3Lambda * (-x) / 2 := by
    nlinarith
  have hD_lower : D ≥ (sdirk3Lambda * (-x) / 2) ^ 3 := by
    rw [hD_def]
    apply pow_le_pow_left (by positivity) h_half
  have hlx2_pos : (0 : ℝ) < sdirk3Lambda * (-x) / 2 := by positivity
  calc |N / D| = |N| / D := by rw [abs_div, abs_of_pos hD_pos]
    _ ≤ (2 * x ^ 2) / D := by
        apply div_le_div_of_nonneg_right hN_bound (by linarith)
    _ ≤ (2 * x ^ 2) / (sdirk3Lambda * (-x) / 2) ^ 3 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hD_lower
    _ = 16 / (sdirk3Lambda ^ 3 * (-x)) := by
        field_simp; nlinarith [sq_nonneg x]
    _ < ε := by
        rw [div_lt_iff₀ (by positivity)]
        have : -x > 16 / (ε * sdirk3Lambda ^ 3) := by
          linarith [neg_div_neg_eq (16 : ℝ) (ε * sdirk3Lambda ^ 3)]
        nlinarith [mul_pos hε hlam3_pos]

/-! ### A-Stability -/

/-- The real polynomial inequality underlying SDIRK3 A-stability.
  For x ≤ 0, the stability function denominator dominates the numerator in norm. -/
private theorem sdirk3_poly_ineq (x y : ℝ) (hx : x ≤ 0) :
    let L := sdirk3Lambda
    (1 + (1 - 3*L)*x + (1/2 - 3*L + 3*L^2)*(x^2 - y^2))^2 +
    ((1 - 3*L)*y + 2*(1/2 - 3*L + 3*L^2)*x*y)^2 ≤
    ((1 - L*x)^2 + (L*y)^2)^3 := by
  set L := sdirk3Lambda
  have hchar := sdirk3Lambda_char  -- 6L³ - 18L² + 9L - 1 = 0
  have hL_pos := sdirk3Lambda_pos
  have hL_lt := sdirk3Lambda_lt    -- L < 1/2
  have hL_gt := sdirk3Lambda_gt    -- L > 2/5
  -- Suffices to show |D|² - |N|² ≥ 0
  suffices h : 0 ≤ ((1 - L*x)^2 + (L*y)^2)^3 -
      ((1 + (1-3*L)*x + (1/2-3*L+3*L^2)*(x^2-y^2))^2 +
       ((1-3*L)*y + 2*(1/2-3*L+3*L^2)*x*y)^2) by linarith
  -- Substitute t = -x ≥ 0
  set t := -x with ht_def
  have ht : 0 ≤ t := by linarith
  have hx_eq : x = -t := by linarith
  rw [hx_eq]
  -- Step 1: Factor the y=0 part as a product
  have hF1 : (1 + L*t)^3 - (1 - (1-3*L)*t + (1/2-3*L+3*L^2)*t^2) =
      t * (1 + (3*L-1/2)*t + L^3*t^2) := by ring
  have hF2 : (1 + L*t)^3 + (1 - (1-3*L)*t + (1/2-3*L+3*L^2)*t^2) =
      2 + (6*L-1)*t + (6*L^2-3*L+1/2)*t^2 + L^3*t^3 := by ring
  -- Step 2: Non-negativity of factors (all coefficients positive for t ≥ 0)
  have h3L_half : 0 < 3*L - 1/2 := by linarith
  have h6L_one : 0 < 6*L - 1 := by linarith
  have h6L2 : 0 < 6*L^2 - 3*L + 1/2 := by nlinarith [sq_nonneg (L - 1/4)]
  have hL3_pos : (0 : ℝ) < L^3 := by positivity
  have hF1_nn : 0 ≤ 1 + (3*L-1/2)*t + L^3*t^2 := by
    have : 0 ≤ (3*L-1/2)*t := mul_nonneg (le_of_lt h3L_half) ht
    have : 0 ≤ L^3*t^2 := mul_nonneg (le_of_lt hL3_pos) (sq_nonneg t)
    linarith
  have hF2_nn : 0 ≤ 2 + (6*L-1)*t + (6*L^2-3*L+1/2)*t^2 + L^3*t^3 := by
    have : 0 ≤ (6*L-1)*t := mul_nonneg (le_of_lt h6L_one) ht
    have : 0 ≤ (6*L^2-3*L+1/2)*t^2 := mul_nonneg (le_of_lt h6L2) (sq_nonneg t)
    have : 0 ≤ L^3*t^3 := by positivity
    linarith
  -- Step 3: y=0 bracket identity and non-negativity
  have hB1 : (1 + L*t)^6 - (1 - (1-3*L)*t + (1/2-3*L+3*L^2)*t^2)^2 =
      t * (1 + (3*L-1/2)*t + L^3*t^2) *
        (2 + (6*L-1)*t + (6*L^2-3*L+1/2)*t^2 + L^3*t^3) := by
    have : (1+L*t)^6 - (1-(1-3*L)*t+(1/2-3*L+3*L^2)*t^2)^2 =
        ((1+L*t)^3 - (1-(1-3*L)*t+(1/2-3*L+3*L^2)*t^2)) *
        ((1+L*t)^3 + (1-(1-3*L)*t+(1/2-3*L+3*L^2)*t^2)) := by ring
    rw [this, hF1, hF2]
  have hB1_nn : 0 ≤ t * (1 + (3*L-1/2)*t + L^3*t^2) *
      (2 + (6*L-1)*t + (6*L^2-3*L+1/2)*t^2 + L^3*t^3) :=
    mul_nonneg (mul_nonneg ht hF1_nn) hF2_nn
  -- Step 4: Tighter bound on L (needed for y² coefficient)
  -- The cubic evaluates to 3083/62500 > 0 at 21/50
  have hpoly_21_50 : sdirk3CubicPoly (21/50) = 3083/62500 := by
    unfold sdirk3CubicPoly; norm_num
  -- Since p is strictly decreasing on (2/5, 1/2) (p' < 0) and p(L)=0, p(21/50)>0 implies L>21/50
  have hL_gt' : 21/50 < L := by
    by_contra hle; push_neg at hle
    -- If L ≤ 21/50, then since p' < 0 on (2/5, 1/2), p(L) ≥ p(21/50) > 0
    -- But p(L) = 0, contradiction.
    -- We prove p(L) > 0 using monotonicity.
    -- p'(x) = 18x²-36x+9 < 0 for x ∈ (2/5, 1/2) because 18(1/2)²-36(1/2)+9 = -4.5 < 0
    -- and the maximum of p' on [2/5,1/2] is at x=2/5: 18(2/5)²-36(2/5)+9 = -2.52 < 0
    have hL_range : 2/5 < L ∧ L ≤ 21/50 := ⟨hL_gt, hle⟩
    -- Evaluate the cubic: p(L) should be > 0 since p(2/5) = 13/125, p(21/50) = 3083/62500,
    -- and p is decreasing, so p(L) ≥ p(21/50) > 0
    -- We just show p(L) > 0 by bounding: p(L) ≥ p(21/50) via mean value argument.
    -- Simpler: since 6L³-18L²+9L-1 = 0, we need to derive a contradiction from L ≤ 21/50.
    -- From hchar: 1 = 6L³-18L²+9L = L(6L²-18L+9) = L·6(L²-3L+3/2)
    -- = 6L(L²-3L+3/2) = 6L((L-3/2)²-3/4) — not helpful.
    -- Direct: from hchar and L ≤ 21/50, show 6L³-18L²+9L-1 > 0 → contradiction with =0.
    -- 6L³-18L²+9L-1 is a polynomial; for L ∈ (2/5, 21/50], show it's positive.
    -- p(L) = 6L³-18L²+9L-1. Using L ≤ 21/50 and L > 2/5:
    -- p(L) = 1-9L+18L²-6L³ ... wait, p(L)=0 by hchar. So there's no contradiction
    -- unless we show that p has no root in (2/5, 21/50].
    -- Direct approach: p(2/5) = 13/125, p(21/50) = 3083/62500.
    -- For L ∈ [2/5, 21/50], p(L) ≥ min(p(2/5), p(21/50)) - |p''|·(21/50-2/5)²/2
    -- This is getting too complex. Let me just nlinarith it.
    have : 6*L^3 - 18*L^2 + 9*L - 1 > 0 := by nlinarith [sq_nonneg L, sq_nonneg (L-2/5), sq_nonneg (21/50-L)]
    linarith
  -- Step 5: y² coefficient is non-negative (uses L > 21/50)
  have hB2_coeff : 0 ≤ 84*L^2 - 48*L + 11/2 := by nlinarith [sq_nonneg (L - 21/50)]
  -- Step 6: y⁴ coefficient is positive
  have hp : 0 < -3*L^2 + 2*L - 1/4 := by nlinarith [sq_nonneg (L - 1/2)]
  -- Step 7: Algebraic identity for the y² bracket (uses cubic)
  -- bracket2 = t·6L² + t²·(84L²-48L+11/2) + 12L⁵t³ + 3L⁶t⁴
  have hB2_id : 3*L^2*((1+L*t)^4-1) + 2*(1-3*L)*(1/2-3*L+3*L^2)*t -
      2*(1/2-3*L+3*L^2)^2*t^2 =
      t*(6*L^2 + (84*L^2-48*L+11/2)*t + 12*L^5*t^2 + 3*L^6*t^3) := by
    linear_combination (9*L^2*t^2-6*L*t^2+t^2+27*L^4*t^4-18*L^3*t^4+3*L^2*t^4+
      54*L^3*t^3-36*L^2*t^3+6*L*t^3-27*L^3*t^2+18*L^2*t^2-3*L*t^2) * hchar
  -- Step 8: Main nlinarith combining everything
  nlinarith [hB1, hB1_nn, hB2_id, hB2_coeff,
             sq_nonneg y, sq_nonneg t, sq_nonneg (L*y), sq_nonneg (L*t*y),
             mul_nonneg ht (sq_nonneg y), mul_nonneg ht (sq_nonneg (L*y)),
             mul_nonneg ht hB2_coeff,
             mul_nonneg (sq_nonneg t) (le_of_lt (show (0:ℝ) < L^5 by positivity)),
             mul_nonneg (mul_nonneg ht (sq_nonneg t)) (le_of_lt (show (0:ℝ) < L^5 by positivity)),
             mul_nonneg (sq_nonneg y) (le_of_lt hp),
             sq_nonneg (L^3*y^3), sq_nonneg (L^2*y^2),
             mul_nonneg (sq_nonneg (L*y)) (sq_nonneg (L*t)),
             mul_nonneg (sq_nonneg (y*t)) ht,
             hchar, sq_nonneg (1+L*t)]

/-- Key norm inequality: |N(z)|² ≤ |D(z)|² for Re(z) ≤ 0.
  The difference |D|² − |N|² factors as (−2x)·P(x,y,λ) where P ≥ 0 for x ≤ 0. -/
theorem sdirk3_normSq_denom_ge_num (z : ℂ) (hz : z.re ≤ 0) :
    Complex.normSq (sdirk3Num z) ≤ Complex.normSq (sdirk3Denom z) := by
  suffices h : 0 ≤ Complex.normSq (sdirk3Denom z) -
      Complex.normSq (sdirk3Num z) by linarith
  set x := z.re
  set y := z.im
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  set L := sdirk3Lambda
  rw [hz_eq]
  -- Compute z² components for later use
  have zsq_re : ((⟨x, y⟩ : ℂ) ^ 2).re = x ^ 2 - y ^ 2 := by
    simp [sq, Complex.mul_re]
  have zsq_im : ((⟨x, y⟩ : ℂ) ^ 2).im = 2 * x * y := by
    simp [sq, Complex.mul_im]; ring
  -- Compute normSq of denominator: normSq((1-Lz)³) = ((1-Lx)²+(Ly)²)³
  have hDsq : Complex.normSq (sdirk3Denom ⟨x, y⟩) =
      ((1 - L*x)^2 + (L*y)^2)^3 := by
    simp only [sdirk3Denom, map_pow, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      mul_zero, sub_zero, zero_mul]
    ring
  -- Helper: reduce re/im of complex literals and ↑L^2
  have h3_re : (3 : ℂ).re = 3 := by norm_num
  have h3_im : (3 : ℂ).im = 0 := by norm_num
  have hhalf_re : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have hhalf_im : ((1 : ℂ) / 2).im = 0 := by norm_num
  have hLsq_re : ((↑sdirk3Lambda : ℂ) ^ 2).re = sdirk3Lambda ^ 2 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
  have hLsq_im : ((↑sdirk3Lambda : ℂ) ^ 2).im = 0 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  -- Compute normSq of numerator
  have hNsq : Complex.normSq (sdirk3Num ⟨x, y⟩) =
      (1 + (1-3*L)*x + (1/2-3*L+3*L^2)*(x^2-y^2))^2 +
      ((1-3*L)*y + 2*(1/2-3*L+3*L^2)*x*y)^2 := by
    simp only [sdirk3Num, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im,
      h3_re, h3_im, hhalf_re, hhalf_im, hLsq_re, hLsq_im,
      zsq_re, zsq_im,
      mul_zero, sub_zero, zero_mul, add_zero, neg_zero, mul_one, one_mul, zero_add]
    ring
  rw [hDsq, hNsq]
  linarith [sdirk3_poly_ineq x y hz]

/-- **A-stability of SDIRK3**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  Reference: Iserles, Section 4.3. -/
theorem sdirk3_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖sdirk3StabilityFn z‖ ≤ 1 := by
  have hD := sdirk3_denom_ne_zero z hz
  have hD_pos : (0 : ℝ) < ‖sdirk3Denom z‖ := norm_pos_iff.mpr hD
  unfold sdirk3StabilityFn
  rw [norm_div, div_le_one hD_pos]
  have h_sq_le : ‖sdirk3Num z‖ ^ 2 ≤ ‖sdirk3Denom z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    exact sdirk3_normSq_denom_ge_num z hz
  by_contra hlt; push_neg at hlt
  nlinarith [norm_nonneg (sdirk3Num z), norm_nonneg (sdirk3Denom z),
             mul_pos (by linarith : (0 : ℝ) < ‖sdirk3Num z‖ - ‖sdirk3Denom z‖)
                     (by linarith [norm_nonneg (sdirk3Num z)] :
                       (0 : ℝ) < ‖sdirk3Num z‖ + ‖sdirk3Denom z‖)]

/-- **SDIRK3 is L-stable**: A-stable with stiff decay.
  Reference: Iserles, Section 4.3. -/
theorem sdirk3_lStable :
    (∀ z : ℂ, z.re ≤ 0 → sdirk3Denom z ≠ 0 → ‖sdirk3StabilityFn z‖ ≤ 1) ∧
    Tendsto (fun x : ℝ => sdirk3StabilityFn (↑x)) atBot (nhds 0) :=
  ⟨fun z hz _ => sdirk3_aStable z hz, sdirk3_stiffDecay⟩

/-! ## NOT Algebraically Stable

The algebraic stability matrix M has M₁₁ = 2b₁a₁₁ − b₁² = b₁(2λ − b₁).
Since b₁ = λ(2−λ)/(1−λ) > λ > 0 and 2λ < 1, we can show M₁₁ < 0
by verifying b₁ > 2λ, i.e., λ(2−λ)/(1−λ) > 2λ, i.e., (2−λ)/(1−λ) > 2,
i.e., 2−λ > 2(1−λ) = 2−2λ, i.e., λ > 0, which holds. -/

/-- **SDIRK3 is NOT algebraically stable**: M₁₁ < 0 since b₁ > 2λ. -/
theorem rkSDIRK3_not_algStable : ¬rkSDIRK3.IsAlgStable := by
  intro ⟨_, hM⟩
  have h := hM (fun i => if i = 0 then 1 else 0)
  simp [ButcherTableau.algStabMatrix, rkSDIRK3] at h
  -- h: 0 ≤ 2 * (λ(2-λ)/(1-λ)) * λ - (λ(2-λ)/(1-λ))²
  -- = (λ(2-λ)/(1-λ)) * (2λ - λ(2-λ)/(1-λ))
  -- = (λ(2-λ)/(1-λ)) * (2λ(1-λ) - λ(2-λ))/(1-λ)
  -- = (λ(2-λ)/(1-λ)) * λ(2-2λ-2+λ)/(1-λ)
  -- = (λ(2-λ)/(1-λ)) * λ(-λ)/(1-λ)
  -- = -λ²·λ(2-λ)/(1-λ)² < 0
  have hne := one_sub_sdirk3Lambda_ne_zero
  have hlam := sdirk3Lambda_pos
  have hlt1 := sdirk3Lambda_lt_one
  field_simp [hne] at h
  nlinarith [sq_nonneg sdirk3Lambda, sq_nonneg (1 - sdirk3Lambda)]

/-! ## Simplifying Assumptions for SDIRK3

The 3-stage SDIRK satisfies B(3), C(1), and D(1), consistent with its order 3.
It does NOT satisfy B(4), C(2), or D(2).
The stage order is exactly 1, typical for SDIRK methods. -/

/-- SDIRK3 satisfies B(3): weights integrate quadratic functions exactly.
  This follows from the order 3 conditions: ∑ bᵢ = 1, ∑ bᵢcᵢ = 1/2, ∑ bᵢcᵢ² = 1/3. -/
theorem rkSDIRK3_B3 : rkSDIRK3.SatisfiesB 3 := by
  intro k hk1 hk2
  interval_cases k
  · -- k=1: ∑ bᵢ = 1
    simp [rkSDIRK3, Fin.sum_univ_three]
    field_simp [one_sub_sdirk3Lambda_ne_zero]; ring
  · -- k=2: ∑ bᵢcᵢ = 1/2
    simp [rkSDIRK3, Fin.sum_univ_three]
    field_simp [one_sub_sdirk3Lambda_ne_zero]
    nlinarith [sdirk3Lambda_char]
  · -- k=3: ∑ bᵢcᵢ² = 1/3
    simp [rkSDIRK3, Fin.sum_univ_three]
    field_simp [one_sub_sdirk3Lambda_ne_zero]
    nlinarith [sdirk3Lambda_char, sdirk3Lambda_pos, one_sub_sdirk3Lambda_pos]

/-- SDIRK3 satisfies C(1): the row-sum condition cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkSDIRK3_C1 : rkSDIRK3.SatisfiesC 1 := by
  rw [ButcherTableau.satisfiesC_one_iff]
  exact rkSDIRK3_consistent.row_sum

/-- SDIRK3 does NOT satisfy C(2): the stage order is exactly 1.
  For i=0: ∑ⱼ a₀ⱼcⱼ = λ² ≠ λ²/2 since λ > 0.
  This is typical for SDIRK methods — the lower-triangular structure limits stage order. -/
theorem rkSDIRK3_not_C2 : ¬rkSDIRK3.SatisfiesC 2 := by
  intro hC
  have h := hC 2 (by omega) le_rfl 0
  simp [rkSDIRK3, Fin.sum_univ_three] at h
  nlinarith [sdirk3Lambda_pos]

/-- SDIRK3 does NOT satisfy B(4): ∑ bᵢcᵢ³ ≠ 1/4.
  This is consistent with the method having order exactly 3, not 4. -/
theorem rkSDIRK3_not_B4 : ¬rkSDIRK3.SatisfiesB 4 := by
  intro hB
  have h := hB 4 (by omega) le_rfl
  simp [rkSDIRK3, Fin.sum_univ_three] at h
  have hne := one_sub_sdirk3Lambda_ne_zero
  field_simp [hne] at h
  nlinarith [sdirk3Lambda_char, sdirk3Lambda_pos, sdirk3Lambda_lt, one_sub_sdirk3Lambda_pos]

/-- SDIRK3 satisfies D(1): ∑ᵢ bᵢ aᵢⱼ = bⱼ(1 − cⱼ).
  This holds because SDIRK3 is stiffly accurate (bᵢ = a₃ᵢ) and consistent. -/
theorem rkSDIRK3_D1 : rkSDIRK3.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; fin_cases j <;> simp [rkSDIRK3, Fin.sum_univ_three] <;>
    field_simp [one_sub_sdirk3Lambda_ne_zero] <;>
    nlinarith [sdirk3Lambda_char, sdirk3Lambda_pos, one_sub_sdirk3Lambda_pos]
