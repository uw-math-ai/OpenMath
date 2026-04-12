import OpenMath.StiffEquations

/-!
# SDIRK Methods (Section 4.3)

A **singly diagonally implicit Runge–Kutta (SDIRK)** method is an implicit RK method
whose stage coefficient matrix A is lower triangular with equal diagonal entries:
  a_{ij} = 0 for j > i,  a_{ii} = λ for all i.

This structure means each stage requires solving an implicit equation with the same
Jacobian (I - hλJ), amortizing the cost of LU factorization.

## 2-Stage SDIRK (order 2, L-stable)

The classic 2-stage SDIRK with λ = 1 - √2/2:

```
  λ   | λ     0
  1   | 1-λ   λ
  ----|----------
      | 1-λ   λ
```

This is the unique 2-stage SDIRK that is both order 2 and L-stable.

The stability function is R(z) = N(z)/D(z) where:
  N(z) = 1 + (1-2λ)z + (1/2-2λ+λ²)z²  (but 1/2-2λ+λ² = 0 for our λ)
  D(z) = (1 - λz)²

So R(z) = (1 + (1-2λ)z) / (1-λz)² = (1 + (√2-1)z) / (1 - (1-√2/2)z)².

Since deg(N) = 1 < deg(D) = 2, R(z) → 0 as z → -∞, giving stiff decay.

Reference: Iserles, Section 4.3, Example 4.7.
-/

open Finset Real Filter

/-! ## SDIRK structure -/

namespace ButcherTableau

variable {s : ℕ}

/-- A Butcher tableau is **SDIRK** (singly diagonally implicit) if A is lower
  triangular with constant diagonal a_{ii} = λ for some λ. -/
structure IsSDIRK (t : ButcherTableau s) : Prop where
  /-- A is lower triangular: a_{ij} = 0 for j > i. -/
  lower_tri : ∀ i j : Fin s, i < j → t.A i j = 0
  /-- Constant diagonal: a_{ii} is the same for all i. -/
  const_diag : ∀ i j : Fin s, t.A i i = t.A j j

/-- The **SDIRK parameter** λ = a_{11} for a SDIRK method with s ≥ 1. -/
noncomputable def sdirkParam (t : ButcherTableau (s + 1)) : ℝ := t.A 0 0

end ButcherTableau

/-! ## 2-Stage SDIRK Method -/

/-- The SDIRK parameter λ = 1 - √2/2 ≈ 0.2929. -/
noncomputable def sdirk2Lambda : ℝ := 1 - Real.sqrt 2 / 2

/-- **2-stage SDIRK** method with λ = 1 - √2/2.
  Butcher tableau:
  ```
    λ   | λ     0
    1   | 1-λ   λ
    ----|----------
        | 1-λ   λ
  ```
  Reference: Iserles, Section 4.3. -/
noncomputable def rkSDIRK2 : ButcherTableau 2 where
  A := ![![sdirk2Lambda, 0], ![1 - sdirk2Lambda, sdirk2Lambda]]
  b := ![1 - sdirk2Lambda, sdirk2Lambda]
  c := ![sdirk2Lambda, 1]

/-! ### Basic properties -/

private theorem sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
private theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
private theorem sqrt2_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [sqrt2_sq, sq_nonneg (Real.sqrt 2 - 2)]

/-- The SDIRK parameter λ is positive. -/
theorem sdirk2Lambda_pos : 0 < sdirk2Lambda := by
  unfold sdirk2Lambda; linarith [sqrt2_lt_two]

/-- The SDIRK parameter λ < 1. -/
theorem sdirk2Lambda_lt_one : sdirk2Lambda < 1 := by
  unfold sdirk2Lambda; linarith [sqrt2_pos]

/-- Key identity: λ² - 2λ + 1/2 = 0 (characterizing property of this λ). -/
theorem sdirk2Lambda_char : sdirk2Lambda ^ 2 - 2 * sdirk2Lambda + 1/2 = 0 := by
  unfold sdirk2Lambda
  nlinarith [sqrt2_sq]

/-- rkSDIRK2 is a SDIRK method. -/
theorem rkSDIRK2_isSDIRK : rkSDIRK2.IsSDIRK where
  lower_tri := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [rkSDIRK2]
  const_diag := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkSDIRK2]

/-- rkSDIRK2 is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkSDIRK2_consistent : rkSDIRK2.IsConsistent where
  weights_sum := by simp [rkSDIRK2, Fin.sum_univ_two]
  row_sum := by
    intro i; fin_cases i <;> simp [rkSDIRK2, Fin.sum_univ_two]

/-- rkSDIRK2 has order at least 2. -/
theorem rkSDIRK2_order2 : rkSDIRK2.HasOrderGe2 := by
  refine ⟨?_, ?_⟩
  · simp [ButcherTableau.order1, rkSDIRK2, Fin.sum_univ_two]
  · simp [ButcherTableau.order2, rkSDIRK2, Fin.sum_univ_two]
    unfold sdirk2Lambda; nlinarith [sqrt2_sq]

/-- rkSDIRK2 does NOT have order 3: the third-order condition ∑ bᵢcᵢ² = 1/3 fails. -/
theorem rkSDIRK2_not_order3 : ¬rkSDIRK2.HasOrderGe3 := by
  intro ⟨_, _, h3a, _⟩
  simp [ButcherTableau.order3a, rkSDIRK2, Fin.sum_univ_two] at h3a
  -- h3a: (1 - sdirk2Lambda) * sdirk2Lambda ^ 2 + sdirk2Lambda * 1 ^ 2 = 1/3
  -- Expand: sdirk2Lambda - sdirk2Lambda^3 + sdirk2Lambda = 1/3
  -- That is: 2λ - λ³ = 1/3
  -- Using λ² = 2λ - 1/2, so λ³ = 2λ² - λ/2 = 4λ - 1 - λ/2 = 7λ/2 - 1
  -- Then 2λ - (7λ/2 - 1) = 2λ - 7λ/2 + 1 = -3λ/2 + 1
  -- Need -3λ/2 + 1 = 1/3, so λ = 4/9, but our λ = 1 - √2/2
  nlinarith [sdirk2Lambda_char, sdirk2Lambda_pos, sdirk2Lambda_lt_one]

/-- rkSDIRK2 has non-negative weights. -/
theorem rkSDIRK2_nonNegWeights : rkSDIRK2.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkSDIRK2]
  · linarith [sdirk2Lambda_lt_one]
  · linarith [sdirk2Lambda_pos]

/-- rkSDIRK2 is NOT explicit. -/
theorem rkSDIRK2_not_explicit : ¬rkSDIRK2.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkSDIRK2] at this
  linarith [sdirk2Lambda_pos]

/-! ## SDIRK2 Stability Function -/

/-- Numerator of the SDIRK2 stability function: N(z) = 1 + (1-2λ)z.
  Note: the z² coefficient λ²-2λ+1/2 = 0 by construction. -/
noncomputable def sdirk2Num (z : ℂ) : ℂ := 1 + (1 - 2 * (sdirk2Lambda : ℝ)) * z

/-- Denominator of the SDIRK2 stability function: D(z) = (1 - λz)². -/
noncomputable def sdirk2Denom (z : ℂ) : ℂ := (1 - (sdirk2Lambda : ℝ) * z) ^ 2

/-- SDIRK2 stability function: R(z) = (1 + (1-2λ)z) / (1-λz)². -/
noncomputable def sdirk2StabilityFn (z : ℂ) : ℂ := sdirk2Num z / sdirk2Denom z

/-- 1-2λ = √2 - 1 > 0. -/
theorem one_sub_two_sdirk2Lambda : 1 - 2 * sdirk2Lambda = Real.sqrt 2 - 1 := by
  unfold sdirk2Lambda; ring

/-! ### A-Stability -/

/-- The SDIRK2 denominator is nonzero for Re(z) ≤ 0. -/
theorem sdirk2_denom_ne_zero (z : ℂ) (hz : z.re ≤ 0) : sdirk2Denom z ≠ 0 := by
  simp only [sdirk2Denom]
  rw [pow_ne_zero_iff (by norm_num)]
  intro heq
  have : (1 : ℂ) - (sdirk2Lambda : ℝ) * z = 0 := heq
  have hre : (1 : ℂ).re - ((sdirk2Lambda : ℝ) * z).re = 0 := by
    have := congr_arg Complex.re this; simpa using this
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hre
  -- hre : 1 - sdirk2Lambda * z.re = 0, so z.re = 1/λ > 0
  have : z.re = 1 / sdirk2Lambda := by
    field_simp [ne_of_gt sdirk2Lambda_pos] at hre ⊢; linarith
  linarith [sdirk2Lambda_pos, div_pos one_pos sdirk2Lambda_pos]

/-- Key norm inequality: |N(z)|² ≤ |D(z)|² for Re(z) ≤ 0. -/
theorem sdirk2_normSq_denom_ge_num (z : ℂ) (hz : z.re ≤ 0) :
    Complex.normSq (sdirk2Num z) ≤ Complex.normSq (sdirk2Denom z) := by
  suffices h : 0 ≤ Complex.normSq (sdirk2Denom z) -
      Complex.normSq (sdirk2Num z) by linarith
  set x := z.re
  set y := z.im
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  -- Use the characterizing identity λ² - 2λ + 1/2 = 0
  have hchar := sdirk2Lambda_char
  rw [hz_eq]
  simp only [sdirk2Denom, sdirk2Num]
  rw [map_pow]
  -- Reduce to real arithmetic
  have eq1 : (1 : ℂ) - ↑sdirk2Lambda * (⟨x, y⟩ : ℂ) =
      ⟨1 - sdirk2Lambda * x, -(sdirk2Lambda * y)⟩ := by
    apply Complex.ext <;> simp
  have eq2 : (1 : ℂ) + (1 - 2 * ↑sdirk2Lambda) * (⟨x, y⟩ : ℂ) =
      ⟨1 + (1 - 2 * sdirk2Lambda) * x, (1 - 2 * sdirk2Lambda) * y⟩ := by
    apply Complex.ext <;> simp
  rw [eq1, eq2]
  simp only [Complex.normSq_mk]
  -- Key algebraic identity
  have key : ((1 - sdirk2Lambda * x) ^ 2 + sdirk2Lambda * y * (sdirk2Lambda * y)) ^ 2 -
      ((1 + (1 - 2 * sdirk2Lambda) * x) ^ 2 +
       (1 - 2 * sdirk2Lambda) * y * ((1 - 2 * sdirk2Lambda) * y)) =
      (2 * sdirk2Lambda * x - sdirk2Lambda ^ 2 * (x ^ 2 + y ^ 2)) ^ 2 - 2 * x := by
    linear_combination (-2 * x ^ 2 - 2 * y ^ 2) * hchar
  linarith [key, sq_nonneg (2 * sdirk2Lambda * x - sdirk2Lambda ^ 2 * (x ^ 2 + y ^ 2))]

/-- **A-stability of SDIRK2**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  Reference: Iserles, Section 4.3. -/
theorem sdirk2_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖sdirk2StabilityFn z‖ ≤ 1 := by
  have hD := sdirk2_denom_ne_zero z hz
  have hD_pos : (0 : ℝ) < ‖sdirk2Denom z‖ := norm_pos_iff.mpr hD
  unfold sdirk2StabilityFn
  rw [norm_div, div_le_one hD_pos]
  have h_sq_le : ‖sdirk2Num z‖ ^ 2 ≤ ‖sdirk2Denom z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    exact sdirk2_normSq_denom_ge_num z hz
  by_contra hlt; push_neg at hlt
  nlinarith [norm_nonneg (sdirk2Num z), norm_nonneg (sdirk2Denom z),
             mul_pos (by linarith : (0 : ℝ) < ‖sdirk2Num z‖ - ‖sdirk2Denom z‖)
                     (by linarith [norm_nonneg (sdirk2Num z)] :
                       (0 : ℝ) < ‖sdirk2Num z‖ + ‖sdirk2Denom z‖)]

/-! ### Stiff Decay and L-Stability -/

/-- **SDIRK2 has stiff decay**: R(x) → 0 as x → -∞.
  Since deg(N) = 1 < deg(D) = 2, this is immediate. -/
theorem sdirk2_stiffDecay :
    Tendsto (fun x : ℝ => sdirk2StabilityFn (↑x)) atBot (nhds 0) := by
  apply NormedAddCommGroup.tendsto_nhds_zero.mpr
  intro ε hε
  have hlam_pos := sdirk2Lambda_pos
  have hlam2_pos : (0 : ℝ) < sdirk2Lambda ^ 2 := sq_pos_of_pos hlam_pos
  have helam2_pos : (0 : ℝ) < ε * sdirk2Lambda ^ 2 := mul_pos hε hlam2_pos
  filter_upwards [eventually_lt_atBot (min (-1) (min (-2/sdirk2Lambda)
    (-8/(ε * sdirk2Lambda ^ 2))))] with x hx
  -- Decompose the min bound
  have ⟨hx_neg', hx_rest⟩ := lt_min_iff.mp hx
  have ⟨hx_2l, hx_8l⟩ := lt_min_iff.mp hx_rest
  have hx_neg : x < -1 := hx_neg'
  have hnx_pos : (0 : ℝ) < -x := by linarith
  have hx_large : -x > 8 / (ε * sdirk2Lambda ^ 2) := by
    rw [gt_iff_lt, ← neg_lt_neg_iff]; simp only [neg_neg]
    linarith [neg_div_neg_eq (8 : ℝ) (ε * sdirk2Lambda ^ 2)]
  have hx_gt_2l : -x > 2 / sdirk2Lambda := by
    rw [gt_iff_lt, ← neg_lt_neg_iff]; simp only [neg_neg]
    linarith [neg_div_neg_eq (2 : ℝ) sdirk2Lambda]
  have h1_minus_lx : 0 < 1 - sdirk2Lambda * x := by nlinarith
  simp only [sdirk2StabilityFn, sdirk2Num, sdirk2Denom]
  rw [show (1 : ℂ) + (1 - 2 * ↑sdirk2Lambda) * (↑x : ℂ) =
        ((1 + (1-2*sdirk2Lambda)*x : ℝ) : ℂ) from by push_cast; ring,
      show ((1 : ℂ) - ↑sdirk2Lambda * (↑x : ℂ)) ^ 2 =
        ((((1-sdirk2Lambda*x)^2 : ℝ)) : ℂ) from by push_cast; ring,
      show ((1 + (1-2*sdirk2Lambda)*x : ℝ) : ℂ) / (((1-sdirk2Lambda*x)^2 : ℝ) : ℂ) =
        (((1 + (1-2*sdirk2Lambda)*x) / (1-sdirk2Lambda*x)^2 : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hD_pos : (0 : ℝ) < (1 - sdirk2Lambda * x) ^ 2 := sq_pos_of_pos h1_minus_lx
  have h1lx_ge : 1 - sdirk2Lambda * x ≥ sdirk2Lambda * (-x) / 2 := by nlinarith
  have hN_bound : |1 + (1-2*sdirk2Lambda)*x| ≤ 2 * (-x) := by
    rw [abs_le]; constructor
    · nlinarith [sdirk2Lambda_lt_one]
    · nlinarith [sdirk2Lambda_lt_one, sdirk2Lambda_pos]
  calc |((1 + (1 - 2 * sdirk2Lambda) * x) / (1 - sdirk2Lambda * x) ^ 2)|
      = |1 + (1-2*sdirk2Lambda)*x| / |(1-sdirk2Lambda*x)^2| := abs_div _ _
    _ = |1 + (1-2*sdirk2Lambda)*x| / (1-sdirk2Lambda*x)^2 := by
        rw [abs_of_pos hD_pos]
    _ ≤ (2*(-x)) / (1-sdirk2Lambda*x)^2 := by
        apply div_le_div_of_nonneg_right hN_bound (by linarith)
    _ ≤ (2*(-x)) / (sdirk2Lambda*(-x)/2)^2 := by
        apply div_le_div_of_nonneg_left (by linarith) (by positivity)
        exact sq_le_sq' (by nlinarith) h1lx_ge
    _ = 8 / (sdirk2Lambda^2 * (-x)) := by field_simp; ring
    _ < ε := by
        rw [div_lt_iff₀ (by positivity)]
        have hmul := mul_lt_mul_of_pos_right hx_large helam2_pos
        rw [div_mul_cancel₀ 8 (ne_of_gt helam2_pos)] at hmul
        nlinarith

/-- **SDIRK2 is L-stable**: A-stable with stiff decay.
  Reference: Iserles, Section 4.3. -/
theorem sdirk2_lStable :
    (∀ z : ℂ, z.re ≤ 0 → sdirk2Denom z ≠ 0 → ‖sdirk2StabilityFn z‖ ≤ 1) ∧
    Tendsto (fun x : ℝ => sdirk2StabilityFn (↑x)) atBot (nhds 0) :=
  ⟨fun z hz _ => sdirk2_aStable z hz, sdirk2_stiffDecay⟩

/-! ## SDIRK2 is NOT algebraically stable

  The algebraic stability matrix M has M₁₁ = (1-λ)(3λ-1) < 0 since 3λ-1 = 2-3√2/2 < 0.
  With v = (1,0), the quadratic form is negative.
  This is expected: algebraic stability holds for Gauss and Radau IIA methods,
  but NOT for SDIRK methods in general. -/

/-- **SDIRK2 is NOT algebraically stable**: the M₁₁ entry (1-λ)(3λ-1) < 0. -/
theorem rkSDIRK2_not_algStable : ¬rkSDIRK2.IsAlgStable := by
  intro ⟨_, hM⟩
  -- Evaluate with v = (1, 0)
  have h := hM (fun i => if i = 0 then 1 else 0)
  simp [ButcherTableau.algStabMatrix, rkSDIRK2] at h
  -- h: 0 ≤ (1-λ)(3λ-1) which is false
  nlinarith [sdirk2Lambda_char, sdirk2Lambda_pos, sdirk2Lambda_lt_one]
