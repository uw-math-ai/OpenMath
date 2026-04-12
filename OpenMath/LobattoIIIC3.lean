import OpenMath.Collocation
import OpenMath.LobattoIIIC

/-!
# Lobatto IIIC 3-Stage Method (Section 4.2)

The **Lobatto IIIC 3-stage** method is a 3-stage fully implicit Runge–Kutta method
based on Lobatto quadrature with collocation at 0, 1/2, and 1.

Butcher tableau:
```
  0   | 1/6   -1/3    1/6
  1/2 | 1/6    5/12   -1/12
  1   | 1/6    2/3    1/6
  ----|----------------------
      | 1/6    2/3    1/6
```

The weights (1/6, 2/3, 1/6) form Simpson's rule, which integrates polynomials
of degree ≤ 3 exactly, i.e., **B(4)** holds. The method satisfies **C(2)** and
**D(1)**, and the combination B(4) ∧ C(2) ∧ D(1) implies **order 4**.

The first column of A is constant (1/6), a defining characteristic of Lobatto IIIC.

The stability function is R(z) = (24 + 6z) / (24 − 18z + 6z² − z³).
Since deg(N) = 1 < deg(D) = 3, R(z) → 0 as z → −∞, giving stiff decay and L-stability.

The algebraic stability matrix M = (1/36)·[[1,−2,1],[−2,4,−2],[1,−2,1]]
has quadratic form (v₀ − 2v₁ + v₂)²/36 ≥ 0, so the method is **algebraically stable**.

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 4.2; Hairer–Wanner, Table 5.12.
-/

open Finset Real Filter

/-! ## Butcher Tableau Definition -/

/-- **Lobatto IIIC 3-stage** RK method.
  Collocation points: c₁ = 0, c₂ = 1/2, c₃ = 1.
  The first column of A is constant (= b₁ = 1/6).
  Reference: Iserles, Section 4.2 / Hairer–Wanner, Table 5.12. -/
noncomputable def rkLobattoIIIC3 : ButcherTableau 3 where
  A := ![![1/6, -1/3, 1/6],
         ![1/6, 5/12, -1/12],
         ![1/6, 2/3, 1/6]]
  b := ![1/6, 2/3, 1/6]
  c := ![0, 1/2, 1]

/-! ## Basic Properties -/

/-- Lobatto IIIC 3-stage is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkLobattoIIIC3_consistent : rkLobattoIIIC3.IsConsistent where
  weights_sum := by simp [rkLobattoIIIC3, Fin.sum_univ_three]; norm_num
  row_sum := by
    intro i; fin_cases i <;> (simp [rkLobattoIIIC3, Fin.sum_univ_three]; norm_num)

/-- Lobatto IIIC 3-stage has non-negative weights. -/
theorem rkLobattoIIIC3_nonNegWeights : rkLobattoIIIC3.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkLobattoIIIC3] <;> norm_num

/-- Lobatto IIIC 3-stage is stiffly accurate: bᵢ = a_{3,i} for all i. -/
theorem rkLobattoIIIC3_stifflyAccurate :
    ∀ i : Fin 3, rkLobattoIIIC3.b i = rkLobattoIIIC3.A 2 i := by
  intro i; fin_cases i <;> simp [rkLobattoIIIC3]

/-- Lobatto IIIC 3-stage is NOT explicit (a₁₁ = 1/6 ≠ 0). -/
theorem rkLobattoIIIC3_not_explicit : ¬rkLobattoIIIC3.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkLobattoIIIC3] at this

/-- The first column of A is constant (= 1/6), characteristic of Lobatto IIIC. -/
theorem rkLobattoIIIC3_constFirstCol :
    ∀ i : Fin 3, rkLobattoIIIC3.A i 0 = 1/6 := by
  intro i; fin_cases i <;> simp [rkLobattoIIIC3]

/-! ## Simplifying Assumptions

Simpson's rule gives B(4), collocation gives C(2), and the defining
conditions give D(1). Together, B(4) ∧ C(2) ∧ D(1) → order 4.
-/

/-- Lobatto IIIC 3-stage satisfies B(4): Simpson's rule integrates
  polynomials of degree ≤ 3 exactly. -/
theorem rkLobattoIIIC3_B4 : rkLobattoIIIC3.SatisfiesB 4 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkLobattoIIIC3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIC 3-stage satisfies C(2): row-sum and ∑ⱼ aᵢⱼ cⱼ = cᵢ²/2. -/
theorem rkLobattoIIIC3_C2 : rkLobattoIIIC3.SatisfiesC 2 := by
  intro k hk1 hk2 i
  interval_cases k <;> fin_cases i <;>
    simp [rkLobattoIIIC3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIC 3-stage does NOT satisfy C(3): for i=0 (c₀=0),
  ∑ⱼ a₀ⱼ cⱼ² = 1/12 ≠ 0 = c₀³/3. -/
theorem rkLobattoIIIC3_not_C3 : ¬rkLobattoIIIC3.SatisfiesC 3 := by
  intro h
  have h3 := h 3 (by omega) le_rfl 0
  simp [rkLobattoIIIC3, Fin.sum_univ_three] at h3
  norm_num at h3

/-- Lobatto IIIC 3-stage satisfies D(1): ∑ᵢ bᵢ aᵢⱼ = bⱼ(1 − cⱼ). -/
theorem rkLobattoIIIC3_D1 : rkLobattoIIIC3.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk
  fin_cases j <;> simp [rkLobattoIIIC3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIC 3-stage satisfies D(2): ∑ᵢ bᵢ cᵢ aᵢⱼ = bⱼ(1−cⱼ²)/2. -/
theorem rkLobattoIIIC3_D2 : rkLobattoIIIC3.SatisfiesD 2 := by
  intro k hk1 hk2 j
  interval_cases k <;> fin_cases j <;>
    simp [rkLobattoIIIC3, Fin.sum_univ_three] <;> norm_num

/-! ## Order -/

/-- **Lobatto IIIC 3-stage has order 4**, derived from B(4) ∧ C(2) ∧ D(1).
  This is the maximum order 2s − 2 = 4 for a Lobatto-type method with s = 3.
  Reference: Iserles, Theorem 2.6. -/
theorem rkLobattoIIIC3_order4 : rkLobattoIIIC3.HasOrderGe4 := by
  exact ButcherTableau.HasOrderGe4_of_B4_C2_D1 _
    rkLobattoIIIC3_B4 rkLobattoIIIC3_C2 rkLobattoIIIC3_D1

/-- Lobatto IIIC 3-stage does NOT satisfy B(5): Simpson's rule gives
  ∑ bᵢ cᵢ⁴ = 5/24 ≠ 1/5. -/
theorem rkLobattoIIIC3_not_B5 : ¬rkLobattoIIIC3.SatisfiesB 5 := by
  intro h
  have h5 := h 5 (by omega) le_rfl
  simp [rkLobattoIIIC3, Fin.sum_univ_three] at h5
  norm_num at h5

/-! ## Stability Function

The stability function of Lobatto IIIC 3-stage is:
  R(z) = (24 + 6z) / (24 − 18z + 6z² − z³)

Computation: det(I − zA + z·𝟙·bᵀ) = 1 + z/4 (upper triangular!), and
det(I − zA) = 1 − 3z/4 + z²/4 − z³/24.

Since deg(N) = 1 < deg(D) = 3, R(z) → 0 as z → −∞, ensuring stiff decay.
-/

/-- Denominator of the Lobatto IIIC 3-stage stability function:
  D(z) = 24 − 18z + 6z² − z³. -/
noncomputable def lobIIIC3Denom (z : ℂ) : ℂ := 24 - 18 * z + 6 * z ^ 2 - z ^ 3

/-- Numerator of the Lobatto IIIC 3-stage stability function:
  N(z) = 24 + 6z. -/
noncomputable def lobIIIC3Num (z : ℂ) : ℂ := 24 + 6 * z

/-- Lobatto IIIC 3-stage stability function:
  R(z) = (24 + 6z) / (24 − 18z + 6z² − z³). -/
noncomputable def lobIIIC3StabilityFn (z : ℂ) : ℂ := lobIIIC3Num z / lobIIIC3Denom z

/-! ### Denominator Analysis -/

/-- The denominator polynomial 24 − 18x + 6x² − x³ is positive for x ≤ 0. -/
theorem lobIIIC3_denom_pos_real (x : ℝ) (hx : x ≤ 0) :
    0 < 24 - 18 * x + 6 * x ^ 2 - x ^ 3 := by
  nlinarith [sq_nonneg x, sq_nonneg (x - 3)]

/-- Helper: ⟨x,y⟩² = ⟨x²−y², 2xy⟩. -/
private theorem complex_sq (x y : ℝ) :
    (⟨x, y⟩ : ℂ) ^ 2 = ⟨x ^ 2 - y ^ 2, 2 * x * y⟩ := by
  rw [sq]; apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Helper: ⟨x,y⟩³ = ⟨x³−3xy², 3x²y−y³⟩. -/
private theorem complex_cube (x y : ℝ) :
    (⟨x, y⟩ : ℂ) ^ 3 = ⟨x ^ 3 - 3 * x * y ^ 2, 3 * x ^ 2 * y - y ^ 3⟩ := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, complex_sq]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The denominator is nonzero for Re(z) ≤ 0. -/
theorem lobIIIC3_denom_ne_zero (z : ℂ) (hz : z.re ≤ 0) :
    lobIIIC3Denom z ≠ 0 := by
  intro heq
  set x := z.re
  set y := z.im
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  rw [hz_eq] at heq
  -- Compute D(⟨x,y⟩)
  have hD : lobIIIC3Denom ⟨x, y⟩ =
      ⟨24 - 18 * x + 6 * (x ^ 2 - y ^ 2) - (x ^ 3 - 3 * x * y ^ 2),
       -18 * y + 6 * (2 * x * y) - (3 * x ^ 2 * y - y ^ 3)⟩ := by
    simp only [lobIIIC3Denom, complex_sq, complex_cube]
    apply Complex.ext <;> simp
  rw [hD] at heq
  have hre : 24 - 18 * x + 6 * (x ^ 2 - y ^ 2) - (x ^ 3 - 3 * x * y ^ 2) = 0 := by
    have := congr_arg Complex.re heq; simpa using this
  have him : -18 * y + 6 * (2 * x * y) - (3 * x ^ 2 * y - y ^ 3) = 0 := by
    have := congr_arg Complex.im heq; simpa using this
  -- From im = 0: y·(-18 + 12x - 3x² + y²) = 0
  have him' : y * (-18 + 12 * x - 3 * x ^ 2 + y ^ 2) = 0 := by linarith
  rcases mul_eq_zero.mp him' with hy0 | hfactor
  · -- Case y = 0: D(x) = 24-18x+6x²-x³ > 0
    rw [hy0] at hre; simp at hre
    linarith [lobIIIC3_denom_pos_real x hz]
  · -- Case y² = 18 - 12x + 3x²
    have hy2 : y ^ 2 = 18 - 12 * x + 3 * x ^ 2 := by linarith
    -- Substitute into re = 0:
    -- re = 24 - 18x + 6(x²-y²) - (x³-3xy²)
    --    = 24 - 18x + 6x² - 6y² - x³ + 3xy²
    -- With y² = 18-12x+3x²:
    -- = 24-18x+6x²-6(18-12x+3x²)-x³+3x(18-12x+3x²)
    -- = 24-18x+6x²-108+72x-18x²-x³+54x-36x²+9x³
    -- = (24-108)+(-18+72+54)x+(6-18-36)x²+(-1+9)x³
    -- = -84+108x-48x²+8x³ = 4(-21+27x-12x²+2x³)
    have hsub : 24 - 18 * x + 6 * (x ^ 2 - (18 - 12 * x + 3 * x ^ 2)) -
        (x ^ 3 - 3 * x * (18 - 12 * x + 3 * x ^ 2)) =
        8 * x ^ 3 - 48 * x ^ 2 + 108 * x - 84 := by ring
    rw [show 24 - 18 * x + 6 * (x ^ 2 - y ^ 2) - (x ^ 3 - 3 * x * y ^ 2) =
        24 - 18 * x + 6 * (x ^ 2 - (18 - 12 * x + 3 * x ^ 2)) -
        (x ^ 3 - 3 * x * (18 - 12 * x + 3 * x ^ 2)) from by rw [hy2]] at hre
    rw [hsub] at hre
    -- 8x³-48x²+108x-84: for x ≤ 0 each term is ≤ 0, sum ≤ -84 < 0
    nlinarith [sq_nonneg x]

/-! ### Stability Function: A-Stability

We prove |R(z)| ≤ 1 for Re(z) ≤ 0 by showing |N(z)|² ≤ |D(z)|².

The key algebraic identity (in terms of x = Re(z), y = Im(z)):
  |D|² − |N|² = (−x)·P(x,y) + y⁶
where P(x,y) ≥ 0 for x ≤ 0. -/

/-- **A-stability of Lobatto IIIC 3-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  Reference: Iserles, Section 4.2. -/
theorem lobIIIC3_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖lobIIIC3StabilityFn z‖ ≤ 1 := by
  have hD := lobIIIC3_denom_ne_zero z hz
  have hD_pos : (0 : ℝ) < ‖lobIIIC3Denom z‖ := norm_pos_iff.mpr hD
  unfold lobIIIC3StabilityFn
  rw [norm_div, div_le_one hD_pos]
  -- Need: ‖N(z)‖ ≤ ‖D(z)‖, equivalently |N|² ≤ |D|²
  suffices h_sq_le : ‖lobIIIC3Num z‖ ^ 2 ≤ ‖lobIIIC3Denom z‖ ^ 2 by
    by_contra hlt; push_neg at hlt
    nlinarith [norm_nonneg (lobIIIC3Num z), norm_nonneg (lobIIIC3Denom z),
               mul_pos (by linarith : (0 : ℝ) < ‖lobIIIC3Num z‖ - ‖lobIIIC3Denom z‖)
                       (by linarith [norm_nonneg (lobIIIC3Num z)] :
                         (0 : ℝ) < ‖lobIIIC3Num z‖ + ‖lobIIIC3Denom z‖)]
  rw [Complex.sq_norm, Complex.sq_norm]
  set x := z.re
  set y := z.im
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  rw [hz_eq]
  -- Compute normSq of numerator
  have hN_eq : lobIIIC3Num ⟨x, y⟩ = ⟨24 + 6 * x, 6 * y⟩ := by
    simp only [lobIIIC3Num]; apply Complex.ext <;> simp
  -- Compute normSq of denominator
  have hD_eq : lobIIIC3Denom ⟨x, y⟩ =
      ⟨24 - 18 * x + 6 * x ^ 2 - 6 * y ^ 2 - x ^ 3 + 3 * x * y ^ 2,
       -18 * y + 12 * x * y - 3 * x ^ 2 * y + y ^ 3⟩ := by
    simp only [lobIIIC3Denom, complex_sq, complex_cube]
    apply Complex.ext <;> simp <;> ring
  rw [hN_eq, hD_eq, Complex.normSq_mk, Complex.normSq_mk]
  -- Goal: (24+6x)² + (6y)² ≤ D_re² + D_im²
  set Dr := 24 - 18 * x + 6 * x ^ 2 - 6 * y ^ 2 - x ^ 3 + 3 * x * y ^ 2
  set Di := -18 * y + 12 * x * y - 3 * x ^ 2 * y + y ^ 3
  -- Show Dr² + Di² - (24+6x)² - (6y)² ≥ 0
  suffices h : 0 ≤ Dr * Dr + Di * Di - ((24 + 6 * x) * (24 + 6 * x) + 6 * y * (6 * y)) by
    linarith
  -- We prove this by decomposing into non-negative terms
  -- The expression is a polynomial in x, y. We use: for x ≤ 0, (-x) ≥ 0.
  -- Factor: |D|²-|N|² = (-x)·Q₁ + (-x)·Q₂·y² + (-x)·Q₃·y⁴ + y⁶
  -- where Q₁, Q₂, Q₃ ≥ 0 for x ≤ 0.
  have hx : x ≤ 0 := hz
  have hnx : 0 ≤ -x := by linarith
  -- Direct nlinarith with helper terms
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x * y), sq_nonneg (x ^ 2),
             sq_nonneg (x * y ^ 2), sq_nonneg (y ^ 2), sq_nonneg (x ^ 2 * y),
             sq_nonneg (y ^ 3), sq_nonneg (x ^ 2 - 3 * y ^ 2),
             sq_nonneg (x * y ^ 2 - 6 * y),
             mul_self_nonneg (Dr - 24 - 6 * x),
             mul_self_nonneg (Di - 6 * y),
             mul_nonneg hnx (sq_nonneg x),
             mul_nonneg hnx (sq_nonneg y),
             mul_nonneg hnx (sq_nonneg (x * y)),
             mul_nonneg (mul_nonneg hnx (sq_nonneg x)) (sq_nonneg y)]

/-! ### Stiff Decay and L-Stability -/

/-- **IIIC 3-stage has stiff decay**: R(x) → 0 as x → −∞.
  Since deg(N) = 1 < deg(D) = 3, this is immediate. -/
theorem lobIIIC3_stiffDecay :
    Tendsto (fun x : ℝ => lobIIIC3StabilityFn (↑x)) atBot (nhds 0) := by
  apply NormedAddCommGroup.tendsto_nhds_zero.mpr
  intro ε hε
  -- For large |x|, |R(x)| ≈ 6/x² → 0
  filter_upwards [eventually_lt_atBot (min (-1) (-48/ε))] with x hx
  have hx_neg : x < -1 := by linarith [min_le_left (-1 : ℝ) (-48/ε)]
  have hnx : 0 < -x := by linarith
  have hD_pos : (0 : ℝ) < 24 - 18 * x + 6 * x ^ 2 - x ^ 3 :=
    lobIIIC3_denom_pos_real x (by linarith)
  -- Simplify to real computation
  simp only [lobIIIC3StabilityFn, lobIIIC3Num, lobIIIC3Denom]
  rw [show (24 : ℂ) + 6 * (↑x : ℂ) = ((24 + 6 * x : ℝ) : ℂ) from by push_cast; ring,
      show (24 : ℂ) - 18 * (↑x : ℂ) + 6 * (↑x : ℂ) ^ 2 - (↑x : ℂ) ^ 3 =
        ((24 - 18 * x + 6 * x ^ 2 - x ^ 3 : ℝ) : ℂ) from by push_cast; ring,
      show ((24 + 6 * x : ℝ) : ℂ) / ((24 - 18 * x + 6 * x ^ 2 - x ^ 3 : ℝ) : ℂ) =
        (((24 + 6 * x) / (24 - 18 * x + 6 * x ^ 2 - x ^ 3) : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  -- Bound: D ≥ (-x)³ for x ≤ -1, and |N| ≤ 24 + 6(-x) ≤ 30(-x)
  have hD_lower : (-x) ^ 3 ≤ 24 - 18 * x + 6 * x ^ 2 - x ^ 3 := by nlinarith [sq_nonneg x]
  have hnx3_pos : (0 : ℝ) < (-x) ^ 3 := by positivity
  have hN_bound : |24 + 6 * x| ≤ 24 + 6 * (-x) := by rw [abs_le]; constructor <;> nlinarith
  have hN_bound2 : 24 + 6 * (-x) ≤ 48 * (-x) := by nlinarith
  calc |(24 + 6 * x) / (24 - 18 * x + 6 * x ^ 2 - x ^ 3)|
      = |24 + 6 * x| / |24 - 18 * x + 6 * x ^ 2 - x ^ 3| := abs_div _ _
    _ = |24 + 6 * x| / (24 - 18 * x + 6 * x ^ 2 - x ^ 3) := by
        rw [abs_of_pos hD_pos]
    _ ≤ (48 * (-x)) / (24 - 18 * x + 6 * x ^ 2 - x ^ 3) := by
        apply div_le_div_of_nonneg_right (le_trans hN_bound hN_bound2) (by linarith)
    _ ≤ (48 * (-x)) / (-x) ^ 3 := by
        apply div_le_div_of_nonneg_left (by positivity) hnx3_pos hD_lower
    _ = 48 / (-x) ^ 2 := by
        rw [show (-x) ^ 3 = (-x) ^ 2 * (-x) from by ring]
        rw [mul_div_mul_right _ _ (ne_of_gt hnx)]
    _ < ε := by
        -- From x < min(-1, -48/ε), extract x < -48/ε
        have h1 : x < -48 / ε := lt_of_lt_of_le hx (min_le_right _ _)
        -- So 48/ε < -x (since -48/ε = -(48/ε))
        have hx_bound : 48 / ε < -x := by linarith [neg_div_neg_eq (48 : ℝ) ε]
        -- (-x)² > 48/ε since -x > 48/ε > 0 and -x > 1
        have h_sq : (-x) ^ 2 > 48 / ε := by
          nlinarith [div_pos (by norm_num : (0:ℝ) < 48) hε]
        -- So ε·(-x)² > 48, giving 48/(-x)² < ε
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < (-x)^2)]
        have : 48 < ε * (-x) ^ 2 := by
          have := (div_lt_iff₀ hε).mp (by linarith : 48 / ε < (-x) ^ 2)
          linarith
        linarith

/-- **Lobatto IIIC 3-stage is L-stable**: A-stable with stiff decay.
  Reference: Iserles, Section 4.2. -/
theorem lobIIIC3_lStable :
    (∀ z : ℂ, z.re ≤ 0 → lobIIIC3Denom z ≠ 0 → ‖lobIIIC3StabilityFn z‖ ≤ 1) ∧
    Tendsto (fun x : ℝ => lobIIIC3StabilityFn (↑x)) atBot (nhds 0) :=
  ⟨fun z hz _ => lobIIIC3_aStable z hz, lobIIIC3_stiffDecay⟩

/-! ## Algebraic Stability -/

/-- **Lobatto IIIC 3-stage is algebraically stable.**
  The algebraic stability matrix M = (1/36)·[[1,−2,1],[−2,4,−2],[1,−2,1]]
  has rank 1, with quadratic form v^T M v = (v₀ − 2v₁ + v₂)²/36 ≥ 0.
  Reference: Iserles, Definition 4.11 / Hairer–Wanner, Theorem 5.5. -/
theorem rkLobattoIIIC3_algStable : rkLobattoIIIC3.IsAlgStable where
  nonneg_weights := rkLobattoIIIC3_nonNegWeights
  posdef_M := by
    intro v; simp [ButcherTableau.algStabMatrix, rkLobattoIIIC3, Fin.sum_univ_three]
    nlinarith [sq_nonneg (v 0 - 2 * v 1 + v 2)]

/-! ## Comparison: IIIC 2-Stage vs 3-Stage

| Property          | IIIC 2-stage            | IIIC 3-stage              |
|-------------------|-------------------------|---------------------------|
| Stages            | 2                       | 3                         |
| Order             | 2                       | 4                         |
| R(z)              | 2/(z²-2z+2)            | (24+6z)/(24-18z+6z²-z³)  |
| R(−∞)             | 0                       | 0                         |
| L-stable          | ✓                       | ✓                         |
| Alg. stable       | ✓                       | ✓                         |
| Stiffly accurate  | ✓                       | ✓                         |
| C(q)              | C(1)                    | C(2)                      |
| D(r)              | D(1)                    | D(2)                      |
-/
