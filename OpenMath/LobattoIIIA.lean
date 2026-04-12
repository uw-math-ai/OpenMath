import OpenMath.StiffEquations

/-!
# Lobatto IIIA 2-Stage Method (Section 4.2)

The **Lobatto IIIA 2-stage** method is a 2-stage implicit Runge–Kutta method
based on Lobatto quadrature with collocation at endpoints 0 and 1.

Butcher tableau:
```
  0 | 0    0
  1 | 1/2  1/2
  --|----------
    | 1/2  1/2
```

This is equivalent to the **trapezoidal rule** formulated as a Runge–Kutta method.

The stability function is R(z) = (2+z)/(2-z), the same as the implicit midpoint rule.
Since deg(numerator) = deg(denominator) = 1, R(z) → -1 as z → -∞,
so the method does NOT have stiff decay and is NOT L-stable.

The method is NOT algebraically stable: M₁₁ = 2b₁a₁₁ - b₁² = -1/4 < 0.

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 4.2; Hairer–Wanner, Table 5.5.
-/

open Finset Real Filter

/-! ## Butcher Tableau Definition -/

/-- **Lobatto IIIA 2-stage** RK method.
  Collocation points: c₁ = 0, c₂ = 1 (endpoints of [0,1]).
  This is the trapezoidal rule as an RK method.
  Reference: Iserles, Section 4.2 / Hairer–Wanner, Table 5.5. -/
noncomputable def rkLobattoIIIA2 : ButcherTableau 2 where
  A := ![![0, 0], ![1/2, 1/2]]
  b := ![1/2, 1/2]
  c := ![0, 1]

/-! ## Basic Properties -/

/-- Lobatto IIIA 2-stage is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkLobattoIIIA2_consistent : rkLobattoIIIA2.IsConsistent where
  weights_sum := by simp [rkLobattoIIIA2, Fin.sum_univ_two]; norm_num

  row_sum := by
    intro i; fin_cases i
    · simp [rkLobattoIIIA2, Fin.sum_univ_two]
    · simp [rkLobattoIIIA2, Fin.sum_univ_two]; norm_num

/-- Lobatto IIIA 2-stage has order at least 2. -/
theorem rkLobattoIIIA2_order2 : rkLobattoIIIA2.HasOrderGe2 := by
  refine ⟨?_, ?_⟩
  · simp [ButcherTableau.order1, rkLobattoIIIA2, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order2, rkLobattoIIIA2, Fin.sum_univ_two]

/-- Lobatto IIIA 2-stage does NOT have order 3: ∑ bᵢ cᵢ² = 1/2 ≠ 1/3. -/
theorem rkLobattoIIIA2_not_order3 : ¬rkLobattoIIIA2.HasOrderGe3 := by
  intro ⟨_, _, h3a, _⟩
  simp [ButcherTableau.order3a, rkLobattoIIIA2, Fin.sum_univ_two] at h3a

/-- Lobatto IIIA 2-stage has non-negative weights. -/
theorem rkLobattoIIIA2_nonNegWeights : rkLobattoIIIA2.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkLobattoIIIA2]

/-- Lobatto IIIA 2-stage is NOT explicit (a₂₂ = 1/2 ≠ 0). -/
theorem rkLobattoIIIA2_not_explicit : ¬rkLobattoIIIA2.IsExplicit := by
  intro h; have := h 1 1 (le_refl _); simp [rkLobattoIIIA2] at this

/-- Lobatto IIIA 2-stage is stiffly accurate: bᵢ = a_{2,i} for all i. -/
theorem rkLobattoIIIA2_stifflyAccurate :
    ∀ i : Fin 2, rkLobattoIIIA2.b i = rkLobattoIIIA2.A 1 i := by
  intro i; fin_cases i <;> simp [rkLobattoIIIA2]

/-! ## Stability Function

The stability function of Lobatto IIIA 2-stage is R(z) = (2+z)/(2-z).
This is computed from R(z) = 1 + z·bᵀ(I - zA)⁻¹·𝟙:
  det(I - zA) = 1 - z/2  (since A is lower triangular with eigenvalues 0 and 1/2)
  R(z) = (2 + z) / (2 - z)

Since deg(numerator) = deg(denominator) = 1, the stability function
does not decay: R(z) → -1 as z → -∞ (NOT L-stable).
-/

/-- Numerator of the Lobatto IIIA 2-stage stability function: N(z) = 2 + z. -/
noncomputable def lobIIIANum (z : ℂ) : ℂ := 2 + z

/-- Denominator of the Lobatto IIIA 2-stage stability function: D(z) = 2 - z. -/
noncomputable def lobIIIADenom (z : ℂ) : ℂ := 2 - z

/-- Lobatto IIIA 2-stage stability function: R(z) = (2+z)/(2-z). -/
noncomputable def lobIIIAStabilityFn (z : ℂ) : ℂ := lobIIIANum z / lobIIIADenom z

/-! ### A-Stability -/

/-- Key norm inequality: |N(z)|² ≤ |D(z)|² for Re(z) ≤ 0.
  The key identity: |D|² - |N|² = -8·Re(z) ≥ 0 for Re(z) ≤ 0. -/
theorem lobIIIA_normSq_denom_ge_num (z : ℂ) (hz : z.re ≤ 0) :
    Complex.normSq (lobIIIANum z) ≤ Complex.normSq (lobIIIADenom z) := by
  set x := z.re
  set y := z.im
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  rw [hz_eq]
  have hN : lobIIIANum ⟨x, y⟩ = ⟨2 + x, y⟩ := by
    simp only [lobIIIANum]; apply Complex.ext <;> simp
  have hD : lobIIIADenom ⟨x, y⟩ = ⟨2 - x, -y⟩ := by
    simp only [lobIIIADenom]; apply Complex.ext <;> simp
  rw [hN, hD, Complex.normSq_mk, Complex.normSq_mk]
  -- Need: (2+x)² + y² ≤ (2-x)² + (-y)²
  -- i.e., (2+x)² + y² ≤ (2-x)² + y²
  -- i.e., (2+x)² ≤ (2-x)²
  -- i.e., 4+4x+x² ≤ 4-4x+x², i.e., 8x ≤ 0
  nlinarith [sq_nonneg y]

/-- The Lobatto IIIA denominator is nonzero for Re(z) ≤ 0. -/
theorem lobIIIA_denom_ne_zero (z : ℂ) (hz : z.re ≤ 0) :
    lobIIIADenom z ≠ 0 := by
  intro heq
  have : (lobIIIADenom z).re = 0 := by rw [heq]; simp
  simp only [lobIIIADenom, Complex.sub_re] at this; norm_num at this; linarith

/-- **A-stability of Lobatto IIIA 2-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  Reference: Iserles, Section 4.2. -/
theorem lobIIIA_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖lobIIIAStabilityFn z‖ ≤ 1 := by
  have hD := lobIIIA_denom_ne_zero z hz
  have hD_pos : (0 : ℝ) < ‖lobIIIADenom z‖ := norm_pos_iff.mpr hD
  unfold lobIIIAStabilityFn
  rw [norm_div, div_le_one hD_pos]
  have h_sq_le : ‖lobIIIANum z‖ ^ 2 ≤ ‖lobIIIADenom z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    exact lobIIIA_normSq_denom_ge_num z hz
  by_contra hlt; push_neg at hlt
  nlinarith [norm_nonneg (lobIIIANum z), norm_nonneg (lobIIIADenom z),
             mul_pos (by linarith : (0 : ℝ) < ‖lobIIIANum z‖ - ‖lobIIIADenom z‖)
                     (by linarith [norm_nonneg (lobIIIANum z)] :
                       (0 : ℝ) < ‖lobIIIANum z‖ + ‖lobIIIADenom z‖)]

/-! ### NOT L-Stable

The Lobatto IIIA stability function satisfies R(x) → -1 as x → -∞,
so it does NOT have stiff decay and is NOT L-stable. -/

/-- The Lobatto IIIA stability function tends to -1 as x → -∞.
  Since R(x) = (2+x)/(2-x) and for large |x|, this approaches x/(-x) = -1. -/
theorem lobIIIA_stabilityFn_tendsto_neg_one :
    Tendsto (fun x : ℝ => lobIIIAStabilityFn (↑x)) atBot (nhds (-1 : ℂ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_lt_atBot (min (-1) (-4/ε))] with x hx
  have hx_neg : x < -1 := by linarith [min_le_left (-1 : ℝ) (-4/ε)]
  have h2mx_pos : (0 : ℝ) < 2 - x := by linarith
  have hDne : (2 : ℂ) - (↑x : ℂ) ≠ 0 := by
    rw [show (2 : ℂ) - (↑x : ℂ) = ((2 - x : ℝ) : ℂ) from by push_cast; ring]
    exact_mod_cast ne_of_gt h2mx_pos
  -- R(x) = (2+x)/(2-x), R(x) + 1 = 4/(2-x)
  simp only [lobIIIAStabilityFn, lobIIIANum, lobIIIADenom, dist_comm, dist_eq_norm]
  -- Rewrite: -1 - (2+x)/(2-x) = (-1·(2-x) - (2+x))/(2-x) = -4/(2-x)
  rw [show (-1 : ℂ) - ((2 : ℂ) + (↑x : ℂ)) / ((2 : ℂ) - (↑x : ℂ)) =
      -4 / ((2 : ℂ) - (↑x : ℂ)) from by field_simp; ring]
  rw [show (-4 : ℂ) / ((2 : ℂ) - (↑x : ℂ)) = (((-4) / (2 - x) : ℝ) : ℂ) from by
    push_cast; field_simp]
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [show |(-4 : ℝ) / (2 - x)| = 4 / (2 - x) from by
    rw [abs_div, abs_of_nonpos (by norm_num : (-4 : ℝ) ≤ 0),
        abs_of_pos h2mx_pos]; ring]
  rw [div_lt_iff₀ h2mx_pos]
  have hx_bound : x < -4/ε := by linarith [min_le_right (-1 : ℝ) (-4/ε)]
  -- Need: 4 < ε * (2 - x). From x < -4/ε: -x > 4/ε, so ε*(-x) > 4
  have : ε * (-x) > 4 := by
    rw [show ε * (-x) = -(ε * x) from by ring]
    have : ε * x < ε * (-4/ε) := mul_lt_mul_of_pos_left hx_bound hε
    have : ε * (-4/ε) = -4 := by field_simp
    linarith
  linarith

/-- **Lobatto IIIA does NOT have stiff decay**: R(x) → -1 ≠ 0 as x → -∞. -/
theorem lobIIIA_not_stiffDecay :
    ¬Tendsto (fun x : ℝ => lobIIIAStabilityFn (↑x)) atBot (nhds 0) := by
  intro h_zero
  exact absurd (tendsto_nhds_unique h_zero lobIIIA_stabilityFn_tendsto_neg_one) (by norm_num)

/-! ## NOT Algebraically Stable -/

/-- **Lobatto IIIA 2-stage is NOT algebraically stable.**
  The M₁₁ entry is 2b₁a₁₁ - b₁² = 2·(1/2)·0 - (1/2)² = -1/4 < 0.
  With v = (1,0), the quadratic form is -1/4 < 0. -/
theorem rkLobattoIIIA2_not_algStable : ¬rkLobattoIIIA2.IsAlgStable := by
  intro ⟨_, hM⟩
  have h := hM (fun i => if i = 0 then 1 else 0)
  simp [ButcherTableau.algStabMatrix, rkLobattoIIIA2] at h
  linarith

/-! ## Comparison with Lobatto IIIC

The Lobatto IIIA and IIIC 2-stage methods share the same nodes c = (0, 1)
and weights b = (1/2, 1/2), but differ in their stage matrices:
- IIIA: A = [[0, 0], [1/2, 1/2]] (lower triangular)
- IIIC: A = [[1/2, -1/2], [1/2, 1/2]] (fully implicit)

Key differences:
- IIIA has R(z) = (2+z)/(2-z) → -1 (NOT L-stable)
- IIIC has R(z) = 2/(z²-2z+2) → 0 (L-stable)
- IIIA is NOT algebraically stable (M₁₁ = -1/4)
- IIIC IS algebraically stable
- Both are A-stable and order 2
-/
