import OpenMath.StiffEquations
import OpenMath.Collocation

/-!
# Lobatto IIIC 2-Stage Method (Section 4.2)

The **Lobatto IIIC 2-stage** method is a 2-stage fully implicit Runge–Kutta method
based on Lobatto quadrature with collocation at endpoints 0 and 1.

Butcher tableau:
```
  0 | 1/2   -1/2
  1 | 1/2    1/2
  --|------------
    | 1/2    1/2
```

The stability function is R(z) = 2/(z² - 2z + 2).
Since deg(numerator) = 0 < deg(denominator) = 2, R(z) → 0 as z → -∞,
giving stiff decay and hence L-stability.

The method is also algebraically stable: the matrix
M_{ij} = b_i a_{ij} + b_j a_{ji} - b_i b_j = (1/4)·[[1,-1],[-1,1]]
is positive semidefinite with quadratic form (v₁ - v₂)²/4 ≥ 0.

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 4.2; Hairer–Wanner, Table 5.7.
-/

open Finset Real Filter

/-! ## Butcher Tableau Definition -/

/-- **Lobatto IIIC 2-stage** RK method.
  Collocation points: c₁ = 0, c₂ = 1 (endpoints of [0,1]).
  Reference: Iserles, Section 4.2 / Hairer–Wanner, Table 5.7. -/
noncomputable def rkLobattoIIIC2 : ButcherTableau 2 where
  A := ![![1/2, -1/2], ![1/2, 1/2]]
  b := ![1/2, 1/2]
  c := ![0, 1]

/-! ## Basic Properties -/

/-- Lobatto IIIC 2-stage is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkLobattoIIIC2_consistent : rkLobattoIIIC2.IsConsistent where
  weights_sum := by simp [rkLobattoIIIC2, Fin.sum_univ_two]; norm_num
  row_sum := by
    intro i; fin_cases i <;> simp [rkLobattoIIIC2, Fin.sum_univ_two] <;> norm_num

/-- Lobatto IIIC 2-stage has order at least 2. -/
theorem rkLobattoIIIC2_order2 : rkLobattoIIIC2.HasOrderGe2 := by
  refine ⟨?_, ?_⟩
  · simp [ButcherTableau.order1, rkLobattoIIIC2, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order2, rkLobattoIIIC2, Fin.sum_univ_two]

/-- Lobatto IIIC 2-stage does NOT have order 3: ∑ bᵢ cᵢ² = 1/2 ≠ 1/3. -/
theorem rkLobattoIIIC2_not_order3 : ¬rkLobattoIIIC2.HasOrderGe3 := by
  intro ⟨_, _, h3a, _⟩
  simp [ButcherTableau.order3a, rkLobattoIIIC2, Fin.sum_univ_two] at h3a

/-- Lobatto IIIC 2-stage has non-negative weights. -/
theorem rkLobattoIIIC2_nonNegWeights : rkLobattoIIIC2.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkLobattoIIIC2]

/-- Lobatto IIIC 2-stage is NOT explicit (a₁₁ = 1/2 ≠ 0). -/
theorem rkLobattoIIIC2_not_explicit : ¬rkLobattoIIIC2.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkLobattoIIIC2] at this

/-- Lobatto IIIC 2-stage is stiffly accurate: bᵢ = a_{2,i} for all i. -/
theorem rkLobattoIIIC2_stifflyAccurate :
    ∀ i : Fin 2, rkLobattoIIIC2.b i = rkLobattoIIIC2.A 1 i := by
  intro i; fin_cases i <;> simp [rkLobattoIIIC2]

/-! ## Simplifying Assumptions B/C/D -/

/-- Lobatto IIIC 2-stage satisfies B(2): the quadrature weights integrate
polynomials of degree ≤ 1 exactly. -/
theorem rkLobattoIIIC2_B2 : rkLobattoIIIC2.SatisfiesB 2 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkLobattoIIIC2, Fin.sum_univ_two] <;> norm_num

/-- Lobatto IIIC 2-stage does NOT satisfy B(3): quadrature order is exactly 2.
  ∑ b_i c_i² = 1/2 ≠ 1/3. -/
theorem rkLobattoIIIC2_not_B3 : ¬rkLobattoIIIC2.SatisfiesB 3 := by
  intro h
  have := h 3 (by omega) (by omega)
  simp [rkLobattoIIIC2, Fin.sum_univ_two] at this
  linarith

/-- Lobatto IIIC 2-stage satisfies C(1): the row-sum condition holds. -/
theorem rkLobattoIIIC2_C1 : rkLobattoIIIC2.SatisfiesC 1 := by
  intro k hk1 hk2 i
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; fin_cases i <;>
    simp [rkLobattoIIIC2, Fin.sum_univ_two] <;> norm_num

/-- Lobatto IIIC 2-stage does NOT satisfy C(2): stage order is exactly 1.
  ∑_j a_{0,j} c_j = -1/2 ≠ 0 = c_0²/2. -/
theorem rkLobattoIIIC2_not_C2 : ¬rkLobattoIIIC2.SatisfiesC 2 := by
  intro h
  have := h 2 (by omega) (by omega) 0
  simp [rkLobattoIIIC2, Fin.sum_univ_two] at this
  linarith

/-- Lobatto IIIC 2-stage satisfies D(1): ∑_i b_i a_{i,j} = b_j(1 − c_j). -/
theorem rkLobattoIIIC2_D1 : rkLobattoIIIC2.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; fin_cases j <;>
    simp [rkLobattoIIIC2, Fin.sum_univ_two] <;> norm_num

/-- Lobatto IIIC 2-stage does NOT satisfy D(2). -/
theorem rkLobattoIIIC2_not_D2 : ¬rkLobattoIIIC2.SatisfiesD 2 := by
  intro h
  have := h 2 (by omega) (by omega) 1
  simp [rkLobattoIIIC2, Fin.sum_univ_two] at this
  linarith

/-! ## Stability Function

The stability function of Lobatto IIIC 2-stage is R(z) = 2/(z² - 2z + 2).
This is computed from R(z) = 1 + z·bᵀ(I - zA)⁻¹·𝟙:
  det(I - zA) = (1 - z/2)² + z²/4 = 1 - z + z²/2
  R(z) = 1/(1 - z + z²/2) = 2/(z² - 2z + 2)

Since the numerator has degree 0 and the denominator has degree 2,
R(z) → 0 as |z| → ∞, ensuring stiff decay.
-/

/-- Denominator of the Lobatto IIIC 2-stage stability function:
  D(z) = z² - 2z + 2 = (z - 1)² + 1. -/
noncomputable def lobIIICDenom (z : ℂ) : ℂ := z ^ 2 - 2 * z + 2

/-- Lobatto IIIC 2-stage stability function:
  R(z) = 2 / (z² - 2z + 2).
  Equivalently, R(z) = 1/(1 - z + z²/2). -/
noncomputable def lobIIICStabilityFn (z : ℂ) : ℂ := 2 / lobIIICDenom z

/-! ### A-Stability -/

/-- Key norm inequality: |D(z)|² ≥ 4 for Re(z) ≤ 0.
  The key decomposition: |D|² - 4 = x(x-2)·(x²-2x+4+2y²) + y⁴
  where x = Re(z), y = Im(z). For x ≤ 0, x(x-2) ≥ 0 since both factors ≤ 0. -/
theorem lobIIIC_normSq_denom_ge_four (z : ℂ) (hz : z.re ≤ 0) :
    4 ≤ Complex.normSq (lobIIICDenom z) := by
  set x := z.re
  set y := z.im
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  have hzz : (⟨x, y⟩ : ℂ) ^ 2 = ⟨x ^ 2 - y ^ 2, 2 * x * y⟩ := by
    rw [sq]; apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hz_eq]
  have hD : lobIIICDenom ⟨x, y⟩ = ⟨x ^ 2 - y ^ 2 - 2 * x + 2, 2 * x * y - 2 * y⟩ := by
    simp only [lobIIICDenom]; rw [hzz]
    apply Complex.ext <;> simp [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.add_im, Complex.sub_im, Complex.mul_im]
  rw [hD, Complex.normSq_mk]
  -- Need: 4 ≤ (x²-y²-2x+2)² + (2xy-2y)²
  -- Key: |D|² - 4 = x(x-2)(x²-2x+4+2y²) + y⁴
  suffices h : 0 ≤ (x ^ 2 - y ^ 2 - 2 * x + 2) ^ 2 + (2 * x * y - 2 * y) ^ 2 - 4 by linarith
  have key : (x ^ 2 - y ^ 2 - 2 * x + 2) ^ 2 + (2 * x * y - 2 * y) ^ 2 - 4 =
      x * (x - 2) * (x ^ 2 - 2 * x + 4 + 2 * y ^ 2) + y ^ 4 := by ring
  rw [key]
  have hx_neg : x ≤ 0 := hz
  have hx2_neg : x - 2 ≤ -2 := by linarith
  have hxx2 : 0 ≤ x * (x - 2) := by nlinarith
  have hrest : 0 < x ^ 2 - 2 * x + 4 + 2 * y ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y]
  nlinarith [sq_nonneg y, sq_nonneg (y ^ 2), mul_nonneg hxx2 (le_of_lt hrest)]

/-- The Lobatto IIIC denominator is nonzero for Re(z) ≤ 0. -/
theorem lobIIIC_denom_ne_zero (z : ℂ) (hz : z.re ≤ 0) :
    lobIIICDenom z ≠ 0 := by
  intro heq
  have h0 : Complex.normSq (lobIIICDenom z) = 0 := by rw [heq]; simp
  linarith [lobIIIC_normSq_denom_ge_four z hz]

/-- **A-stability of Lobatto IIIC 2-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  Reference: Iserles, Section 4.2. -/
theorem lobIIIC_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖lobIIICStabilityFn z‖ ≤ 1 := by
  have hD := lobIIIC_denom_ne_zero z hz
  have hD_pos : (0 : ℝ) < ‖lobIIICDenom z‖ := norm_pos_iff.mpr hD
  unfold lobIIICStabilityFn
  rw [norm_div]
  -- ‖2‖ / ‖D‖ ≤ 1 ⟺ ‖2‖ ≤ ‖D‖ ⟺ 2 ≤ ‖D‖
  rw [div_le_one hD_pos]
  -- Need: 2 ≤ ‖D(z)‖, i.e., 4 ≤ ‖D(z)‖²
  have h_sq : 4 ≤ ‖lobIIICDenom z‖ ^ 2 := by
    rw [Complex.sq_norm]
    exact lobIIIC_normSq_denom_ge_four z hz
  -- ‖2‖ = 2
  have h2 : ‖(2 : ℂ)‖ = 2 := by
    rw [Complex.norm_ofNat]
  rw [h2]
  nlinarith [sq_nonneg (‖lobIIICDenom z‖ - 2)]

/-! ### Stiff Decay and L-Stability -/

/-- **Lobatto IIIC has stiff decay**: R(x) → 0 as x → -∞.
  Since deg(numerator) = 0 < deg(denominator) = 2, R(z) → 0 along
  the negative real axis. -/
theorem lobIIIC_stiffDecay :
    Tendsto (fun x : ℝ => lobIIICStabilityFn (↑x)) atBot (nhds 0) := by
  apply NormedAddCommGroup.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [eventually_lt_atBot (min (-1) (-2/ε))] with x hx
  have hx_neg : x < -1 := by linarith [min_le_left (-1 : ℝ) (-2/ε)]
  have hx_large : -x > 2/ε := by
    have : -2/ε = -(2/ε) := by ring
    linarith [min_le_right (-1 : ℝ) (-2/ε)]
  have hD_pos : (0 : ℝ) < x ^ 2 - 2 * x + 2 := by nlinarith [sq_nonneg x]
  have hnx_pos : (0 : ℝ) < -x := by linarith
  simp only [lobIIICStabilityFn, lobIIICDenom]
  rw [show (↑x : ℂ) ^ 2 - 2 * (↑x : ℂ) + 2 = ((x ^ 2 - 2 * x + 2 : ℝ) : ℂ) from by
        push_cast; ring,
      show (2 : ℂ) / ((x ^ 2 - 2 * x + 2 : ℝ) : ℂ) =
        ((2 / (x ^ 2 - 2 * x + 2) : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (by norm_num : (0:ℝ) < 2) hD_pos)]
  -- x²-2x+2 ≥ -2x since x²+2 ≥ 0, so 2/(x²-2x+2) ≤ 2/(-2x) = 1/(-x)
  have hD_lower : -2 * x ≤ x ^ 2 - 2 * x + 2 := by nlinarith [sq_nonneg x]
  have h2x_pos : (0 : ℝ) < -2 * x := by linarith
  calc 2 / (x ^ 2 - 2 * x + 2)
      ≤ 2 / (-2 * x) := by
        apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) h2x_pos hD_lower
    _ = 1 / (-x) := by field_simp
    _ < ε := by
        rw [div_lt_iff₀ hnx_pos]
        have h1 : ε * (2 / ε) = 2 := by field_simp
        have h2 : ε * (-x) > ε * (2 / ε) := mul_lt_mul_of_pos_left hx_large hε
        linarith

/-- **Lobatto IIIC 2-stage is L-stable**: A-stable with stiff decay.
  Reference: Iserles, Section 4.2. -/
theorem lobIIIC_lStable :
    (∀ z : ℂ, z.re ≤ 0 → lobIIICDenom z ≠ 0 → ‖lobIIICStabilityFn z‖ ≤ 1) ∧
    Tendsto (fun x : ℝ => lobIIICStabilityFn (↑x)) atBot (nhds 0) :=
  ⟨fun z hz _ => lobIIIC_aStable z hz, lobIIIC_stiffDecay⟩

/-! ## Algebraic Stability -/

/-- **Lobatto IIIC 2-stage is algebraically stable.**
  The algebraic stability matrix M = (1/4)·[[1,-1],[-1,1]] is PSD,
  with quadratic form (v₁ - v₂)²/4 ≥ 0.
  Reference: Iserles, Definition 4.11. -/
theorem rkLobattoIIIC2_algStable : rkLobattoIIIC2.IsAlgStable where
  nonneg_weights := rkLobattoIIIC2_nonNegWeights
  posdef_M := by
    intro v; simp [ButcherTableau.algStabMatrix, rkLobattoIIIC2, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 - v 1)]
