import OpenMath.Collocation
import OpenMath.StiffEquations

/-!
# Radau IIA 3-Stage Method (Section 4.2)

The **Radau IIA 3-stage** method is a 3-stage implicit Runge–Kutta method based on
Radau quadrature on [0,1]. It achieves order 2s - 1 = 5 and is both A-stable and L-stable.

Butcher tableau:
```
  (4-√6)/10  | (88-7√6)/360    (296-169√6)/1800   (-2+3√6)/225
  (4+√6)/10  | (296+169√6)/1800  (88+7√6)/360     (-2-3√6)/225
  1           | (16-√6)/36       (16+√6)/36         1/9
  ------------|--------------------------------------------------
              | (16-√6)/36       (16+√6)/36         1/9
```

The stability function is the (2,3)-Padé approximant to eᶻ:
  R(z) = (1 + 2z/5 + z²/20) / (1 - 3z/5 + 3z²/20 - z³/60)

Since deg(numerator) = 2 < deg(denominator) = 3, R(z) → 0 as z → -∞,
giving stiff decay and hence L-stability.

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 4.2 and Chapter 2.
-/

open Finset Real Filter

/-! ## √6 Utilities -/

private theorem sqrt6_pos : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos_of_pos (by norm_num)
private theorem sqrt6_sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)
private theorem sqrt6_nonneg : (0 : ℝ) ≤ Real.sqrt 6 := le_of_lt sqrt6_pos
private theorem sqrt6_lt_three : Real.sqrt 6 < 3 := by
  nlinarith [sqrt6_sq, sq_nonneg (Real.sqrt 6 - 3)]
private theorem sqrt6_lt_four : Real.sqrt 6 < 4 := by linarith [sqrt6_lt_three]
private theorem sqrt6_gt_two : Real.sqrt 6 > 2 := by
  nlinarith [sqrt6_sq, sqrt6_nonneg]

/-! ## Butcher Tableau Definition -/

/-- **Radau IIA 3-stage** RK method.
  Collocation points: c₁ = (4-√6)/10, c₂ = (4+√6)/10, c₃ = 1.
  Reference: Iserles, Chapter 2 and 4; Hairer–Wanner, Table 5.6. -/
noncomputable def rkRadauIIA3 : ButcherTableau 3 where
  A := ![![(88 - 7 * Real.sqrt 6) / 360,
           (296 - 169 * Real.sqrt 6) / 1800,
           (-2 + 3 * Real.sqrt 6) / 225],
         ![(296 + 169 * Real.sqrt 6) / 1800,
           (88 + 7 * Real.sqrt 6) / 360,
           (-2 - 3 * Real.sqrt 6) / 225],
         ![(16 - Real.sqrt 6) / 36,
           (16 + Real.sqrt 6) / 36,
           1 / 9]]
  b := ![(16 - Real.sqrt 6) / 36, (16 + Real.sqrt 6) / 36, 1 / 9]
  c := ![(4 - Real.sqrt 6) / 10, (4 + Real.sqrt 6) / 10, 1]

/-! ## Basic Properties -/

/-- Radau IIA 3-stage is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkRadauIIA3_consistent : rkRadauIIA3.IsConsistent where
  weights_sum := by
    simp [rkRadauIIA3, Fin.sum_univ_three]; ring
  row_sum := by
    intro i; fin_cases i <;> (simp [rkRadauIIA3, Fin.sum_univ_three]; ring)

/-- Radau IIA 3-stage has non-negative weights. -/
theorem rkRadauIIA3_nonNegWeights : rkRadauIIA3.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkRadauIIA3]
  · linarith [sqrt6_lt_four]
  · positivity

/-- Radau IIA 3-stage is stiffly accurate: bᵢ = a_{3,i} for all i. -/
theorem rkRadauIIA3_stifflyAccurate :
    ∀ i : Fin 3, rkRadauIIA3.b i = rkRadauIIA3.A 2 i := by
  intro i; fin_cases i <;> simp [rkRadauIIA3]

/-- Radau IIA 3-stage is NOT explicit. -/
theorem rkRadauIIA3_not_explicit : ¬rkRadauIIA3.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkRadauIIA3] at this
  nlinarith [sqrt6_sq]

/-! ## Order via Simplifying Assumptions

The Radau IIA 3-stage method has order 2s−1 = 5. We prove this via the simplifying
assumptions B(5), C(3), D(1) using the theorem B(5)∧C(3)∧D(1) → order ≥ 5.
-/

/-- Radau IIA 3-stage satisfies B(5): Radau quadrature on [0,1] with s points
integrates polynomials of degree ≤ 2s−2 = 4 exactly. -/
theorem rkRadauIIA3_B5 : rkRadauIIA3.SatisfiesB 5 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkRadauIIA3, Fin.sum_univ_three] <;> nlinarith [sqrt6_sq]

/-- Radau IIA 3-stage satisfies C(3): collocation with s=3 nodes gives C(s). -/
theorem rkRadauIIA3_C3 : rkRadauIIA3.SatisfiesC 3 := by
  intro k hk1 hk2 i
  interval_cases k <;> fin_cases i <;>
    simp [rkRadauIIA3, Fin.sum_univ_three] <;> nlinarith [sqrt6_sq]

/-- Radau IIA 3-stage satisfies D(1): ∑ᵢ bᵢ aᵢⱼ = bⱼ(1−cⱼ). -/
theorem rkRadauIIA3_D1 : rkRadauIIA3.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; fin_cases j <;>
    simp [rkRadauIIA3, Fin.sum_univ_three] <;> nlinarith [sqrt6_sq]

/-- Radau IIA 3-stage has order at least 4 (via B(4)∧C(3)). -/
theorem rkRadauIIA3_order4 : rkRadauIIA3.HasOrderGe4 :=
  ButcherTableau.HasOrderGe4_of_B4_C3 _ (rkRadauIIA3_B5.mono (by omega)) rkRadauIIA3_C3

/-- **Radau IIA 3-stage has order at least 5** (= 2s−1 for s=3),
the maximum possible for a Radau method.
Proved via B(5) ∧ C(3) ∧ D(1). -/
theorem rkRadauIIA3_order5 : rkRadauIIA3.HasOrderGe5 :=
  ButcherTableau.HasOrderGe5_of_B5_C3_D1 _ rkRadauIIA3_B5 rkRadauIIA3_C3 rkRadauIIA3_D1

/-! ## Stability Function

The stability function of Radau IIA 3-stage is the (2,3)-Padé approximant to eᶻ.
Its coefficients are rational (no √6), making stability analysis cleaner.
-/

/-- Numerator of the Radau IIA 3-stage stability function: N(z) = 1 + 2z/5 + z²/20. -/
noncomputable def radauIIA3Num (z : ℂ) : ℂ := 1 + 2 * z / 5 + z ^ 2 / 20

/-- Denominator of the Radau IIA 3-stage stability function:
  D(z) = 1 - 3z/5 + 3z²/20 - z³/60. -/
noncomputable def radauIIA3Denom (z : ℂ) : ℂ := 1 - 3 * z / 5 + 3 * z ^ 2 / 20 - z ^ 3 / 60

/-- Radau IIA 3-stage stability function:
  R(z) = (1 + 2z/5 + z²/20) / (1 - 3z/5 + 3z²/20 - z³/60).
  This is the (2,3)-Padé approximant to eᶻ. -/
noncomputable def radauIIA3StabilityFn (z : ℂ) : ℂ :=
  radauIIA3Num z / radauIIA3Denom z

/-! ### A-Stability -/

/-- Key norm inequality: |N(z)|² ≤ |D(z)|² for Re(z) ≤ 0.
  The difference 3600(|D|²-|N|²) = y⁶ + x·g(x,y) where g ≤ 0 for x ≤ 0,
  since all polynomial-in-x coefficients are non-positive. -/
theorem radauIIA3_normSq_denom_ge_num (z : ℂ) (hz : z.re ≤ 0) :
    Complex.normSq (radauIIA3Num z) ≤ Complex.normSq (radauIIA3Denom z) := by
  suffices h : 0 ≤ Complex.normSq (radauIIA3Denom z) -
      Complex.normSq (radauIIA3Num z) by linarith
  set x := z.re
  set y := z.im
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  have hzz : (⟨x, y⟩ : ℂ) ^ 2 = ⟨x ^ 2 - y ^ 2, 2 * x * y⟩ := by
    rw [sq]; apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hzzz : (⟨x, y⟩ : ℂ) ^ 3 = ⟨x ^ 3 - 3 * x * y ^ 2, 3 * x ^ 2 * y - y ^ 3⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hzz]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hz_eq]
  have hN : radauIIA3Num ⟨x, y⟩ =
      ⟨1 + 2 * x / 5 + (x ^ 2 - y ^ 2) / 20, 2 * y / 5 + x * y / 10⟩ := by
    simp only [radauIIA3Num]; rw [hzz]
    apply Complex.ext <;> simp <;> ring
  have hD : radauIIA3Denom ⟨x, y⟩ =
      ⟨1 - 3 * x / 5 + 3 * x ^ 2 / 20 - 3 * y ^ 2 / 20 - x ^ 3 / 60 + x * y ^ 2 / 20,
       -3 * y / 5 + 3 * x * y / 10 - x ^ 2 * y / 20 + y ^ 3 / 60⟩ := by
    simp only [radauIIA3Denom]; rw [hzz, hzzz]
    apply Complex.ext <;> simp <;> ring
  rw [hN, hD, Complex.normSq_mk, Complex.normSq_mk]
  -- Key decomposition: 3600·(|D|²-|N|²) = y⁶ + x·g(x,y) where g ≤ 0 for x ≤ 0
  suffices hkey : 0 ≤ 3600 *
      ((1 - 3 * x / 5 + 3 * x ^ 2 / 20 - 3 * y ^ 2 / 20 -
        x ^ 3 / 60 + x * y ^ 2 / 20) ^ 2 +
       (-3 * y / 5 + 3 * x * y / 10 - x ^ 2 * y / 20 + y ^ 3 / 60) ^ 2 -
       ((1 + 2 * x / 5 + (x ^ 2 - y ^ 2) / 20) ^ 2 +
        (2 * y / 5 + x * y / 10) ^ 2)) by linarith
  have key : 3600 *
      ((1 - 3 * x / 5 + 3 * x ^ 2 / 20 - 3 * y ^ 2 / 20 -
        x ^ 3 / 60 + x * y ^ 2 / 20) ^ 2 +
       (-3 * y / 5 + 3 * x * y / 10 - x ^ 2 * y / 20 + y ^ 3 / 60) ^ 2 -
       ((1 + 2 * x / 5 + (x ^ 2 - y ^ 2) / 20) ^ 2 +
        (2 * y / 5 + x * y / 10) ^ 2)) =
      y ^ 6 + x * (x ^ 5 - 18 * x ^ 4 + 144 * x ^ 3 - 912 * x ^ 2 +
        1440 * x - 7200 + y ^ 2 * (3 * x ^ 3 - 36 * x ^ 2 + 144 * x - 432) +
        y ^ 4 * (3 * x - 18)) := by ring
  rw [key]
  have hp : x ^ 5 - 18 * x ^ 4 + 144 * x ^ 3 - 912 * x ^ 2 + 1440 * x - 7200 ≤ 0 := by
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), sq_nonneg (x * x)]
  have hq : 3 * x ^ 3 - 36 * x ^ 2 + 144 * x - 432 ≤ 0 := by
    nlinarith [sq_nonneg x]
  have hr : 3 * x - 18 ≤ 0 := by linarith
  have h_sum_le : x ^ 5 - 18 * x ^ 4 + 144 * x ^ 3 - 912 * x ^ 2 + 1440 * x - 7200 +
      y ^ 2 * (3 * x ^ 3 - 36 * x ^ 2 + 144 * x - 432) +
      y ^ 4 * (3 * x - 18) ≤ 0 := by nlinarith [sq_nonneg y, sq_nonneg (y ^ 2)]
  nlinarith [sq_nonneg y, sq_nonneg (y ^ 2), sq_nonneg (y ^ 3),
             mul_nonpos_of_nonpos_of_nonneg hz (neg_nonneg.mpr h_sum_le)]

/-- The Radau IIA 3-stage denominator is nonzero for Re(z) ≤ 0. -/
theorem radauIIA3_denom_ne_zero (z : ℂ) (hz : z.re ≤ 0) :
    radauIIA3Denom z ≠ 0 := by
  intro heq
  have h0 : Complex.normSq (radauIIA3Denom z) = 0 := by rw [heq]; simp
  have h1 : Complex.normSq (radauIIA3Num z) ≤ 0 := by
    linarith [radauIIA3_normSq_denom_ge_num z hz]
  have hN0 : radauIIA3Num z = 0 :=
    Complex.normSq_eq_zero.mp (le_antisymm h1 (Complex.normSq_nonneg _))
  -- N(z) = 0 means z² + 8z + 20 = 0
  have hN20 : z ^ 2 + 8 * z + 20 = 0 := by
    have : 20 * radauIIA3Num z = z ^ 2 + 8 * z + 20 := by
      simp [radauIIA3Num]; ring
    rw [hN0, mul_zero] at this; exact this.symm
  -- Substitute into D: when z²+8z+20=0, we get 30·D(z) = -140 - 76z
  have hD30 : 30 * radauIIA3Denom z = -140 - 76 * z := by
    have h30 : 30 * radauIIA3Denom z = 30 - 18 * z + (9 : ℂ) / 2 * z ^ 2 -
        (1 : ℂ) / 2 * z ^ 3 := by
      simp [radauIIA3Denom]; ring
    have hz3 : z ^ 3 = 44 * z + 160 := by
      have h1 : z ^ 3 + 8 * z ^ 2 + 20 * z = 0 := by linear_combination z * hN20
      linear_combination h1 - 8 * hN20
    have hz2 : z ^ 2 = -8 * z - 20 := by linear_combination hN20
    rw [h30, hz2, hz3]; ring
  -- D(z) = 0 implies 76z = -140
  rw [heq, mul_zero] at hD30
  have h76z : 76 * z = -140 := by linear_combination hD30
  -- Substitute back into z²+8z+20=0 (multiply by 76² first)
  have : (76 * z) ^ 2 + 8 * 76 * (76 * z) + 20 * 76 ^ 2 = 0 := by
    linear_combination 76 ^ 2 * hN20
  rw [h76z] at this; norm_num at this

/-- **A-stability of Radau IIA 3-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  Reference: Iserles, Section 4.2. -/
theorem radauIIA3_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖radauIIA3StabilityFn z‖ ≤ 1 := by
  have hD := radauIIA3_denom_ne_zero z hz
  have hD_pos : (0 : ℝ) < ‖radauIIA3Denom z‖ := norm_pos_iff.mpr hD
  unfold radauIIA3StabilityFn
  rw [norm_div, div_le_one hD_pos]
  have h_sq_le : ‖radauIIA3Num z‖ ^ 2 ≤ ‖radauIIA3Denom z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    exact radauIIA3_normSq_denom_ge_num z hz
  by_contra hlt; push_neg at hlt
  nlinarith [norm_nonneg (radauIIA3Num z), norm_nonneg (radauIIA3Denom z),
             mul_pos (by linarith : (0 : ℝ) < ‖radauIIA3Num z‖ - ‖radauIIA3Denom z‖)
                     (by linarith [norm_nonneg (radauIIA3Num z)] :
                       (0 : ℝ) < ‖radauIIA3Num z‖ + ‖radauIIA3Denom z‖)]

/-! ### Stiff Decay and L-Stability -/

/-- **Radau IIA 3-stage has stiff decay**: R(x) → 0 as x → -∞.
  Since deg(N) = 2 < deg(D) = 3, R(z) → 0 along the negative real axis. -/
theorem radauIIA3_stiffDecay :
    Tendsto (fun x : ℝ => radauIIA3StabilityFn (↑x)) atBot (nhds 0) := by
  apply NormedAddCommGroup.tendsto_nhds_zero.mpr
  intro ε hε
  -- N(x) ≤ x²/20 for x ≤ -6, D(x) ≥ -x³/60, so |R(x)| ≤ 3/(-x)
  filter_upwards [eventually_lt_atBot (min (-6) (-3/ε))] with x hx
  have hx_neg6 : x < -6 := by linarith [min_le_left (-6 : ℝ) (-3/ε)]
  have hx_large : -x > 3 / ε := by
    have h1 : x < -3 / ε := lt_of_lt_of_le hx (min_le_right _ _)
    have : -(-3 / ε) = 3 / ε := by ring
    linarith
  have hD_pos : (0 : ℝ) < 1 - 3 * x / 5 + 3 * x ^ 2 / 20 - x ^ 3 / 60 := by
    nlinarith [sq_nonneg x, sq_nonneg (x + 6)]
  have hnx_pos : (0 : ℝ) < -x := by linarith
  simp only [radauIIA3StabilityFn, radauIIA3Num, radauIIA3Denom]
  rw [show (1 : ℂ) + 2 * (↑x : ℂ) / 5 + (↑x : ℂ) ^ 2 / 20 =
        ((1 + 2 * x / 5 + x ^ 2 / 20 : ℝ) : ℂ) from by push_cast; ring,
      show (1 : ℂ) - 3 * (↑x : ℂ) / 5 + 3 * (↑x : ℂ) ^ 2 / 20 - (↑x : ℂ) ^ 3 / 60 =
        ((1 - 3 * x / 5 + 3 * x ^ 2 / 20 - x ^ 3 / 60 : ℝ) : ℂ) from by push_cast; ring,
      show ((1 + 2 * x / 5 + x ^ 2 / 20 : ℝ) : ℂ) /
        ((1 - 3 * x / 5 + 3 * x ^ 2 / 20 - x ^ 3 / 60 : ℝ) : ℂ) =
        (((1 + 2 * x / 5 + x ^ 2 / 20) /
          (1 - 3 * x / 5 + 3 * x ^ 2 / 20 - x ^ 3 / 60) : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  -- N(x) = (x+4)²/20 + 1/5 > 0 always, so |N(x)| = N(x)
  have hN_pos : 0 < 1 + 2 * x / 5 + x ^ 2 / 20 := by nlinarith [sq_nonneg (x + 4)]
  -- N(x) ≤ x²/20 for x ≤ -6 (since 1+2x/5 ≤ 0)
  have hN_bound : 1 + 2 * x / 5 + x ^ 2 / 20 ≤ x ^ 2 / 20 := by nlinarith
  -- D(x) ≥ -x³/60 (the remaining terms are positive)
  have hD_lower : -x ^ 3 / 60 ≤ 1 - 3 * x / 5 + 3 * x ^ 2 / 20 - x ^ 3 / 60 := by
    nlinarith [sq_nonneg x, sq_nonneg (x + 6)]
  have hx3_neg : x ^ 3 < 0 := by nlinarith [sq_nonneg x]
  have hx3_60_pos : (0 : ℝ) < -x ^ 3 / 60 := by nlinarith
  calc |(1 + 2 * x / 5 + x ^ 2 / 20) /
        (1 - 3 * x / 5 + 3 * x ^ 2 / 20 - x ^ 3 / 60)|
      = (1 + 2 * x / 5 + x ^ 2 / 20) /
        (1 - 3 * x / 5 + 3 * x ^ 2 / 20 - x ^ 3 / 60) := by
        rw [abs_of_pos (div_pos hN_pos hD_pos)]
    _ ≤ (x ^ 2 / 20) / (1 - 3 * x / 5 + 3 * x ^ 2 / 20 - x ^ 3 / 60) := by
        apply div_le_div_of_nonneg_right hN_bound (by linarith)
    _ ≤ (x ^ 2 / 20) / (-x ^ 3 / 60) := by
        apply div_le_div_of_nonneg_left (by positivity) hx3_60_pos hD_lower
    _ = 3 / (-x) := by field_simp; nlinarith [sq_nonneg x]
    _ < ε := by
        rw [div_lt_iff₀ hnx_pos]
        calc 3 = ε * (3 / ε) := by field_simp
          _ < ε * (-x) := by apply mul_lt_mul_of_pos_left hx_large hε

/-- **Radau IIA 3-stage is L-stable**: A-stable with stiff decay.
  Reference: Iserles, Section 4.2. -/
theorem radauIIA3_lStable :
    (∀ z : ℂ, z.re ≤ 0 → radauIIA3Denom z ≠ 0 → ‖radauIIA3StabilityFn z‖ ≤ 1) ∧
    Tendsto (fun x : ℝ => radauIIA3StabilityFn (↑x)) atBot (nhds 0) :=
  ⟨fun z hz _ => radauIIA3_aStable z hz, radauIIA3_stiffDecay⟩

/-! ## Algebraic Stability -/

/-- Radau IIA 3-stage is algebraically stable.
  The algebraic stability matrix M_{ij} = b_i a_{ij} + b_j a_{ji} - b_i b_j is PSD. -/
theorem rkRadauIIA3_algStable : rkRadauIIA3.IsAlgStable where
  nonneg_weights := rkRadauIIA3_nonNegWeights
  posdef_M := by
    intro v; simp [ButcherTableau.algStabMatrix, rkRadauIIA3, Fin.sum_univ_three]
    -- The algebraic stability matrix M is rank 1 with eigenvalue 18 (trace):
    -- all 2×2 minors vanish since (7-2√6)(7+2√6) = 49-24 = 25.
    -- Key identity: 324(7-2√6) · Q = ((7-2√6)v₀ - 5v₁ + 2(√6-1)v₂)²
    -- Since (7-2√6) > 0 and the RHS is a perfect square, Q ≥ 0.
    have hs := sqrt6_sq
    have h7 : (0 : ℝ) < 7 - 2 * Real.sqrt 6 := by nlinarith [hs, sqrt6_lt_three]
    norm_num
    ring_nf; rw [hs]
    nlinarith [h7, sq_nonneg ((7 - 2 * Real.sqrt 6) * v 0 - 5 * v 1 + 2 * (Real.sqrt 6 - 1) * v 2),
               sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2),
               sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2), sq_nonneg (v 1 - v 2),
               sq_nonneg ((v 0 - v 1) * Real.sqrt 6),
               sq_nonneg ((v 0 - v 2) * Real.sqrt 6),
               sq_nonneg ((v 1 - v 2) * Real.sqrt 6)]

/-! ## Stage Order and Quadrature Order Bounds

Radau IIA 3-stage has stage order = s = 3 (C(3) but NOT C(4)) and
quadrature order = 2s−1 = 5 (B(5) but NOT B(6)).
These are the maximal values for s-stage Radau methods. -/

/-- Radau IIA 3-stage does NOT satisfy C(4): the stage order is exactly s = 3.
  For Radau collocation with s nodes, C(s) holds but C(s+1) is overdetermined. -/
theorem rkRadauIIA3_not_C4 : ¬rkRadauIIA3.SatisfiesC 4 := by
  intro hC
  have h := hC 4 (by omega) le_rfl 1
  simp [rkRadauIIA3, Fin.sum_univ_three] at h
  nlinarith [sqrt6_sq]

/-- Radau IIA 3-stage does NOT satisfy B(6): the quadrature order is exactly 2s−1 = 5.
  The s-point Radau quadrature integrates polynomials of degree ≤ 2s−2 = 4 exactly. -/
theorem rkRadauIIA3_not_B6 : ¬rkRadauIIA3.SatisfiesB 6 := by
  intro hB
  have h := hB 6 (by omega) le_rfl
  simp [rkRadauIIA3, Fin.sum_univ_three] at h
  nlinarith [sqrt6_sq]

/-- Radau IIA 3-stage satisfies D(2): the maximal D condition exceeds D(1). -/
theorem rkRadauIIA3_D2 : rkRadauIIA3.SatisfiesD 2 := by
  intro k hk1 hk2 j
  interval_cases k <;> fin_cases j <;>
    simp [rkRadauIIA3, Fin.sum_univ_three] <;> nlinarith [sqrt6_sq]
