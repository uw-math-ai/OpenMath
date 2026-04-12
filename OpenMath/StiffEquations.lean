import OpenMath.RungeKutta

/-!
# Chapter 4: Stiff Equations and L-stability

Stability concepts beyond A-stability for stiff ODEs.

## L-stability (Section 4.2)

An A-stable method is **L-stable** if its stability function R(z) → 0 as Re(z) → -∞.

Key results:
* Backward Euler is L-stable: R(z) = 1/(1-z) → 0.
* Implicit midpoint is NOT L-stable: R(z) → -1.
* Gauss–Legendre 2-stage is NOT L-stable: R(z) → 1.
* **Radau IIA 2-stage is L-stable**: R(z) = (1+z/3)/(1-2z/3+z²/6) → 0.

## Algebraic Stability (Section 4.4)

A Runge–Kutta method is **algebraically stable** if b_i ≥ 0 and the matrix
M_{ij} = b_i·a_{ij} + b_j·a_{ji} - b_i·b_j is positive semidefinite.

Reference: Iserles, Chapter 4.
-/

open Finset Real Filter

namespace ButcherTableau

/-- A 1-stage RK method has **stiff decay** if R(z) → 0 as z → -∞ along the real axis. -/
def HasStiffDecay1 (t : ButcherTableau 1) : Prop :=
  Tendsto (fun x : ℝ => t.stabilityFn1 (↑x)) atBot (nhds 0)

/-- A 1-stage RK method is **L-stable** if it is A-stable and has stiff decay.
  Reference: Iserles, Definition 4.3. -/
def IsLStable1 (t : ButcherTableau 1) : Prop :=
  t.IsAStable1 ∧ t.HasStiffDecay1

end ButcherTableau

/-! ### Backward Euler: L-stable -/

/-- Backward Euler has stiff decay: R(x) = 1/(1-x) → 0 as x → -∞. -/
theorem rkImplicitEuler_stiffDecay : rkImplicitEuler.HasStiffDecay1 := by
  simp only [ButcherTableau.HasStiffDecay1]
  apply NormedAddCommGroup.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [eventually_lt_atBot (min 0 (-1/ε))] with x hx
  have hx_neg : x < 0 := by linarith [min_le_left (0 : ℝ) (-1/ε)]
  simp only [ButcherTableau.stabilityFn1, rkImplicitEuler, Matrix.cons_val_zero]
  have h1mx_pos : (0 : ℝ) < 1 - x := by linarith
  -- Simplify: (1 + x*0) / (1 - x*1) = 1/(1-x)
  rw [show (1 : ℂ) + (↑x : ℂ) * ((↑(1 : ℝ) : ℂ) - ↑(1 : ℝ)) = 1 from by push_cast; ring,
      show (1 : ℂ) - (↑x : ℂ) * (↑(1 : ℝ) : ℂ) = ((1 - x : ℝ) : ℂ) from by push_cast; ring,
      show (1 : ℂ) / ((1 - x : ℝ) : ℂ) = ((1 / (1 - x) : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos one_pos h1mx_pos),
      div_lt_iff₀ h1mx_pos]
  -- Need: 1 < ε * (1 - x)
  have key : ε * (1 - x) > ε * (1/ε) := by
    apply mul_lt_mul_of_pos_left _ hε
    have : -1/ε = -(1/ε) := by ring
    linarith [min_le_right (0 : ℝ) (-1/ε)]
  simp [ne_of_gt hε] at key; linarith

/-- **Backward Euler is L-stable.** Reference: Iserles, Example 4.4. -/
theorem rkImplicitEuler_lStable : rkImplicitEuler.IsLStable1 :=
  ⟨rkImplicitEuler_aStable, rkImplicitEuler_stiffDecay⟩

/-! ### Implicit Midpoint: NOT L-stable -/

/-- The implicit midpoint stability function tends to -1 as x → -∞. -/
theorem rkImplicitMidpoint_stabilityFn1_tendsto :
    Tendsto (fun x : ℝ => rkImplicitMidpoint.stabilityFn1 (↑x)) atBot (nhds (-1 : ℂ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_lt_atBot (min 0 (2 - 4/ε))] with x hx
  have hx_neg : x < 0 := by linarith [min_le_left (0 : ℝ) (2 - 4/ε)]
  have hx_bound : 2 - x > 4/ε := by linarith [min_le_right (0 : ℝ) (2 - 4/ε)]
  have h1mx2 : (0 : ℝ) < 1 - x / 2 := by linarith
  simp only [ButcherTableau.stabilityFn1, rkImplicitMidpoint, Matrix.cons_val_zero]
  rw [dist_comm, dist_eq_norm]
  -- R(x) = (1+x/2)/(1-x/2), R(x) - (-1) = 2/(1-x/2)
  -- ‖R(x) + 1‖ = 2/(1-x/2) = 4/(2-x) < ε
  have h_ne : (1 : ℂ) - (↑x : ℂ) * ↑((1 : ℝ) / 2) ≠ 0 := by
    rw [show (1 : ℂ) - (↑x : ℂ) * ↑((1 : ℝ) / 2) = ((1 - x/2 : ℝ) : ℂ) from by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt h1mx2)
  -- Use field_simp after establishing non-vanishing
  rw [show (-1 : ℂ) - ((1 : ℂ) + (↑x : ℂ) * ((↑(1 : ℝ) : ℂ) - ↑((1 : ℝ) / 2))) /
        ((1 : ℂ) - (↑x : ℂ) * (↑((1 : ℝ) / 2) : ℂ)) =
      ((-2 / (1 - x / 2) : ℝ) : ℂ) from by
    rw [show (1 : ℂ) - (↑x : ℂ) * ↑((1 : ℝ) / 2) = ((1 - x/2 : ℝ) : ℂ) from by push_cast; ring,
        show (1 : ℂ) + (↑x : ℂ) * ((↑(1 : ℝ) : ℂ) - ↑((1 : ℝ) / 2)) = ((1 + x/2 : ℝ) : ℂ) from by
          push_cast; ring,
        show ((1 + x / 2 : ℝ) : ℂ) / ((1 - x / 2 : ℝ) : ℂ) =
          (((1 + x / 2) / (1 - x / 2) : ℝ) : ℂ) from by push_cast; ring,
        show (-1 : ℂ) - (((1 + x / 2) / (1 - x / 2) : ℝ) : ℂ) =
          ((-1 - (1 + x / 2) / (1 - x / 2) : ℝ) : ℂ) from by push_cast; ring,
        show ((-1 - (1 + x / 2) / (1 - x / 2) : ℝ) : ℂ) =
          ((-2 / (1 - x / 2) : ℝ) : ℂ) from by
          congr 1; rw [sub_div' (ne_of_gt h1mx2)]; congr 1; ring],
      Complex.norm_real, Real.norm_eq_abs, abs_div,
      show |(-(2 : ℝ))| = 2 from by norm_num,
      abs_of_pos h1mx2, div_lt_iff₀ h1mx2]
  -- Need: 2 < ε * (1 - x/2) from 2 - x > 4/ε
  have : ε * (1 - x / 2) > ε * (2/ε) := by
    apply mul_lt_mul_of_pos_left _ hε
    rw [show 2/ε = (4/ε) / 2 from by ring]
    linarith
  rw [show ε * (2 / ε) = 2 from by field_simp] at this; linarith

/-- Implicit midpoint does NOT have stiff decay: R(z) → -1 ≠ 0. -/
theorem rkImplicitMidpoint_not_stiffDecay : ¬rkImplicitMidpoint.HasStiffDecay1 := by
  intro h_decay
  simp only [ButcherTableau.HasStiffDecay1] at h_decay
  exact absurd (tendsto_nhds_unique h_decay rkImplicitMidpoint_stabilityFn1_tendsto)
    (by norm_num)

/-- Implicit midpoint is NOT L-stable. -/
theorem rkImplicitMidpoint_not_lStable : ¬rkImplicitMidpoint.IsLStable1 := by
  intro ⟨_, h⟩; exact rkImplicitMidpoint_not_stiffDecay h

/-! ### Gauss–Legendre 2-stage: NOT L-stable -/

/-- The GL2 stability function tends to 1 as z → -∞ along the real axis. -/
theorem gl2StabilityFn_tendsto_one :
    Tendsto (fun x : ℝ => gl2StabilityFn (↑x)) atBot (nhds (1 : ℂ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_lt_atBot (min (-12) (-24/ε - 1))] with x hx
  have hx_neg : x < -12 := by linarith [min_le_left (-12 : ℝ) (-24/ε - 1)]
  have hx_large : -x > 24/ε := by
    have : -24/ε - 1 = -(24/ε) - 1 := by ring
    linarith [min_le_right (-12 : ℝ) (-24/ε - 1)]
  have hD_pos : (0 : ℝ) < 1 - x/2 + x^2/12 := by nlinarith [sq_nonneg x]
  have hD_ne : gl2Denom (↑x) ≠ 0 := by
    rw [show gl2Denom (↑x) = ((1 - x/2 + x^2/12 : ℝ) : ℂ) from by simp [gl2Denom]]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hD_pos)
  rw [dist_comm, dist_eq_norm]
  -- 1 - R(x) = -x/D(x), rewrite to real
  rw [show (1 : ℂ) - gl2StabilityFn (↑x) =
      (((-x) / (1 - x/2 + x^2/12) : ℝ) : ℂ) from by
    simp only [gl2StabilityFn]
    rw [show gl2Denom (↑x) = ((1 - x/2 + x^2/12 : ℝ) : ℂ) from by simp [gl2Denom],
        show gl2Num (↑x) = ((1 + x/2 + x^2/12 : ℝ) : ℂ) from by simp [gl2Num]]
    have hDc : ((1 - x / 2 + x ^ 2 / 12 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hD_pos)
    rw [one_sub_div hDc]; push_cast; congr 1; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hD_pos,
      abs_of_pos (show (0 : ℝ) < -x by linarith)]
  have hD_lower : x^2/24 ≤ 1 - x/2 + x^2/12 := by nlinarith [sq_nonneg x]
  calc (-x) / (1 - x/2 + x^2/12)
      ≤ (-x) / (x^2/24) := by
        apply div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ -x)
          (show (0:ℝ) < x^2/24 by nlinarith [sq_nonneg x]) hD_lower
    _ = 24 / (-x) := by field_simp
    _ < ε := by
        rw [div_lt_iff₀ (show (0:ℝ) < -x by linarith)]
        have h24e : ε * (24 / ε) = 24 := by field_simp
        nlinarith

/-- GL2 does NOT have stiff decay: R(z) → 1 ≠ 0 as z → -∞. -/
theorem gl2_not_stiffDecay :
    ¬Tendsto (fun x : ℝ => gl2StabilityFn (↑x)) atBot (nhds 0) := by
  intro h_zero
  exact absurd (tendsto_nhds_unique h_zero gl2StabilityFn_tendsto_one) (by norm_num)

/-! ## Algebraic Stability -/

namespace ButcherTableau

variable {s : ℕ}

/-- The **algebraic stability matrix** M_{ij} = b_i·a_{ij} + b_j·a_{ji} - b_i·b_j. -/
noncomputable def algStabMatrix (t : ButcherTableau s) (i j : Fin s) : ℝ :=
  t.b i * t.A i j + t.b j * t.A j i - t.b i * t.b j

/-- The algebraic stability matrix is symmetric. -/
theorem algStabMatrix_symm (t : ButcherTableau s) (i j : Fin s) :
    t.algStabMatrix i j = t.algStabMatrix j i := by
  simp only [algStabMatrix]; ring

/-- A RK method has **non-negative weights** if b_i ≥ 0 for all i. -/
def HasNonNegWeights (t : ButcherTableau s) : Prop :=
  ∀ i : Fin s, 0 ≤ t.b i

/-- A RK method is **algebraically stable** if b_i ≥ 0 and the matrix
  M_{ij} = b_i·a_{ij} + b_j·a_{ji} - b_i·b_j is positive semidefinite.
  Reference: Iserles, Definition 4.11. -/
structure IsAlgStable (t : ButcherTableau s) : Prop where
  nonneg_weights : t.HasNonNegWeights
  posdef_M : ∀ v : Fin s → ℝ,
    0 ≤ ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j

end ButcherTableau

/-- Backward Euler is algebraically stable. -/
theorem rkImplicitEuler_algStable : rkImplicitEuler.IsAlgStable where
  nonneg_weights := by intro i; fin_cases i; simp [rkImplicitEuler]
  posdef_M := by
    intro v; simp [ButcherTableau.algStabMatrix, rkImplicitEuler]
    nlinarith [sq_nonneg (v 0)]

/-- Implicit midpoint is algebraically stable. -/
theorem rkImplicitMidpoint_algStable : rkImplicitMidpoint.IsAlgStable where
  nonneg_weights := by intro i; fin_cases i; simp [rkImplicitMidpoint]
  posdef_M := by
    intro v; simp [ButcherTableau.algStabMatrix, rkImplicitMidpoint]
    nlinarith [sq_nonneg (v 0)]

/-- GL2 has non-negative weights. -/
theorem rkGaussLegendre2_nonNegWeights : rkGaussLegendre2.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkGaussLegendre2]

/-- The GL2 algebraic stability matrix is identically zero. -/
theorem rkGaussLegendre2_algStabMatrix_zero (i j : Fin 2) :
    rkGaussLegendre2.algStabMatrix i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [ButcherTableau.algStabMatrix, rkGaussLegendre2] <;> ring

/-- **GL2 is algebraically stable.** Reference: Iserles, Thm 4.14. -/
theorem rkGaussLegendre2_algStable : rkGaussLegendre2.IsAlgStable where
  nonneg_weights := rkGaussLegendre2_nonNegWeights
  posdef_M := by
    intro v; simp only [rkGaussLegendre2_algStabMatrix_zero, mul_zero]; simp

/-- Forward Euler is NOT algebraically stable. -/
theorem rkEuler_not_algStable : ¬rkEuler.IsAlgStable := by
  intro ⟨_, hM⟩
  have h := hM (fun _ => 1)
  simp [ButcherTableau.algStabMatrix, rkEuler] at h
  linarith

/-! ## Radau IIA 2-Stage Method

The Radau IIA 2-stage method is a 2-stage implicit Runge–Kutta method based on
Radau quadrature. It achieves order 2s - 1 = 3 and is both A-stable and L-stable.

Butcher tableau:
```
  1/3 | 5/12   -1/12
   1  | 3/4     1/4
  ----|---------------
      | 3/4     1/4
```

The stability function is R(z) = (1 + z/3) / (1 - 2z/3 + z²/6), the (1,2)-Padé
approximant to eᶻ. Since deg(numerator) < deg(denominator), R(z) → 0 as z → -∞,
giving stiff decay and hence L-stability.

Reference: Iserles, Section 4.2 (L-stability) and Section 2.2 (implicit RK).
-/

/-- **Radau IIA 2-stage** RK method.
  Collocation points: c₁ = 1/3, c₂ = 1 (Radau quadrature on [0,1]).
  Reference: Iserles, Chapter 2 and 4. -/
noncomputable def rkRadauIIA2 : ButcherTableau 2 where
  A := ![![5/12, -1/12], ![3/4, 1/4]]
  b := ![3/4, 1/4]
  c := ![1/3, 1]

/-- Radau IIA 2-stage is consistent. -/
theorem rkRadauIIA2_consistent : rkRadauIIA2.IsConsistent where
  weights_sum := by simp [rkRadauIIA2, Fin.sum_univ_two]; norm_num
  row_sum := by
    intro i; fin_cases i <;> simp [rkRadauIIA2, Fin.sum_univ_two] <;> norm_num

/-- Radau IIA 2-stage has order at least 3. -/
theorem rkRadauIIA2_order3 : rkRadauIIA2.HasOrderGe3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ButcherTableau.order1, rkRadauIIA2, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order2, rkRadauIIA2, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order3a, rkRadauIIA2, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order3b, rkRadauIIA2, Fin.sum_univ_two]; norm_num

/-- Radau IIA 2-stage does NOT have order 4: ∑ bᵢ cᵢ³ = 5/18 ≠ 1/4. -/
theorem rkRadauIIA2_not_order4 : ¬rkRadauIIA2.HasOrderGe4 := by
  intro ⟨_, _, _, _, h4a, _⟩
  simp [ButcherTableau.order4a, rkRadauIIA2, Fin.sum_univ_two] at h4a

/-- Radau IIA has non-negative weights. -/
theorem rkRadauIIA2_nonNegWeights : rkRadauIIA2.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkRadauIIA2] <;> norm_num

/-- Radau IIA is algebraically stable.
  M = (1/16)·[[1, -1], [-1, 1]] is PSD. -/
theorem rkRadauIIA2_algStable : rkRadauIIA2.IsAlgStable where
  nonneg_weights := rkRadauIIA2_nonNegWeights
  posdef_M := by
    intro v; simp [ButcherTableau.algStabMatrix, rkRadauIIA2, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 - v 1)]

/-! ### Radau IIA Stability Function -/

/-- Numerator of the Radau IIA 2-stage stability function: N(z) = 1 + z/3. -/
noncomputable def radauIIA2Num (z : ℂ) : ℂ := 1 + z / 3

/-- Denominator of the Radau IIA 2-stage stability function:
  D(z) = 1 - 2z/3 + z²/6. -/
noncomputable def radauIIA2Denom (z : ℂ) : ℂ := 1 - 2 * z / 3 + z ^ 2 / 6

/-- Radau IIA 2-stage stability function:
  R(z) = (1 + z/3) / (1 - 2z/3 + z²/6).
  This is the (1,2)-Padé approximant to eᶻ. -/
noncomputable def radauIIA2StabilityFn (z : ℂ) : ℂ :=
  radauIIA2Num z / radauIIA2Denom z

/-! ### Radau IIA A-Stability -/

/-- Key norm inequality: |N(z)|² ≤ |D(z)|² for Re(z) ≤ 0.
  |D|² - |N|² = (-2x)(9 - 3x + x² + y²)/9 + (x² + y²)²/36 ≥ 0. -/
theorem radauIIA2_normSq_denom_ge_num (z : ℂ) (hz : z.re ≤ 0) :
    Complex.normSq (radauIIA2Num z) ≤ Complex.normSq (radauIIA2Denom z) := by
  suffices h : 0 ≤ Complex.normSq (radauIIA2Denom z) -
      Complex.normSq (radauIIA2Num z) by linarith
  set x := z.re
  set y := z.im
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  have hzz : (⟨x, y⟩ : ℂ) ^ 2 = ⟨x^2 - y^2, 2*x*y⟩ := by
    rw [sq]; apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hz_eq]
  -- Reduce N and D to explicit ⟨re, im⟩ form
  have hN : radauIIA2Num ⟨x, y⟩ = ⟨1 + x/3, y/3⟩ := by
    simp only [radauIIA2Num]
    apply Complex.ext <;> simp
  have hD : radauIIA2Denom ⟨x, y⟩ = ⟨1 - 2*x/3 + (x^2 - y^2)/6, -2*y/3 + x*y/3⟩ := by
    simp only [radauIIA2Denom]; rw [hzz]
    apply Complex.ext <;> simp <;> ring
  rw [hN, hD, Complex.normSq_mk, Complex.normSq_mk]
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x*y),
             sq_nonneg (x*x + y*y), sq_nonneg (x + y)]

/-- The Radau IIA denominator is nonzero for Re(z) ≤ 0. -/
theorem radauIIA2_denom_ne_zero (z : ℂ) (hz : z.re ≤ 0) :
    radauIIA2Denom z ≠ 0 := by
  intro heq
  have h0 : Complex.normSq (radauIIA2Denom z) = 0 := by rw [heq]; simp
  have h1 : Complex.normSq (radauIIA2Num z) ≤ 0 := by
    linarith [radauIIA2_normSq_denom_ge_num z hz]
  have hN0 : radauIIA2Num z = 0 :=
    Complex.normSq_eq_zero.mp (le_antisymm h1 (Complex.normSq_nonneg _))
  -- N(z) = 0 means z = -3, but D(-3) = 9/2 ≠ 0
  have hz3 : z = -3 := by
    simp only [radauIIA2Num] at hN0
    have : z = -(3 : ℂ) := by linear_combination 3 * hN0
    exact_mod_cast this
  rw [hz3] at heq; simp only [radauIIA2Denom] at heq; norm_num at heq

/-- **A-stability of Radau IIA 2-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  Reference: Iserles, Section 4.2. -/
theorem radauIIA2_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖radauIIA2StabilityFn z‖ ≤ 1 := by
  have hD := radauIIA2_denom_ne_zero z hz
  have hD_pos : (0 : ℝ) < ‖radauIIA2Denom z‖ := norm_pos_iff.mpr hD
  unfold radauIIA2StabilityFn
  rw [norm_div, div_le_one hD_pos]
  have h_sq_le : ‖radauIIA2Num z‖ ^ 2 ≤ ‖radauIIA2Denom z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    exact radauIIA2_normSq_denom_ge_num z hz
  by_contra hlt; push_neg at hlt
  nlinarith [norm_nonneg (radauIIA2Num z), norm_nonneg (radauIIA2Denom z),
             mul_pos (by linarith : (0 : ℝ) < ‖radauIIA2Num z‖ - ‖radauIIA2Denom z‖)
                     (by linarith [norm_nonneg (radauIIA2Num z)] :
                       (0 : ℝ) < ‖radauIIA2Num z‖ + ‖radauIIA2Denom z‖)]

/-! ### Radau IIA Stiff Decay and L-Stability -/

/-- **Radau IIA has stiff decay**: R(x) → 0 as x → -∞. -/
theorem radauIIA2_stiffDecay :
    Tendsto (fun x : ℝ => radauIIA2StabilityFn (↑x)) atBot (nhds 0) := by
  apply NormedAddCommGroup.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [eventually_lt_atBot (min (-3) (-4/ε))] with x hx
  have hx_neg3 : x < -3 := by linarith [min_le_left (-3 : ℝ) (-4/ε)]
  have hx_large : -x > 4/ε := by
    have : -4/ε = -(4/ε) := by ring
    linarith [min_le_right (-3 : ℝ) (-4/ε)]
  have hD_pos : (0 : ℝ) < 1 - 2 * x / 3 + x ^ 2 / 6 := by nlinarith [sq_nonneg x]
  have hx2_pos : (0 : ℝ) < x ^ 2 / 6 := by nlinarith [sq_nonneg x]
  simp only [radauIIA2StabilityFn]
  rw [show radauIIA2Num (↑x) = ((1 + x / 3 : ℝ) : ℂ) from by simp [radauIIA2Num],
      show radauIIA2Denom (↑x) = ((1 - 2 * x / 3 + x ^ 2 / 6 : ℝ) : ℂ) from by
        simp [radauIIA2Denom],
      show ((1 + x / 3 : ℝ) : ℂ) / ((1 - 2 * x / 3 + x ^ 2 / 6 : ℝ) : ℂ) =
        (((1 + x / 3) / (1 - 2 * x / 3 + x ^ 2 / 6) : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hD_pos,
      abs_of_nonpos (by linarith : 1 + x / 3 ≤ 0)]
  -- -(1 + x/3) / D(x) ≤ (-x/3) / (x²/6) = 2/(-x) < ε
  calc -(1 + x / 3) / (1 - 2 * x / 3 + x ^ 2 / 6)
      ≤ (-x / 3) / (x ^ 2 / 6) := by
        have hN : -(1 + x / 3) ≤ -x / 3 := by linarith
        have hDl : x ^ 2 / 6 ≤ 1 - 2 * x / 3 + x ^ 2 / 6 := by nlinarith
        rw [div_le_div_iff₀ hD_pos hx2_pos]
        calc -(1 + x / 3) * (x ^ 2 / 6) ≤ (-x / 3) * (x ^ 2 / 6) := by nlinarith
          _ ≤ (-x / 3) * (1 - 2 * x / 3 + x ^ 2 / 6) := by nlinarith
    _ = 2 / (-x) := by field_simp; nlinarith [sq_nonneg x]
    _ < ε := by
        rw [div_lt_iff₀ (show (0:ℝ) < -x by linarith)]
        have h4e : ε * (4 / ε) = 4 := by field_simp
        nlinarith

/-- **Radau IIA 2-stage is L-stable**: A-stable with stiff decay.
  Reference: Iserles, Section 4.2. -/
theorem radauIIA2_lStable :
    (∀ z : ℂ, z.re ≤ 0 → radauIIA2Denom z ≠ 0 → ‖radauIIA2StabilityFn z‖ ≤ 1) ∧
    Tendsto (fun x : ℝ => radauIIA2StabilityFn (↑x)) atBot (nhds 0) :=
  ⟨fun z hz _ => radauIIA2_aStable z hz, radauIIA2_stiffDecay⟩
