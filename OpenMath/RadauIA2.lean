import OpenMath.StiffEquations
import OpenMath.Collocation

/-!
# Radau IA 2-Stage Method (Section 4.2)

The **Radau IA 2-stage** method is a 2-stage implicit Runge–Kutta method based on
Radau quadrature on [0,1] with the left endpoint included.

Butcher tableau:
```
  0   | 1/4   -1/4
  2/3 | 1/4    5/12
  ----|---------------
      | 1/4    3/4
```

The nodes are c₁ = 0, c₂ = 2/3, and the method achieves order 2s − 1 = 3.

The stability function is R(z) = (1 + z/3) / (1 − 2z/3 + z²/6), the same
(1,2)-Padé approximant to eᶻ as for Radau IIA 2-stage. Since
deg(numerator) = 1 < deg(denominator) = 2, R(z) → 0 as z → −∞,
giving stiff decay and hence L-stability.

The method satisfies simplifying assumptions B(3), C(1), and D(2).

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 2.2 and 4.2; Hairer–Wanner, Table 5.4.
-/

open Finset Real Filter

/-! ## Butcher Tableau Definition -/

/-- **Radau IA 2-stage** RK method.
  Collocation points: c₁ = 0, c₂ = 2/3 (Radau quadrature with left endpoint).
  Reference: Iserles, Chapter 2 and 4; Hairer–Wanner, Table 5.4. -/
noncomputable def rkRadauIA2 : ButcherTableau 2 where
  A := ![![1/4, -1/4], ![1/4, 5/12]]
  b := ![1/4, 3/4]
  c := ![0, 2/3]

/-! ## Basic Properties -/

/-- Radau IA 2-stage is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkRadauIA2_consistent : rkRadauIA2.IsConsistent where
  weights_sum := by simp [rkRadauIA2, Fin.sum_univ_two]; norm_num
  row_sum := by
    intro i; fin_cases i <;> simp [rkRadauIA2, Fin.sum_univ_two] <;> norm_num

/-- Radau IA 2-stage has non-negative weights. -/
theorem rkRadauIA2_nonNegWeights : rkRadauIA2.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkRadauIA2] <;> norm_num

/-- Radau IA 2-stage is NOT explicit. -/
theorem rkRadauIA2_not_explicit : ¬rkRadauIA2.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkRadauIA2] at this

/-- Radau IA 2-stage is NOT stiffly accurate: b₂ = 3/4 ≠ a₂₂ = 5/12. -/
theorem rkRadauIA2_not_stifflyAccurate :
    ¬(∀ i : Fin 2, rkRadauIA2.b i = rkRadauIA2.A 1 i) := by
  intro h; have := h 1; simp [rkRadauIA2] at this; norm_num at this

/-! ## Order Conditions -/

/-- Radau IA 2-stage has order at least 3. -/
theorem rkRadauIA2_order3 : rkRadauIA2.HasOrderGe3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ButcherTableau.order1, rkRadauIA2, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order2, rkRadauIA2, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order3a, rkRadauIA2, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order3b, rkRadauIA2, Fin.sum_univ_two]; norm_num

/-- Radau IA 2-stage does NOT have order 4: ∑ bᵢ cᵢ³ = 2/9 ≠ 1/4. -/
theorem rkRadauIA2_not_order4 : ¬rkRadauIA2.HasOrderGe4 := by
  intro ⟨_, _, _, _, h4a, _⟩
  simp [ButcherTableau.order4a, rkRadauIA2, Fin.sum_univ_two] at h4a; norm_num at h4a

/-! ## Simplifying Assumptions -/

/-- Radau IA 2-stage satisfies B(3): the quadrature (b, c) integrates polynomials
of degree ≤ 2 exactly. -/
theorem rkRadauIA2_B3 : rkRadauIA2.SatisfiesB 3 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkRadauIA2, Fin.sum_univ_two] <;> norm_num

/-- Radau IA 2-stage satisfies C(1): the row-sum condition. -/
theorem rkRadauIA2_C1 : rkRadauIA2.SatisfiesC 1 := by
  rw [ButcherTableau.satisfiesC_one_iff]
  exact rkRadauIA2_consistent.row_sum

/-- Radau IA 2-stage satisfies D(2). -/
theorem rkRadauIA2_D2 : rkRadauIA2.SatisfiesD 2 := by
  intro k hk1 hk2 j
  interval_cases k <;> fin_cases j <;>
    simp [rkRadauIA2, Fin.sum_univ_two] <;> norm_num

/-! ## Stability Function

The stability function of Radau IA 2-stage is the same (1,2)-Padé approximant
to eᶻ as Radau IIA 2-stage:
  R(z) = (1 + z/3) / (1 − 2z/3 + z²/6)

This follows from the general theory: Radau IA and Radau IIA with the same
number of stages share the same stability function.
-/

/-- The Radau IA 2-stage stability function equals the Radau IIA 2-stage one:
  R(z) = (1 + z/3) / (1 − 2z/3 + z²/6). -/
noncomputable def radauIA2StabilityFn (z : ℂ) : ℂ :=
  radauIIA2Num z / radauIIA2Denom z

/-- The Radau IA and Radau IIA 2-stage stability functions are identical. -/
theorem radauIA2_eq_radauIIA2_stabilityFn :
    radauIA2StabilityFn = radauIIA2StabilityFn :=
  rfl

/-! ### A-Stability -/

/-- **A-stability of Radau IA 2-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  Follows from the shared stability function with Radau IIA 2-stage. -/
theorem radauIA2_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖radauIA2StabilityFn z‖ ≤ 1 :=
  radauIIA2_aStable z hz

/-! ### Stiff Decay and L-Stability -/

/-- **Radau IA 2-stage has stiff decay**: R(x) → 0 as x → −∞.
  Follows from the shared stability function with Radau IIA 2-stage. -/
theorem radauIA2_stiffDecay :
    Tendsto (fun x : ℝ => radauIA2StabilityFn (↑x)) atBot (nhds 0) :=
  radauIIA2_stiffDecay

/-- **Radau IA 2-stage is L-stable**: A-stable with stiff decay. -/
theorem radauIA2_lStable :
    (∀ z : ℂ, z.re ≤ 0 → radauIIA2Denom z ≠ 0 → ‖radauIA2StabilityFn z‖ ≤ 1) ∧
    Tendsto (fun x : ℝ => radauIA2StabilityFn (↑x)) atBot (nhds 0) :=
  ⟨fun z hz _ => radauIA2_aStable z hz, radauIA2_stiffDecay⟩

/-! ## Algebraic Stability -/

/-- Radau IA 2-stage is algebraically stable.
  M = (1/16)·[[1, −1], [−1, 1]], so v^T M v = (v₀ − v₁)²/16 ≥ 0. -/
theorem rkRadauIA2_algStable : rkRadauIA2.IsAlgStable where
  nonneg_weights := rkRadauIA2_nonNegWeights
  posdef_M := by
    intro v; simp [ButcherTableau.algStabMatrix, rkRadauIA2, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 - v 1)]

/-! ## Radau IIA 2-Stage: Simplifying Assumptions

The Radau IIA 2-stage method also satisfies simplifying assumptions B(3) and C(2),
giving an alternative derivation of its order 3 property.
-/

/-- Radau IIA 2-stage satisfies B(3). -/
theorem rkRadauIIA2_B3 : rkRadauIIA2.SatisfiesB 3 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkRadauIIA2, Fin.sum_univ_two] <;> norm_num

/-- Radau IIA 2-stage satisfies C(2): ∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k/k for k = 1, 2. -/
theorem rkRadauIIA2_C2 : rkRadauIIA2.SatisfiesC 2 := by
  intro k hk1 hk2 i
  interval_cases k <;> fin_cases i <;>
    simp [rkRadauIIA2, Fin.sum_univ_two] <;> norm_num

/-- Radau IIA 2-stage has order ≥ 3 via B(3) ∧ C(2). -/
theorem rkRadauIIA2_order3' : rkRadauIIA2.HasOrderGe3 :=
  ButcherTableau.HasOrderGe3_of_B3_C2 _ rkRadauIIA2_B3 rkRadauIIA2_C2
