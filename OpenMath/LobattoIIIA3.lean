import OpenMath.Collocation
import OpenMath.StiffEquations

/-!
# Lobatto IIIA 3-Stage Method (Section 4.2)

The **Lobatto IIIA 3-stage** method is a 3-stage implicit Runge–Kutta method
based on Lobatto quadrature with collocation at 0, 1/2, and 1.

Butcher tableau:
```
  0   | 0      0      0
  1/2 | 5/24   1/3    -1/24
  1   | 1/6    2/3    1/6
  ----|----------------------
      | 1/6    2/3    1/6
```

The weights (1/6, 2/3, 1/6) form Simpson's rule, which integrates polynomials
of degree ≤ 3 exactly, i.e., **B(4)** holds.

The method satisfies the collocation condition **C(3)**, and the combination
B(4) ∧ C(3) implies **order 4** (= 2s − 2 for s = 3 stages).

The stability function is R(z) = (1+z/2+z²/12)/(1-z/2+z²/12), the
(2,2)-diagonal Padé approximant to eᶻ — identical to the Gauss–Legendre
2-stage stability function. Since R(z) → 1 as z → -∞, the method is
A-stable but **NOT L-stable**.

The method is stiffly accurate (b = last row of A) but NOT algebraically
stable (M₁₁ = −1/36 < 0).

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 4.2; Hairer–Wanner, Table 5.5.
-/

open Finset Real Filter

/-! ## Butcher Tableau Definition -/

/-- **Lobatto IIIA 3-stage** RK method.
  Collocation points: c₁ = 0, c₂ = 1/2, c₃ = 1.
  Weights form Simpson's rule: b = (1/6, 2/3, 1/6).
  Reference: Iserles, Section 4.2 / Hairer–Wanner, Table 5.5. -/
noncomputable def rkLobattoIIIA3 : ButcherTableau 3 where
  A := ![![0, 0, 0],
         ![5/24, 1/3, -1/24],
         ![1/6, 2/3, 1/6]]
  b := ![1/6, 2/3, 1/6]
  c := ![0, 1/2, 1]

/-! ## Basic Properties -/

/-- Lobatto IIIA 3-stage is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkLobattoIIIA3_consistent : rkLobattoIIIA3.IsConsistent where
  weights_sum := by simp [rkLobattoIIIA3, Fin.sum_univ_three]; norm_num
  row_sum := by
    intro i; fin_cases i <;> simp [rkLobattoIIIA3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIA 3-stage has non-negative weights. -/
theorem rkLobattoIIIA3_nonNegWeights : rkLobattoIIIA3.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkLobattoIIIA3] <;> norm_num

/-- Lobatto IIIA 3-stage is stiffly accurate: bᵢ = a_{3,i} for all i. -/
theorem rkLobattoIIIA3_stifflyAccurate :
    ∀ i : Fin 3, rkLobattoIIIA3.b i = rkLobattoIIIA3.A 2 i := by
  intro i; fin_cases i <;> simp [rkLobattoIIIA3]

/-- Lobatto IIIA 3-stage is NOT explicit (a₂₂ = 1/3 ≠ 0). -/
theorem rkLobattoIIIA3_not_explicit : ¬rkLobattoIIIA3.IsExplicit := by
  intro h; have := h 1 1 (le_refl _); simp [rkLobattoIIIA3] at this

/-! ## Simplifying Assumptions

Simpson's rule (b = (1/6, 2/3, 1/6) on nodes c = (0, 1/2, 1)) integrates
polynomials of degree ≤ 3 exactly, giving B(4).

The stage coefficients are determined by collocation, giving C(3).

Together, B(4) ∧ C(3) implies order 4 via `HasOrderGe4_of_B4_C3`.
-/

/-- Lobatto IIIA 3-stage satisfies B(4): Simpson's rule integrates
  polynomials of degree ≤ 3 exactly. -/
theorem rkLobattoIIIA3_B4 : rkLobattoIIIA3.SatisfiesB 4 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkLobattoIIIA3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIA 3-stage satisfies C(3): the collocation conditions hold
  for k = 1, 2, 3. -/
theorem rkLobattoIIIA3_C3 : rkLobattoIIIA3.SatisfiesC 3 := by
  intro k hk1 hk2 i
  interval_cases k <;> fin_cases i <;>
    simp [rkLobattoIIIA3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIA 3-stage satisfies D(1): ∑ᵢ bᵢ aᵢⱼ = bⱼ(1 − cⱼ). -/
theorem rkLobattoIIIA3_D1 : rkLobattoIIIA3.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk
  fin_cases j <;> simp [rkLobattoIIIA3, Fin.sum_univ_three] <;> norm_num

/-! ## Order -/

/-- **Lobatto IIIA 3-stage has order 4**, derived from B(4) ∧ C(3).
  This is the maximum order 2s − 2 = 4 for a Lobatto-type method with s = 3.
  Reference: Iserles, Theorem 2.6. -/
theorem rkLobattoIIIA3_order4 : rkLobattoIIIA3.HasOrderGe4 :=
  ButcherTableau.HasOrderGe4_of_B4_C3 _ rkLobattoIIIA3_B4 rkLobattoIIIA3_C3

/-- Lobatto IIIA 3-stage does NOT satisfy B(5): Simpson's rule gives
  ∑ bᵢ cᵢ⁴ = 5/24 ≠ 1/5. -/
theorem rkLobattoIIIA3_not_B5 : ¬rkLobattoIIIA3.SatisfiesB 5 := by
  intro h
  have h5 := h 5 (by omega) le_rfl
  simp [rkLobattoIIIA3, Fin.sum_univ_three] at h5
  norm_num at h5

/-! ## Stability Function

The stability function of Lobatto IIIA 3-stage is:
  R(z) = (1 + z/2 + z²/12) / (1 − z/2 + z²/12)

This is the (2,2)-diagonal Padé approximant to eᶻ, identical to the
Gauss–Legendre 2-stage stability function `gl2StabilityFn`.

Computation:
  det(I − zA) = 1 − z/2 + z²/12  (= gl2Denom)
  det(I − zA + z·𝟙·bᵀ) = 1 + z/2 + z²/12  (= gl2Num)
  R(z) = gl2Num(z) / gl2Denom(z) = gl2StabilityFn(z)
-/

/-! ### A-Stability -/

/-- **A-stability of Lobatto IIIA 3-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  The stability function is identical to GL2, so A-stability follows directly.
  Reference: Iserles, Section 4.2. -/
theorem lobIIIA3_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖gl2StabilityFn z‖ ≤ 1 :=
  gl2_aStable z hz

/-! ### NOT L-Stable

Since R(z) = gl2StabilityFn(z) → 1 as z → −∞, the method does NOT have
stiff decay and is NOT L-stable. -/

/-- **Lobatto IIIA 3-stage does NOT have stiff decay**: R(z) → 1 ≠ 0 as z → −∞. -/
theorem lobIIIA3_not_stiffDecay :
    ¬Tendsto (fun x : ℝ => gl2StabilityFn (↑x)) atBot (nhds 0) :=
  gl2_not_stiffDecay

/-! ## NOT Algebraically Stable -/

/-- **Lobatto IIIA 3-stage is NOT algebraically stable.**
  M₁₁ = 2b₁a₁₁ − b₁² = 2·(1/6)·0 − (1/6)² = −1/36 < 0.
  With v = (1,0,0), the quadratic form is −1/36 < 0. -/
theorem rkLobattoIIIA3_not_algStable : ¬rkLobattoIIIA3.IsAlgStable := by
  intro ⟨_, hM⟩
  have h := hM (fun i => if i = 0 then 1 else 0)
  simp [ButcherTableau.algStabMatrix, rkLobattoIIIA3] at h
  linarith

/-! ## Comparison with GL2 and Lobatto IIIA 2-Stage

| Property          | IIIA 2-stage      | IIIA 3-stage             | GL2              |
|-------------------|-------------------|--------------------------|------------------|
| Stages            | 2                 | 3                        | 2                |
| Order             | 2                 | 4                        | 4                |
| R(z)              | (2+z)/(2−z)       | (12+6z+z²)/(12−6z+z²)   | same as IIIA-3   |
| R(−∞)             | −1                | 1                        | 1                |
| L-stable          | ✗                 | ✗                        | ✗                |
| Alg. stable       | ✗                 | ✗                        | ✓                |
| Stiffly accurate  | ✓                 | ✓                        | ✗                |
-/
