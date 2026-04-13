import OpenMath.Collocation
import OpenMath.StiffEquations
import OpenMath.RadauIIA3

/-!
# Radau IA 3-Stage Method (Section 4.2)

The **Radau IA 3-stage** method is a 3-stage implicit Runge–Kutta method based on
Radau quadrature on [0,1] with the left endpoint included (c₁ = 0).

Butcher tableau:
```
  0           | 1/9              (-1-√6)/18       (-1+√6)/18
  (6-√6)/10   | 1/9              (88+7√6)/360     (88-43√6)/360
  (6+√6)/10   | 1/9              (88+43√6)/360    (88-7√6)/360
  ------------|--------------------------------------------------
              | 1/9              (16+√6)/36        (16-√6)/36
```

The nodes are c₁ = 0, c₂ = (6-√6)/10, c₃ = (6+√6)/10, and the method achieves
order 2s − 1 = 5.

## Key Properties

- **Order ≥ 5** (proven): via B(5) ∧ C(2) ∧ D(2) simplifying assumptions
- **B(5)**: Radau quadrature with left endpoint integrates polynomials up to degree 4
- **C(2)**: the collocation-like condition holds for k = 1, 2
- **D(3)**: the adjoint condition holds for k = 1, 2, 3 (D(s) for s = 3)

The first column of A is constant (= 1/9 = b₁), a characteristic property of
Radau IA methods.

Reference: Iserles, *A First Course in the Numerical Analysis of Differential
Equations*, Section 4.2; Hairer–Wanner, *Solving ODEs II*, Table IV.5.4.
-/

open Finset Real Filter

/-! ## √6 Utilities -/

private theorem sqrt6_pos : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos_of_pos (by norm_num)
private theorem sqrt6_sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)
private theorem sqrt6_nonneg : (0 : ℝ) ≤ Real.sqrt 6 := le_of_lt sqrt6_pos
private theorem sqrt6_lt_three : Real.sqrt 6 < 3 := by
  nlinarith [sqrt6_sq, sq_nonneg (Real.sqrt 6 - 3)]

/-! ## Butcher Tableau Definition -/

/-- **Radau IA 3-stage** RK method.
  Collocation points: c₁ = 0, c₂ = (6-√6)/10, c₃ = (6+√6)/10 (Radau quadrature, left endpoint).
  The first column of A is constant (= 1/9), a characteristic property of Radau IA.
  Reference: Iserles, Section 4.2; Hairer–Wanner, Table IV.5.4. -/
noncomputable def rkRadauIA3 : ButcherTableau 3 where
  A := ![![1/9, (-1 - Real.sqrt 6) / 18, (-1 + Real.sqrt 6) / 18],
         ![1/9, (88 + 7 * Real.sqrt 6) / 360, (88 - 43 * Real.sqrt 6) / 360],
         ![1/9, (88 + 43 * Real.sqrt 6) / 360, (88 - 7 * Real.sqrt 6) / 360]]
  b := ![1/9, (16 + Real.sqrt 6) / 36, (16 - Real.sqrt 6) / 36]
  c := ![0, (6 - Real.sqrt 6) / 10, (6 + Real.sqrt 6) / 10]

/-! ## Basic Properties -/

theorem rkRadauIA3_consistent : rkRadauIA3.IsConsistent where
  weights_sum := by simp [rkRadauIA3, Fin.sum_univ_three]; ring
  row_sum := by
    intro i; fin_cases i <;> simp [rkRadauIA3, Fin.sum_univ_three] <;> ring

theorem rkRadauIA3_nonNegWeights : rkRadauIA3.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkRadauIA3]
  · nlinarith [sqrt6_nonneg]
  · nlinarith [sqrt6_lt_three]

theorem rkRadauIA3_not_explicit : ¬rkRadauIA3.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkRadauIA3] at this

/-- The first column of A is constant (= 1/9), a characteristic of Radau IA. -/
theorem rkRadauIA3_first_col_constant :
    ∀ i : Fin 3, rkRadauIA3.A i 0 = 1/9 := by
  intro i; fin_cases i <;> simp [rkRadauIA3]

/-! ## Simplifying Assumptions -/

/-- Radau IA 3-stage satisfies B(5): the Radau quadrature with left endpoint integrates
polynomials of degree ≤ 4 exactly (2s−1 = 5 for s=3). -/
theorem rkRadauIA3_B5 : rkRadauIA3.SatisfiesB 5 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkRadauIA3, Fin.sum_univ_three] <;> nlinarith [sqrt6_sq]

/-- Radau IA 3-stage satisfies C(2): ∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k/k for k = 1, 2.
(Radau IA satisfies C(s-1) = C(2) in general.) -/
theorem rkRadauIA3_C2 : rkRadauIA3.SatisfiesC 2 := by
  intro k hk1 hk2 i
  interval_cases k <;> fin_cases i <;>
    simp [rkRadauIA3, Fin.sum_univ_three] <;> nlinarith [sqrt6_sq]

/-- Radau IA 3-stage satisfies D(3): ∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = bⱼ(1 − cⱼ^k)/k
for k = 1, 2, 3 and all j. (Radau IA satisfies D(s) = D(3) in general.) -/
theorem rkRadauIA3_D3 : rkRadauIA3.SatisfiesD 3 := by
  intro k hk1 hk2 j
  interval_cases k <;> fin_cases j <;>
    simp [rkRadauIA3, Fin.sum_univ_three] <;> nlinarith [sqrt6_sq]

/-! ## Order ≥ 5

Radau IA 3-stage has order ≥ 5 via B(5) ∧ C(2) ∧ D(2). In fact Radau IA 3-stage
has order exactly 2s − 1 = 5.

The order follows from the simplifying assumptions theorem: B(5), C(2), D(2) implies
all 17 order conditions through order 5, since 5 ≤ 2+2+1 and 5 ≤ 2·2+2 in the
Butcher theorem (Hairer–Nørsett–Wanner IV.5.1). -/

theorem rkRadauIA3_order5 : rkRadauIA3.HasOrderGe5 :=
  ButcherTableau.HasOrderGe5_of_B5_C2_D2 _
    rkRadauIA3_B5 rkRadauIA3_C2 (rkRadauIA3_D3.mono (by omega))

/-! ## Stability Function

The Radau IA 3-stage stability function is the (2,3)-Padé approximant to eᶻ (same as
Radau IIA 3-stage, since both methods have the same weights and order):
  R(z) = P(z)/Q(z) where (scaled by 60):
  P(z) = 60 + 24z + 3z²
  Q(z) = 60 − 36z + 9z² − z³

Since deg(numerator) = 2 < deg(denominator) = 3, R(z) → 0 as z → −∞,
giving stiff decay and hence L-stability.

We use the same scaled polynomials as in RadauIIA3 for consistency. -/

/-- Scaled numerator: P(z) = 60 + 24z + 3z² = 60 · (1 + 2z/5 + z²/20). -/
noncomputable def radauIA3P (z : ℂ) : ℂ := 60 + 24 * z + 3 * z ^ 2

/-- Scaled denominator: Q(z) = 60 − 36z + 9z² − z³ = 60 · (1 − 3z/5 + 3z²/20 − z³/60). -/
noncomputable def radauIA3Q (z : ℂ) : ℂ := 60 - 36 * z + 9 * z ^ 2 - z ^ 3

/-- Radau IA 3-stage stability function: R(z) = P(z)/Q(z). -/
noncomputable def radauIA3StabilityFn (z : ℂ) : ℂ := radauIA3P z / radauIA3Q z

/-- P(z) = 60 · N(z) where N is the RadauIIA3 numerator. -/
theorem radauIA3P_eq (z : ℂ) : radauIA3P z = 60 * radauIIA3Num z := by
  simp [radauIA3P, radauIIA3Num]; ring

/-- Q(z) = 60 · D(z) where D is the RadauIIA3 denominator. -/
theorem radauIA3Q_eq (z : ℂ) : radauIA3Q z = 60 * radauIIA3Denom z := by
  simp [radauIA3Q, radauIIA3Denom]; ring

/-- The Radau IA 3-stage stability function equals the Radau IIA 3-stage stability function
(both are the (2,3)-Padé approximant to eᶻ). -/
theorem radauIA3_eq_radauIIA3_stability (z : ℂ) :
    radauIA3StabilityFn z = radauIIA3StabilityFn z := by
  simp only [radauIA3StabilityFn, radauIIA3StabilityFn, radauIA3P_eq, radauIA3Q_eq]
  rw [mul_div_mul_left _ _ (by norm_num : (60 : ℂ) ≠ 0)]

/-- **A-stability of Radau IA 3-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0. -/
theorem radauIA3_aStable (z : ℂ) (hz : z.re ≤ 0) : ‖radauIA3StabilityFn z‖ ≤ 1 := by
  rw [radauIA3_eq_radauIIA3_stability]
  exact radauIIA3_aStable z hz

/-! ## L-stability (Stiff Decay)

Since deg(P) = 2 < deg(Q) = 3, R(x) → 0 as x → −∞. -/

/-- Radau IA 3-stage has stiff decay: R(x) → 0 as x → −∞. -/
theorem radauIA3_stiffDecay :
    Tendsto (fun x : ℝ => radauIA3StabilityFn (↑x)) atBot (nhds 0) := by
  simp_rw [radauIA3_eq_radauIIA3_stability]
  exact radauIIA3_stiffDecay

/-! ## Algebraic Stability -/

/-- **Radau IA 3-stage is algebraically stable**: M is positive semidefinite. -/
theorem rkRadauIA3_algStable : rkRadauIA3.IsAlgStable where
  nonneg_weights := rkRadauIA3_nonNegWeights
  posdef_M := by
    intro v; simp [ButcherTableau.algStabMatrix, rkRadauIA3, Fin.sum_univ_three]
    have hs := sqrt6_sq
    norm_num; ring_nf; rw [hs]
    -- The M matrix is rank 1 (all 2×2 minors vanish when s²=6).
    -- The quadratic form equals (2v₀ - (1+√6)v₁ - (1-√6)v₂)² / 324.
    have key : (2 * v 0 - (1 + Real.sqrt 6) * v 1 - (1 - Real.sqrt 6) * v 2) ^ 2 =
        4 * v 0 ^ 2 + (7 + 2 * Real.sqrt 6) * v 1 ^ 2 + (7 - 2 * Real.sqrt 6) * v 2 ^ 2 -
        (4 + 4 * Real.sqrt 6) * (v 0 * v 1) - (4 - 4 * Real.sqrt 6) * (v 0 * v 2) -
        10 * (v 1 * v 2) := by
      ring_nf; rw [hs]; ring_nf
    linarith [sq_nonneg (2 * v 0 - (1 + Real.sqrt 6) * v 1 - (1 - Real.sqrt 6) * v 2), key]
