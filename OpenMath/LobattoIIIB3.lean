import OpenMath.Collocation
import OpenMath.StiffEquations

/-!
# Lobatto IIIB 3-Stage Method (Section 4.2)

The **Lobatto IIIB 3-stage** method is a 3-stage implicit Runge–Kutta method,
the "adjoint" of the Lobatto IIIA 3-stage method.

Butcher tableau:
```
  0   | 1/6   -1/6    0
  1/2 | 1/6    1/3    0
  1   | 1/6    5/6    0
  ----|----------------------
      | 1/6    2/3    1/6
```

The weights (1/6, 2/3, 1/6) form Simpson's rule, which integrates polynomials
of degree ≤ 3 exactly, i.e., **B(4)** holds.

The last column of A is zero, a defining characteristic of Lobatto IIIB.

The method satisfies **C(1)** (row-sum consistent) but **NOT C(2)**.
It satisfies **D(3)** (and hence D(1), D(2)), and the combination
B(4) ∧ C(1) ∧ D(2) implies **order 4**.

The stability function is R(z) = (1+z/2+z²/12)/(1−z/2+z²/12), the
(2,2)-diagonal Padé approximant to eᶻ — identical to the Gauss–Legendre
2-stage and Lobatto IIIA 3-stage stability functions. Since R(z) → 1 as
z → −∞, the method is A-stable but **NOT L-stable**.

The method is NOT stiffly accurate (b ≠ last row of A) and NOT
algebraically stable (M₃₃ = −1/36 < 0).

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 4.2; Hairer–Wanner, Table 5.7.
-/

open Finset Real Filter

/-! ## Butcher Tableau Definition -/

/-- **Lobatto IIIB 3-stage** RK method.
  Collocation points: c₁ = 0, c₂ = 1/2, c₃ = 1.
  The last column of A is zero.
  Reference: Iserles, Section 4.2 / Hairer–Wanner, Table 5.7. -/
noncomputable def rkLobattoIIIB3 : ButcherTableau 3 where
  A := ![![1/6, -1/6, 0],
         ![1/6, 1/3, 0],
         ![1/6, 5/6, 0]]
  b := ![1/6, 2/3, 1/6]
  c := ![0, 1/2, 1]

/-! ## Basic Properties -/

/-- Lobatto IIIB 3-stage is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkLobattoIIIB3_consistent : rkLobattoIIIB3.IsConsistent where
  weights_sum := by simp [rkLobattoIIIB3, Fin.sum_univ_three]; norm_num
  row_sum := by
    intro i; fin_cases i <;> simp [rkLobattoIIIB3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIB 3-stage has non-negative weights. -/
theorem rkLobattoIIIB3_nonNegWeights : rkLobattoIIIB3.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkLobattoIIIB3] <;> norm_num

/-- Lobatto IIIB 3-stage is NOT stiffly accurate: b ≠ last row of A.
  b₁ = 2/3 but a₃₁ = 5/6. -/
theorem rkLobattoIIIB3_not_stifflyAccurate :
    ¬∀ i : Fin 3, rkLobattoIIIB3.b i = rkLobattoIIIB3.A 2 i := by
  intro h; have := h 1; simp [rkLobattoIIIB3] at this; norm_num at this

/-- Lobatto IIIB 3-stage is NOT explicit (a₁₁ = 1/6 ≠ 0). -/
theorem rkLobattoIIIB3_not_explicit : ¬rkLobattoIIIB3.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkLobattoIIIB3] at this

/-- The last column of A is zero, characteristic of Lobatto IIIB. -/
theorem rkLobattoIIIB3_zeroLastCol :
    ∀ i : Fin 3, rkLobattoIIIB3.A i 2 = 0 := by
  intro i; fin_cases i <;> simp [rkLobattoIIIB3]

/-! ## Simplifying Assumptions

Simpson's rule gives B(4). The row-sum condition gives C(1), but C(2)
fails. The method satisfies D(3) (in particular D(1) and D(2)).

The order theorem `HasOrderGe4_of_B4_C1_D2` gives order 4 from
B(4) ∧ C(1) ∧ D(2).
-/

/-- Lobatto IIIB 3-stage satisfies B(4): Simpson's rule integrates
  polynomials of degree ≤ 3 exactly. -/
theorem rkLobattoIIIB3_B4 : rkLobattoIIIB3.SatisfiesB 4 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkLobattoIIIB3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIB 3-stage satisfies C(1): row-sum consistent. -/
theorem rkLobattoIIIB3_C1 : rkLobattoIIIB3.SatisfiesC 1 := by
  rw [ButcherTableau.satisfiesC_one_iff]
  exact rkLobattoIIIB3_consistent.row_sum

/-- Lobatto IIIB 3-stage does NOT satisfy C(2): for i=0 (c₀=0),
  ∑ⱼ a₀ⱼ cⱼ = −1/12 ≠ 0 = c₀²/2. -/
theorem rkLobattoIIIB3_not_C2 : ¬rkLobattoIIIB3.SatisfiesC 2 := by
  intro h
  have h2 := h 2 (by omega) le_rfl 0
  simp [rkLobattoIIIB3, Fin.sum_univ_three] at h2

/-- Lobatto IIIB 3-stage satisfies D(1): ∑ᵢ bᵢ aᵢⱼ = bⱼ(1 − cⱼ). -/
theorem rkLobattoIIIB3_D1 : rkLobattoIIIB3.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk
  fin_cases j <;> simp [rkLobattoIIIB3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIB 3-stage satisfies D(2): ∑ᵢ bᵢ cᵢ aᵢⱼ = bⱼ(1−cⱼ²)/2. -/
theorem rkLobattoIIIB3_D2 : rkLobattoIIIB3.SatisfiesD 2 := by
  intro k hk1 hk2 j
  interval_cases k <;> fin_cases j <;>
    simp [rkLobattoIIIB3, Fin.sum_univ_three] <;> norm_num

/-- Lobatto IIIB 3-stage satisfies D(3): ∑ᵢ bᵢ cᵢ² aᵢⱼ = bⱼ(1−cⱼ³)/3.
  This is the maximum D-order for the 3-stage Lobatto IIIB method. -/
theorem rkLobattoIIIB3_D3 : rkLobattoIIIB3.SatisfiesD 3 := by
  intro k hk1 hk2 j
  interval_cases k <;> fin_cases j <;>
    simp [rkLobattoIIIB3, Fin.sum_univ_three] <;> norm_num

/-! ## Order -/

/-- **Lobatto IIIB 3-stage has order 4**, derived from B(4) ∧ C(1) ∧ D(2).
  This is the maximum order 2s − 2 = 4 for a Lobatto-type method with s = 3.
  Reference: Iserles, Theorem 2.6 / Hairer–Wanner, Theorem IV.5.1. -/
theorem rkLobattoIIIB3_order4 : rkLobattoIIIB3.HasOrderGe4 :=
  ButcherTableau.HasOrderGe4_of_B4_C1_D2 _
    rkLobattoIIIB3_B4 rkLobattoIIIB3_C1 rkLobattoIIIB3_D2

/-- Lobatto IIIB 3-stage does NOT satisfy B(5): Simpson's rule gives
  ∑ bᵢ cᵢ⁴ = 5/24 ≠ 1/5. -/
theorem rkLobattoIIIB3_not_B5 : ¬rkLobattoIIIB3.SatisfiesB 5 := by
  intro h
  have h5 := h 5 (by omega) le_rfl
  simp [rkLobattoIIIB3, Fin.sum_univ_three] at h5
  norm_num at h5

/-- **Lobatto IIIB 3-stage does NOT have order 5**: since B(5) fails,
  the first fifth-order condition (order5a: ∑ bᵢcᵢ⁴ = 1/5) fails.
  The order is exactly 2s−2 = 4. -/
theorem rkLobattoIIIB3_not_order5 : ¬rkLobattoIIIB3.HasOrderGe5 := by
  intro ⟨_, h5a, _⟩
  simp [ButcherTableau.order5a, rkLobattoIIIB3, Fin.sum_univ_three] at h5a
  norm_num at h5a

/-! ## Stability Function

The stability function of Lobatto IIIB 3-stage is:
  R(z) = (1 + z/2 + z²/12) / (1 − z/2 + z²/12)

This is the (2,2)-diagonal Padé approximant to eᶻ, identical to the
Gauss–Legendre 2-stage and Lobatto IIIA 3-stage stability functions.

Computation:
  det(I − zA) = 1 − z/2 + z²/12  (expanding along the zero last column)
  det(I − zA + z·𝟙·bᵀ) = 1 + z/2 + z²/12
  R(z) = gl2Num(z) / gl2Denom(z) = gl2StabilityFn(z)
-/

/-! ### A-Stability -/

/-- **A-stability of Lobatto IIIB 3-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  The stability function is identical to GL2, so A-stability follows directly.
  Reference: Iserles, Section 4.2. -/
theorem lobIIIB3_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖gl2StabilityFn z‖ ≤ 1 :=
  gl2_aStable z hz

/-! ### NOT L-Stable

Since R(z) = gl2StabilityFn(z) → 1 as z → −∞, the method does NOT have
stiff decay and is NOT L-stable. -/

/-- **Lobatto IIIB 3-stage does NOT have stiff decay**: R(z) → 1 ≠ 0 as z → −∞. -/
theorem lobIIIB3_not_stiffDecay :
    ¬Tendsto (fun x : ℝ => gl2StabilityFn (↑x)) atBot (nhds 0) :=
  gl2_not_stiffDecay

/-! ## NOT Algebraically Stable -/

/-- **Lobatto IIIB 3-stage is NOT algebraically stable.**
  M₃₃ = 2b₃a₃₃ − b₃² = 2·(1/6)·0 − (1/6)² = −1/36 < 0.
  With v = (0,0,1), the quadratic form is −1/36 < 0. -/
theorem rkLobattoIIIB3_not_algStable : ¬rkLobattoIIIB3.IsAlgStable := by
  intro ⟨_, hM⟩
  have h := hM (fun i => if i = 2 then 1 else 0)
  simp [ButcherTableau.algStabMatrix, rkLobattoIIIB3] at h
  linarith

/-! ## NOT D(4) -/

/-- Lobatto IIIB 3-stage does NOT satisfy D(4): for j=1,
  ∑ᵢ bᵢ cᵢ³ aᵢ₁ = 1/6 ≠ 5/32 = b₁(1−c₁⁴)/4. -/
theorem rkLobattoIIIB3_not_D4 : ¬rkLobattoIIIB3.SatisfiesD 4 := by
  intro h
  have h4 := h 4 (by omega) le_rfl 1
  simp [rkLobattoIIIB3, Fin.sum_univ_three] at h4
  norm_num at h4

/-! ## Comparison: Lobatto III 3-Stage Family

| Property          | IIIA 3-stage        | IIIB 3-stage          | IIIC 3-stage            |
|-------------------|---------------------|-----------------------|-------------------------|
| Stages            | 3                   | 3                     | 3                       |
| Order             | 4                   | 4                     | 4                       |
| Row-sum           | ✓                   | ✓                     | ✓                       |
| R(z)              | GL2 Padé (2,2)      | GL2 Padé (2,2)        | (24+6z)/(24−18z+6z²−z³) |
| R(−∞)             | 1                   | 1                     | 0                       |
| L-stable          | ✗                   | ✗                     | ✓                       |
| Alg. stable       | ✗                   | ✗                     | ✓                       |
| Stiffly accurate  | ✓                   | ✗                     | ✓                       |
| C(q)              | C(3)                | C(1)                  | C(2)                    |
| D(r)              | D(1)                | D(3)                  | D(2)                    |
| Zero structure    | 1st row = 0         | last col = 0          | 1st col = const         |

IIIA and IIIB are **adjoint** to each other: A_IIIA + A_IIIB = 𝟙·bᵀ.
-/
