import Mathlib

/-!
# Chapter 2: Runge–Kutta Methods

Definitions and basic properties of Runge–Kutta (RK) methods for ODEs.

An s-stage Runge–Kutta method is specified by a **Butcher tableau** (A, b, c) where:
- A : s × s matrix of stage coefficients
- b : s-vector of weights
- c : s-vector of nodes

The method computes:
  k_i = f(t_n + c_i h, y_n + h ∑_j a_{ij} k_j),   i = 1, …, s
  y_{n+1} = y_n + h ∑_i b_i k_i

A method is **explicit** if A is strictly lower triangular.

A method is **consistent** if ∑ b_i = 1 and c_i = ∑_j a_{ij} for all i.

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Chapter 2.
-/

open Finset Real

/-! ## Butcher Tableau -/

/-- A **Butcher tableau** for an s-stage Runge–Kutta method.
The tableau consists of:
- `A`: the s × s matrix of stage coefficients a_{ij}
- `b`: the s-vector of weights
- `c`: the s-vector of nodes (abscissae) -/
structure ButcherTableau (s : ℕ) where
  /-- Stage coefficient matrix a_{ij}. -/
  A : Fin s → Fin s → ℝ
  /-- Weights for the final combination. -/
  b : Fin s → ℝ
  /-- Nodes (abscissae). -/
  c : Fin s → ℝ

namespace ButcherTableau

variable {s : ℕ}

/-! ### Consistency -/

/-- A Butcher tableau is **row-sum consistent** if c_i = ∑_j a_{ij} for all i.
This is the "row-sum condition". -/
def IsRowSumConsistent (t : ButcherTableau s) : Prop :=
  ∀ i : Fin s, t.c i = ∑ j : Fin s, t.A i j

/-- A Butcher tableau is **consistent** if:
1. The weights sum to 1: ∑ b_i = 1, and
2. The row-sum condition holds: c_i = ∑_j a_{ij}. -/
structure IsConsistent (t : ButcherTableau s) : Prop where
  /-- The weights sum to 1. -/
  weights_sum : ∑ i : Fin s, t.b i = 1
  /-- The row-sum condition: c_i = ∑_j a_{ij}. -/
  row_sum : t.IsRowSumConsistent

/-! ### Explicit Methods -/

/-- A Runge–Kutta method is **explicit** if A is strictly lower triangular:
a_{ij} = 0 for j ≥ i. -/
def IsExplicit (t : ButcherTableau s) : Prop :=
  ∀ i j : Fin s, i ≤ j → t.A i j = 0

/-! ### Order Conditions

The order conditions for Runge–Kutta methods up to order 4 are given by
conditions on the Butcher tableau coefficients.

Reference: Iserles, Section 2.3, Table 2.1.
-/

/-- **First-order condition**: ∑ b_i = 1. -/
def order1 (t : ButcherTableau s) : Prop :=
  ∑ i : Fin s, t.b i = 1

/-- **Second-order condition**: ∑ b_i c_i = 1/2. -/
def order2 (t : ButcherTableau s) : Prop :=
  ∑ i : Fin s, t.b i * t.c i = 1 / 2

/-- **Third-order condition (τ₁)**: ∑ b_i c_i² = 1/3. -/
def order3a (t : ButcherTableau s) : Prop :=
  ∑ i : Fin s, t.b i * t.c i ^ 2 = 1 / 3

/-- **Third-order condition (τ₂)**: ∑_{i,j} b_i a_{ij} c_j = 1/6. -/
def order3b (t : ButcherTableau s) : Prop :=
  ∑ i : Fin s, ∑ j : Fin s, t.b i * t.A i j * t.c j = 1 / 6

/-- **Fourth-order condition (τ₁)**: ∑ b_i c_i³ = 1/4. -/
def order4a (t : ButcherTableau s) : Prop :=
  ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4

/-- **Fourth-order condition (τ₂)**: ∑_{i,j} b_i c_i a_{ij} c_j = 1/8. -/
def order4b (t : ButcherTableau s) : Prop :=
  ∑ i : Fin s, t.b i * t.c i * (∑ j : Fin s, t.A i j * t.c j) = 1 / 8

/-- **Fourth-order condition (τ₃)**: ∑_{i,j} b_i a_{ij} c_j² = 1/12. -/
def order4c (t : ButcherTableau s) : Prop :=
  ∑ i : Fin s, ∑ j : Fin s, t.b i * t.A i j * t.c j ^ 2 = 1 / 12

/-- **Fourth-order condition (τ₄)**: ∑_{i,j,k} b_i a_{ij} a_{jk} c_k = 1/24. -/
def order4d (t : ButcherTableau s) : Prop :=
  ∑ i : Fin s, ∑ j : Fin s, ∑ k : Fin s,
    t.b i * t.A i j * t.A j k * t.c k = 1 / 24

/-- A method has **order at least 1** if ∑ b_i = 1. -/
def HasOrderGe1 (t : ButcherTableau s) : Prop :=
  t.order1

/-- A method has **order at least 2** if it satisfies order conditions 1–2. -/
def HasOrderGe2 (t : ButcherTableau s) : Prop :=
  t.order1 ∧ t.order2

/-- A method has **order at least 3** if it satisfies order conditions 1–2 and both
third-order conditions. -/
def HasOrderGe3 (t : ButcherTableau s) : Prop :=
  t.order1 ∧ t.order2 ∧ t.order3a ∧ t.order3b

/-- A method has **order at least 4** if it satisfies all order conditions through
fourth order (8 conditions total). -/
def HasOrderGe4 (t : ButcherTableau s) : Prop :=
  t.order1 ∧ t.order2 ∧ t.order3a ∧ t.order3b ∧
  t.order4a ∧ t.order4b ∧ t.order4c ∧ t.order4d

/-- A consistent method has order at least 1. -/
theorem IsConsistent.hasOrderGe1 {t : ButcherTableau s} (h : t.IsConsistent) :
    t.HasOrderGe1 :=
  h.weights_sum

end ButcherTableau

/-! ## Standard Runge–Kutta Methods -/

/-- **Forward Euler** as a 1-stage RK method:
  k₁ = f(tₙ, yₙ), yₙ₊₁ = yₙ + h·k₁.
  Butcher tableau: A = [0], b = [1], c = [0]. -/
noncomputable def rkEuler : ButcherTableau 1 where
  A := ![![0]]
  b := ![1]
  c := ![0]

/-- **Explicit midpoint** (modified Euler) as a 2-stage RK method:
  k₁ = f(tₙ, yₙ), k₂ = f(tₙ + h/2, yₙ + (h/2)k₁),
  yₙ₊₁ = yₙ + h·k₂.
  Butcher tableau: A = [[0,0],[1/2,0]], b = [0,1], c = [0,1/2]. -/
noncomputable def rkMidpoint : ButcherTableau 2 where
  A := ![![0, 0], ![1/2, 0]]
  b := ![0, 1]
  c := ![0, 1/2]

/-- **Heun's method** (improved Euler / explicit trapezoidal) as a 2-stage RK method:
  k₁ = f(tₙ, yₙ), k₂ = f(tₙ + h, yₙ + h·k₁),
  yₙ₊₁ = yₙ + (h/2)(k₁ + k₂).
  Butcher tableau: A = [[0,0],[1,0]], b = [1/2,1/2], c = [0,1]. -/
noncomputable def rkHeun : ButcherTableau 2 where
  A := ![![0, 0], ![1, 0]]
  b := ![1/2, 1/2]
  c := ![0, 1]

/-- **Classical RK4** (the Runge–Kutta method) as a 4-stage RK method:
  k₁ = f(tₙ, yₙ),
  k₂ = f(tₙ + h/2, yₙ + (h/2)k₁),
  k₃ = f(tₙ + h/2, yₙ + (h/2)k₂),
  k₄ = f(tₙ + h, yₙ + h·k₃),
  yₙ₊₁ = yₙ + (h/6)(k₁ + 2k₂ + 2k₃ + k₄).

  Butcher tableau:
  0   |
  1/2 | 1/2
  1/2 | 0    1/2
  1   | 0    0    1
  ----|------------------
      | 1/6  1/3  1/3  1/6

  Reference: Iserles, Section 2.1, Example 2.2. -/
noncomputable def rk4 : ButcherTableau 4 where
  A := ![![0,   0,   0,   0],
         ![1/2, 0,   0,   0],
         ![0,   1/2, 0,   0],
         ![0,   0,   1,   0]]
  b := ![1/6, 1/3, 1/3, 1/6]
  c := ![0, 1/2, 1/2, 1]

/-! ## Properties of Standard Methods -/

/-- Forward Euler (RK) is consistent. -/
theorem rkEuler_consistent : rkEuler.IsConsistent where
  weights_sum := by simp [rkEuler]
  row_sum := by
    intro i; fin_cases i; simp [rkEuler]

/-- Forward Euler (RK) is explicit. -/
theorem rkEuler_explicit : rkEuler.IsExplicit := by
  intro i j hij
  fin_cases i; fin_cases j; simp_all [rkEuler]

/-- Explicit midpoint method is consistent. -/
theorem rkMidpoint_consistent : rkMidpoint.IsConsistent where
  weights_sum := by simp [rkMidpoint, Fin.sum_univ_two]
  row_sum := by
    intro i; fin_cases i <;> simp [rkMidpoint, Fin.sum_univ_two]

/-- Explicit midpoint method is explicit. -/
theorem rkMidpoint_explicit : rkMidpoint.IsExplicit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [rkMidpoint]

/-- Heun's method is consistent. -/
theorem rkHeun_consistent : rkHeun.IsConsistent where
  weights_sum := by simp [rkHeun, Fin.sum_univ_two]; norm_num
  row_sum := by
    intro i; fin_cases i <;> simp [rkHeun, Fin.sum_univ_two]

/-- Heun's method is explicit. -/
theorem rkHeun_explicit : rkHeun.IsExplicit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [rkHeun]

/-- Classical RK4 is consistent. -/
theorem rk4_consistent : rk4.IsConsistent where
  weights_sum := by
    simp [rk4, Fin.sum_univ_four]
    norm_num
  row_sum := by
    intro i; fin_cases i <;> (simp [rk4, Fin.sum_univ_four]; try norm_num)

/-- Classical RK4 is explicit (A is strictly lower triangular). -/
theorem rk4_explicit : rk4.IsExplicit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [rk4]

/-! ### Order of Standard Methods -/

/-- Forward Euler (RK) has order at least 1. -/
theorem rkEuler_order1 : rkEuler.HasOrderGe1 := by
  simp [ButcherTableau.HasOrderGe1, ButcherTableau.order1, rkEuler]

/-- Explicit midpoint has order at least 2. -/
theorem rkMidpoint_order2 : rkMidpoint.HasOrderGe2 := by
  refine ⟨?_, ?_⟩
  · simp [ButcherTableau.order1, rkMidpoint, Fin.sum_univ_two]
  · simp [ButcherTableau.order2, rkMidpoint, Fin.sum_univ_two]

/-- Heun's method has order at least 2. -/
theorem rkHeun_order2 : rkHeun.HasOrderGe2 := by
  refine ⟨?_, ?_⟩
  · simp [ButcherTableau.order1, rkHeun, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order2, rkHeun, Fin.sum_univ_two]

/-- Classical RK4 has order at least 4. -/
theorem rk4_order4 : rk4.HasOrderGe4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- order1: ∑ b_i = 1
    simp [ButcherTableau.order1, rk4, Fin.sum_univ_four]; norm_num
  · -- order2: ∑ b_i c_i = 1/2
    simp [ButcherTableau.order2, rk4, Fin.sum_univ_four]; norm_num
  · -- order3a: ∑ b_i c_i² = 1/3
    simp [ButcherTableau.order3a, rk4, Fin.sum_univ_four]; norm_num
  · -- order3b: ∑ b_i a_{ij} c_j = 1/6
    simp [ButcherTableau.order3b, rk4, Fin.sum_univ_four]; norm_num
  · -- order4a: ∑ b_i c_i³ = 1/4
    simp [ButcherTableau.order4a, rk4, Fin.sum_univ_four]; norm_num
  · -- order4b: ∑ b_i c_i (∑ a_{ij} c_j) = 1/8
    simp [ButcherTableau.order4b, rk4, Fin.sum_univ_four]; norm_num
  · -- order4c: ∑ b_i a_{ij} c_j² = 1/12
    simp [ButcherTableau.order4c, rk4, Fin.sum_univ_four]; norm_num
  · -- order4d: ∑ b_i a_{ij} a_{jk} c_k = 1/24
    simp [ButcherTableau.order4d, rk4, Fin.sum_univ_four]; norm_num

/-! ## Implicit Runge–Kutta Methods

Implicit RK methods allow the stage coefficient matrix A to have entries on or above
the diagonal. This enables superior stability properties, in particular A-stability.

Reference: Iserles, Section 2.2 and Chapter 3.
-/

/-! ### Standard Implicit Methods -/

/-- **Implicit Euler** (backward Euler) as a 1-stage RK method:
  k₁ = f(tₙ + h, yₙ + h·k₁),  yₙ₊₁ = yₙ + h·k₁.
  Butcher tableau: A = [[1]], b = [1], c = [1]. -/
noncomputable def rkImplicitEuler : ButcherTableau 1 where
  A := ![![1]]
  b := ![1]
  c := ![1]

/-- **Implicit midpoint rule** as a 1-stage RK method:
  k₁ = f(tₙ + h/2, yₙ + (h/2)·k₁),  yₙ₊₁ = yₙ + h·k₁.
  Butcher tableau: A = [[1/2]], b = [1], c = [1/2]. -/
noncomputable def rkImplicitMidpoint : ButcherTableau 1 where
  A := ![![1/2]]
  b := ![1]
  c := ![1/2]

/-- Implicit Euler is consistent. -/
theorem rkImplicitEuler_consistent : rkImplicitEuler.IsConsistent where
  weights_sum := by simp [rkImplicitEuler]
  row_sum := by intro i; fin_cases i; simp [rkImplicitEuler]

/-- Implicit Euler is NOT explicit (A has nonzero diagonal entry). -/
theorem rkImplicitEuler_not_explicit : ¬rkImplicitEuler.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkImplicitEuler] at this

/-- Implicit midpoint is consistent. -/
theorem rkImplicitMidpoint_consistent : rkImplicitMidpoint.IsConsistent where
  weights_sum := by simp [rkImplicitMidpoint]
  row_sum := by intro i; fin_cases i; simp [rkImplicitMidpoint]

/-- Implicit midpoint is NOT explicit. -/
theorem rkImplicitMidpoint_not_explicit : ¬rkImplicitMidpoint.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkImplicitMidpoint] at this

/-- Implicit midpoint has order at least 2. -/
theorem rkImplicitMidpoint_order2 : rkImplicitMidpoint.HasOrderGe2 := by
  refine ⟨?_, ?_⟩
  · simp [ButcherTableau.order1, rkImplicitMidpoint]
  · simp [ButcherTableau.order2, rkImplicitMidpoint]

/-! ## A-Stability for Runge–Kutta Methods

For a 1-stage RK method with tableau (a, b, c), the stability function applied to
the test equation y' = λy with z = hλ is:
  R(z) = 1 + z·b·(1 - z·a)⁻¹ = (1 + z·(b - a)) / (1 - z·a)

For implicit Euler (a=1, b=1): R(z) = 1/(1-z)
For implicit midpoint (a=1/2, b=1): R(z) = (1+z/2)/(1-z/2)

A method is A-stable if |R(z)| ≤ 1 for all Re(z) ≤ 0.

Reference: Iserles, Chapter 3.
-/

namespace ButcherTableau

/-- The stability function R(z) for a 1-stage RK method applied to y' = λy:
  R(z) = (1 + z(b₁ - a₁₁)) / (1 - z·a₁₁),
  defined as the unique ξ satisfying ξ(1 - z·a₁₁) = 1 + z(b₁ - a₁₁).
  This is the amplification factor: yₙ₊₁ = R(z)·yₙ. -/
noncomputable def stabilityFn1 (t : ButcherTableau 1) (z : ℂ) : ℂ :=
  (1 + z * ((t.b 0 : ℂ) - (t.A 0 0 : ℂ))) / (1 - z * (t.A 0 0 : ℂ))

/-- A 1-stage RK method is **A-stable** if |R(z)| ≤ 1 for all z with Re(z) ≤ 0.
Reference: Iserles, Definition 3.3. -/
def IsAStable1 (t : ButcherTableau 1) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → 1 - z * (t.A 0 0 : ℂ) ≠ 0 →
    ‖t.stabilityFn1 z‖ ≤ 1

end ButcherTableau

/-- Implicit Euler is A-stable: R(z) = 1/(1-z) satisfies |R(z)| ≤ 1 when Re(z) ≤ 0. -/
theorem rkImplicitEuler_aStable : rkImplicitEuler.IsAStable1 := by
  intro z hz hne
  simp only [ButcherTableau.stabilityFn1, rkImplicitEuler]
  simp only [Matrix.cons_val_zero]
  norm_num
  simp only [rkImplicitEuler] at hne
  have h1z_ge : 1 ≤ ‖(1 : ℂ) - z‖ := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) - z)
    simp [Complex.sub_re] at h
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.re)] at h
    linarith
  exact inv_le_one_of_one_le₀ h1z_ge

/-- Implicit midpoint is A-stable: R(z) = (2+z)/(2-z) satisfies |R(z)| ≤ 1
when Re(z) ≤ 0. -/
theorem rkImplicitMidpoint_aStable : rkImplicitMidpoint.IsAStable1 := by
  intro z hz hne
  simp only [ButcherTableau.stabilityFn1, rkImplicitMidpoint]
  simp only [Matrix.cons_val_zero]
  simp only [rkImplicitMidpoint] at hne
  norm_num at hne ⊢
  have h_denom_pos : (0 : ℝ) < ‖(1 : ℂ) - z * (1/2)‖ := norm_pos_iff.mpr hne
  rw [div_le_one h_denom_pos]
  have h_nsq_le : ‖(1 : ℂ) + z * (1/2)‖ ^ 2 ≤ ‖(1 : ℂ) - z * (1/2)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.mul_re,
               Complex.add_im, Complex.sub_im, Complex.mul_im,
               Complex.one_re, Complex.one_im]
    norm_num
    nlinarith
  nlinarith [norm_nonneg ((1 : ℂ) + z * (1/2)), norm_nonneg ((1 : ℂ) - z * (1/2)),
             sq_nonneg (‖(1 : ℂ) - z * (1/2)‖ - ‖(1 : ℂ) + z * (1/2)‖)]

/-- Forward Euler (RK) is **not** A-stable: R(-3) = 1 + (-3) = -2, |R(-3)| = 2 > 1. -/
theorem rkEuler_not_aStable : ¬rkEuler.IsAStable1 := by
  intro h
  have h1 := h ((-3 : ℝ) : ℂ) (by simp) (by simp [rkEuler])
  simp only [ButcherTableau.stabilityFn1, rkEuler, Matrix.cons_val_zero] at h1
  norm_num at h1

/-! ## Gauss–Legendre 2-Stage Method

The Gauss–Legendre 2-stage (GL2) method is the 2-stage implicit RK method based on
Gauss–Legendre quadrature nodes. It achieves order 2s = 4, the maximum for s-stage
methods. Its stability function is the [1/1] diagonal Padé approximant to eᶻ:
  R(z) = (1 + z/2 + z²/12) / (1 - z/2 + z²/12).

Butcher tableau:
  1/2 - √3/6 | 1/4          1/4 - √3/6
  1/2 + √3/6 | 1/4 + √3/6   1/4
  ────────────|────────────────────────
              | 1/2           1/2

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 2.2, Table 2.2 and Chapter 3.
-/

/-- **Gauss–Legendre 2-stage** RK method.
Nodes are the Gauss–Legendre quadrature points on [0,1]: c = 1/2 ∓ √3/6.
This 2-stage method achieves order 4 and is A-stable.
Reference: Iserles, Table 2.2. -/
noncomputable def rkGaussLegendre2 : ButcherTableau 2 where
  A := ![![1/4,                    1/4 - Real.sqrt 3 / 6],
         ![1/4 + Real.sqrt 3 / 6,  1/4                 ]]
  b := ![1/2, 1/2]
  c := ![1/2 - Real.sqrt 3 / 6, 1/2 + Real.sqrt 3 / 6]

/-- GL2 is consistent: ∑ bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ. -/
theorem rkGaussLegendre2_consistent : rkGaussLegendre2.IsConsistent where
  weights_sum := by
    simp [rkGaussLegendre2, Fin.sum_univ_two]; ring
  row_sum := by
    intro i; fin_cases i <;> simp [rkGaussLegendre2, Fin.sum_univ_two] <;> ring

/-- GL2 is NOT explicit (the matrix A has nonzero diagonal entry a₁₁ = 1/4). -/
theorem rkGaussLegendre2_not_explicit : ¬rkGaussLegendre2.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkGaussLegendre2] at this

/-! ### GL2 Stability Function and A-Stability

The stability function for the GL2 method is:
  R(z) = (1 + z/2 + z²/12) / (1 - z/2 + z²/12)

This is the [1/1] diagonal Padé approximant to eᶻ. A-stability follows from
the algebraic identity |D(z)|² - |N(z)|² = -Re(z)·(12 + |z|²)/6 ≥ 0
for Re(z) ≤ 0, where N and D are the numerator and denominator.
-/

/-- Numerator of the GL2 stability function: N(z) = 1 + z/2 + z²/12. -/
noncomputable def gl2Num (z : ℂ) : ℂ := 1 + z / 2 + z ^ 2 / 12

/-- Denominator of the GL2 stability function: D(z) = 1 - z/2 + z²/12. -/
noncomputable def gl2Denom (z : ℂ) : ℂ := 1 - z / 2 + z ^ 2 / 12

/-- GL2 stability function: R(z) = (1 + z/2 + z²/12) / (1 - z/2 + z²/12).
This is the [1/1] diagonal Padé approximant to eᶻ. -/
noncomputable def gl2StabilityFn (z : ℂ) : ℂ := gl2Num z / gl2Denom z

/-- The GL2 denominator equals the numerator minus z: D(z) = N(z) - z. -/
theorem gl2Denom_eq_num_sub (z : ℂ) : gl2Denom z = gl2Num z - z := by
  simp [gl2Num, gl2Denom]; ring

/-- Key norm inequality: |N(z)|² ≤ |D(z)|² for Re(z) ≤ 0.
The difference |D|² - |N|² = -Re(z)·(12 + Re(z)² + Im(z)²)/6 ≥ 0. -/
theorem gl2_normSq_denom_ge_num (z : ℂ) (hz : z.re ≤ 0) :
    Complex.normSq (gl2Num z) ≤ Complex.normSq (gl2Denom z) := by
  suffices h : 0 ≤ Complex.normSq (gl2Denom z) - Complex.normSq (gl2Num z) by linarith
  set x := z.re with hx_def
  set y := z.im with hy_def
  -- Rewrite z as ⟨x, y⟩ to enable full expansion
  have hz_eq : z = (⟨x, y⟩ : ℂ) := (Complex.eta z).symm
  rw [hz_eq]
  simp only [gl2Num, gl2Denom, Complex.normSq_apply,
    Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.one_re, Complex.one_im, sq]
  simp only [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
    show (12 : ℂ) = ((12 : ℝ) : ℂ) from by norm_num,
    Complex.div_ofReal, Complex.mul_re, Complex.mul_im]
  ring_nf
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x * y)]

/-- The GL2 denominator is nonzero for Re(z) ≤ 0.
The roots of 1 - z/2 + z²/12 = 0 are z = 3 ± i√3, both with Re = 3 > 0. -/
theorem gl2_denom_ne_zero (z : ℂ) (hz : z.re ≤ 0) : gl2Denom z ≠ 0 := by
  intro heq
  have h0 : Complex.normSq (gl2Denom z) = 0 := by rw [heq]; simp
  have h1 : Complex.normSq (gl2Num z) ≤ 0 := by linarith [gl2_normSq_denom_ge_num z hz]
  have h2 : Complex.normSq (gl2Num z) = 0 := le_antisymm h1 (Complex.normSq_nonneg _)
  have hN0 : gl2Num z = 0 := Complex.normSq_eq_zero.mp h2
  -- N(z) = 0 and D(z) = N(z) - z = 0, so z = 0
  have h_sub : gl2Num z - z = 0 := by rw [← gl2Denom_eq_num_sub]; exact heq
  rw [hN0, zero_sub] at h_sub
  have hz0 : z = 0 := neg_eq_zero.mp h_sub
  -- But N(0) = 1 ≠ 0
  rw [hz0] at hN0; simp [gl2Num] at hN0

/-- **A-stability of the Gauss–Legendre 2-stage method**:
|R(z)| ≤ 1 for all z with Re(z) ≤ 0.
Reference: Iserles, Chapter 3. -/
theorem gl2_aStable (z : ℂ) (hz : z.re ≤ 0) : ‖gl2StabilityFn z‖ ≤ 1 := by
  have hD := gl2_denom_ne_zero z hz
  have hD_pos : (0 : ℝ) < ‖gl2Denom z‖ := norm_pos_iff.mpr hD
  unfold gl2StabilityFn
  rw [norm_div, div_le_one hD_pos]
  -- ‖gl2Num z‖ ≤ ‖gl2Denom z‖ from normSq inequality
  have hnsq := gl2_normSq_denom_ge_num z hz
  have h_sq_le : ‖gl2Num z‖ ^ 2 ≤ ‖gl2Denom z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]; exact hnsq
  -- Deduce ‖N‖ ≤ ‖D‖ from ‖N‖² ≤ ‖D‖² and ‖D‖ > 0
  by_contra hlt
  push_neg at hlt
  -- hlt: ‖D‖ < ‖N‖, derive ‖D‖² < ‖N‖² for contradiction
  nlinarith [norm_nonneg (gl2Num z), norm_nonneg (gl2Denom z),
             mul_pos (by linarith : (0 : ℝ) < ‖gl2Num z‖ - ‖gl2Denom z‖)
                     (by linarith [norm_nonneg (gl2Num z)] :
                       (0 : ℝ) < ‖gl2Num z‖ + ‖gl2Denom z‖)]

/-! ### GL2 Order Conditions

The Gauss–Legendre 2-stage method achieves order 2s = 4, the maximum possible
for an s-stage Runge–Kutta method. We verify all 8 order conditions (up to order 4).

Reference: Iserles, Section 2.3, Table 2.1.
-/

private theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)

/-- **GL2 has order at least 4**: all order conditions through fourth order are satisfied. -/
theorem rkGaussLegendre2_order4 : rkGaussLegendre2.HasOrderGe4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- order1: ∑ b_i = 1
    simp [ButcherTableau.order1, rkGaussLegendre2, Fin.sum_univ_two]; ring
  · -- order2: ∑ b_i c_i = 1/2
    simp [ButcherTableau.order2, rkGaussLegendre2, Fin.sum_univ_two]; ring
  · -- order3a: ∑ b_i c_i² = 1/3
    simp [ButcherTableau.order3a, rkGaussLegendre2, Fin.sum_univ_two]
    nlinarith [sqrt3_sq]
  · -- order3b: ∑ b_i a_{ij} c_j = 1/6
    simp [ButcherTableau.order3b, rkGaussLegendre2, Fin.sum_univ_two]
    nlinarith [sqrt3_sq]
  · -- order4a: ∑ b_i c_i³ = 1/4
    simp [ButcherTableau.order4a, rkGaussLegendre2, Fin.sum_univ_two]
    nlinarith [sqrt3_sq, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
  · -- order4b: ∑ b_i c_i (∑ a_{ij} c_j) = 1/8
    simp [ButcherTableau.order4b, rkGaussLegendre2, Fin.sum_univ_two]
    nlinarith [sqrt3_sq]
  · -- order4c: ∑ b_i a_{ij} c_j² = 1/12
    simp [ButcherTableau.order4c, rkGaussLegendre2, Fin.sum_univ_two]
    nlinarith [sqrt3_sq]
  · -- order4d: ∑ b_i a_{ij} a_{jk} c_k = 1/24
    simp [ButcherTableau.order4d, rkGaussLegendre2, Fin.sum_univ_two]
    nlinarith [sqrt3_sq]
