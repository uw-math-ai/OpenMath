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
