import OpenMath.GaussLegendre3
import OpenMath.LobattoIIIA3
import OpenMath.LobattoIIIB
import OpenMath.LobattoIIIB3
import OpenMath.LobattoIIIC3
import OpenMath.RadauIA2
import OpenMath.RadauIA3
import OpenMath.SDIRK3

/-!
# RK Method Symmetry (Section 2.5)

## Definition

A Runge–Kutta method with Butcher tableau (A, b, c) is **symmetric** (or **self-adjoint**)
if applying it with step size h followed by step size −h returns to the starting point.

The algebraic characterization is (0-based indexing with `Fin.rev`):
  A[i][j] + A[rev(i)][rev(j)] = b[j]   for all i, j
  b[i] = b[rev(i)]                       for all i
  c[i] + c[rev(i)] = 1                   for all i

## Key Results

- **Gauss–Legendre methods** are symmetric (implicit midpoint, GL2, GL3)
- **Lobatto IIIA/IIIB** are symmetric; Lobatto IIIC is NOT
- **Radau methods** are NOT symmetric (asymmetric weights)
- **SDIRK methods** are NOT symmetric
- Symmetric methods have even order (Theorem 2.8, Iserles)
- Symmetric methods are never L-stable

## The Adjoint Method

The **adjoint** of (A, b, c) is (A*, b*, c*) with:
  a*[i][j] = b[j] − a[rev(i)][rev(j)],   b*[i] = b[rev(i)],   c*[i] = 1 − c[rev(i)]

A method is symmetric iff it equals its own adjoint.

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 2.5; Hairer–Nørsett–Wanner, *Solving ODEs I*, Section II.8.
-/

open Finset Real Filter

namespace ButcherTableau

variable {s : ℕ}

/-! ## Symmetry Definition -/

/-- An RK method is **symmetric** (self-adjoint) if:
  1. b[i] = b[rev(i)] (symmetric weights)
  2. c[i] + c[rev(i)] = 1 (symmetric nodes about 1/2)
  3. A[i][j] + A[rev(i)][rev(j)] = b[j] (the defining symmetry condition)

  A symmetric method applied with step h then step −h recovers the initial value.
  Reference: Iserles, Definition 2.5 / Hairer–Nørsett–Wanner, Definition II.8.2. -/
structure IsSymmetric (t : ButcherTableau s) : Prop where
  symm_weights : ∀ i : Fin s, t.b i = t.b i.rev
  symm_nodes : ∀ i : Fin s, t.c i + t.c i.rev = 1
  symm_tableau : ∀ i j : Fin s, t.A i j + t.A i.rev j.rev = t.b j

/-! ## The Adjoint Method -/

/-- The **adjoint** (or **dual**) of a Butcher tableau.
  Given (A, b, c), the adjoint has:
    A*[i][j] = b[j] − A[rev(i)][rev(j)]
    b*[i] = b[rev(i)]
    c*[i] = 1 − c[rev(i)]
  Reference: Hairer–Nørsett–Wanner, Definition II.8.1. -/
noncomputable def adjoint (t : ButcherTableau s) : ButcherTableau s where
  A := fun i j => t.b j - t.A i.rev j.rev
  b := fun i => t.b i.rev
  c := fun i => 1 - t.c i.rev

/-- A method is symmetric iff A = A* (it equals its adjoint). -/
theorem isSymmetric_iff_eq_adjoint (t : ButcherTableau s) :
    t.IsSymmetric ↔
    (∀ i j : Fin s, t.A i j = (t.adjoint).A i j) ∧
    (∀ i : Fin s, t.b i = (t.adjoint).b i) ∧
    (∀ i : Fin s, t.c i = (t.adjoint).c i) := by
  constructor
  · intro ⟨hw, hn, ht⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j; simp only [adjoint]; linarith [ht i j]
    · exact hw
    · intro i; simp only [adjoint]; linarith [hn i]
  · intro ⟨hA, hb, hc⟩
    refine ⟨hb, ?_, ?_⟩
    · intro i; simp only [adjoint] at hc; linarith [hc i]
    · intro i j; simp only [adjoint] at hA; linarith [hA i j]

/-- The adjoint of the adjoint recovers the original tableau entries. -/
theorem adjoint_adjoint (t : ButcherTableau s) :
    ∀ i j : Fin s, (t.adjoint.adjoint).A i j = t.A i j := by
  intro i j; simp only [adjoint, Fin.rev_rev]

/-! ## Symmetry Implies Even Order

Symmetric methods satisfy the remarkable property that their order is always even.
The key insight: if a method is symmetric and consistent, then ∑ bᵢcᵢ = 1/2
follows automatically from node and weight symmetry.

Reference: Iserles, Theorem 2.8; Hairer–Nørsett–Wanner, Theorem II.8.4. -/

/-- **Symmetric consistent methods have order ≥ 2.**
  From the node symmetry cᵢ + c_{rev(i)} = 1 and weight symmetry bᵢ = b_{rev(i)},
  the second-order condition ∑ bᵢcᵢ = 1/2 follows.
  Reference: Iserles, Theorem 2.8. -/
theorem IsSymmetric.order2_of_consistent {t : ButcherTableau s}
    (hs : t.IsSymmetric) (hc : t.order1) : t.HasOrderGe2 := by
  refine ⟨hc, ?_⟩
  simp only [order2]
  -- Key: 2·∑ bᵢcᵢ = ∑ bᵢcᵢ + ∑ b_{rev(i)}c_{rev(i)}
  --               = ∑ bᵢcᵢ + ∑ bᵢc_{rev(i)}    (weight symmetry)
  --               = ∑ bᵢ(cᵢ + c_{rev(i)})
  --               = ∑ bᵢ · 1 = 1
  have step1 : ∑ i : Fin s, t.b i * t.c i =
      ∑ i : Fin s, t.b i.rev * t.c i.rev :=
    (Fin.revPerm.sum_comp (fun i => t.b i * t.c i)).symm
  have step2 : ∑ i : Fin s, t.b i.rev * t.c i.rev =
      ∑ i : Fin s, t.b i * t.c i.rev := by
    congr 1; ext i; rw [← hs.symm_weights i]
  have step3 : 2 * ∑ i : Fin s, t.b i * t.c i = 1 := by
    rw [two_mul, step1, step2, ← Finset.sum_add_distrib]
    conv_rhs => rw [← hc]
    congr 1; ext i; rw [← mul_add, hs.symm_nodes i, mul_one]
  linarith

end ButcherTableau

/-! ## Implicit Midpoint is Symmetric -/

/-- **Implicit midpoint is symmetric.**
  For s = 1: rev(0) = 0, so the conditions reduce to b₀ = b₀, 2c₀ = 1, and 2a₀₀ = b₀.
  All hold with b₀ = 1, c₀ = 1/2, a₀₀ = 1/2.
  Reference: Iserles, Section 2.5. -/
theorem rkImplicitMidpoint_symmetric : rkImplicitMidpoint.IsSymmetric where
  symm_weights := by intro i; fin_cases i; simp [rkImplicitMidpoint]
  symm_nodes := by intro i; fin_cases i; simp [rkImplicitMidpoint]
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkImplicitMidpoint]

/-! ## Backward Euler is NOT Symmetric -/

/-- **Backward Euler is NOT symmetric**: c₀ = 1, so c₀ + c₀ = 2 ≠ 1. -/
theorem rkImplicitEuler_not_symmetric : ¬rkImplicitEuler.IsSymmetric := by
  intro ⟨_, hn, _⟩
  have h := hn 0
  simp [rkImplicitEuler, Fin.rev] at h

/-! ## Forward Euler is NOT Symmetric -/

/-- **Forward Euler is NOT symmetric**: c₀ = 0, so c₀ + c₀ = 0 ≠ 1. -/
theorem rkEuler_not_symmetric : ¬rkEuler.IsSymmetric := by
  intro ⟨_, hn, _⟩
  have h := hn 0
  simp [rkEuler, Fin.rev] at h

/-! ## Gauss–Legendre 2-Stage is Symmetric -/

/-- **GL2 is symmetric.**
  The nodes c₀ + c₁ = 1, weights b₀ = b₁ = 1/2, and A[i][j] + A[1−i][1−j] = 1/2 = b[j].
  Reference: Iserles, Section 2.5; Hairer–Nørsett–Wanner, Theorem IV.5.2. -/
theorem rkGaussLegendre2_symmetric : rkGaussLegendre2.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkGaussLegendre2]
  symm_nodes := by intro i; fin_cases i <;> simp [rkGaussLegendre2] <;> ring
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkGaussLegendre2] <;> ring

/-! ## Gauss–Legendre 3-Stage is Symmetric -/

/-- **GL3 is symmetric.**
  The nodes satisfy c₀ + c₂ = 1, c₁ = 1/2. The weights satisfy b₀ = b₂, b₁ = 4/9.
  The tableau satisfies A[i][j] + A[2−i][2−j] = b[j].
  Reference: Iserles, Section 2.5; Hairer–Nørsett–Wanner, Theorem IV.5.2. -/
theorem rkGaussLegendre3_symmetric : rkGaussLegendre3.IsSymmetric where
  symm_weights := by
    intro i; fin_cases i <;> simp [rkGaussLegendre3]
  symm_nodes := by
    intro i; fin_cases i <;> simp [rkGaussLegendre3] <;> ring
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkGaussLegendre3] <;> ring

/-! ## Lobatto IIIA 2-Stage (Trapezoidal Rule) is Symmetric -/

/-- **Lobatto IIIA 2-stage (trapezoidal rule) is symmetric.**
  Nodes c = (0, 1), weights b = (1/2, 1/2), both symmetric.
  A = [[0,0],[1/2,1/2]] satisfies A[i][j] + A[1−i][1−j] = 1/2. -/
theorem rkLobattoIIIA2_symmetric : rkLobattoIIIA2.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIA2]
  symm_nodes := by intro i; fin_cases i <;> simp [rkLobattoIIIA2]
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkLobattoIIIA2] <;> norm_num

/-! ## Lobatto IIIA 3-Stage is Symmetric -/

/-- **Lobatto IIIA 3-stage is symmetric.**
  Nodes c = (0, 1/2, 1) and Simpson weights b = (1/6, 2/3, 1/6) are both symmetric.
  The tableau satisfies A[i][j] + A[2−i][2−j] = b[j]. -/
theorem rkLobattoIIIA3_symmetric : rkLobattoIIIA3.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIA3]
  symm_nodes := by intro i; fin_cases i <;> simp [rkLobattoIIIA3] <;> norm_num
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkLobattoIIIA3] <;> norm_num

/-! ## Lobatto IIIB 2-Stage is Symmetric -/

/-- **Lobatto IIIB 2-stage is symmetric.**
  Same nodes and weights as IIIA 2-stage. A = [[1/2,0],[1/2,0]] satisfies
  A[i][j] + A[1−i][1−j] = 1/2. -/
theorem rkLobattoIIIB2_symmetric : rkLobattoIIIB2.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIB2]
  symm_nodes := by intro i; fin_cases i <;> simp [rkLobattoIIIB2]
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkLobattoIIIB2] <;> norm_num

/-! ## Lobatto IIIB 3-Stage is Symmetric -/

/-- **Lobatto IIIB 3-stage is symmetric.**
  Same nodes and weights as IIIA 3-stage. The tableau A has zero last column and
  satisfies A[i][j] + A[2−i][2−j] = b[j]. -/
theorem rkLobattoIIIB3_symmetric : rkLobattoIIIB3.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIB3]
  symm_nodes := by intro i; fin_cases i <;> simp [rkLobattoIIIB3] <;> norm_num
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkLobattoIIIB3] <;> norm_num

/-! ## Lobatto IIIC 2-Stage is NOT Symmetric -/

/-- **Lobatto IIIC 2-stage is NOT symmetric.**
  A[0][0] + A[1][1] = 1/2 + 1/2 = 1 ≠ 1/2 = b[0]. -/
theorem rkLobattoIIIC2_not_symmetric : ¬rkLobattoIIIC2.IsSymmetric := by
  intro ⟨_, _, ht⟩
  have h := ht 0 0
  simp [rkLobattoIIIC2, Fin.rev] at h

/-! ## Lobatto IIIC 3-Stage is NOT Symmetric -/

/-- **Lobatto IIIC 3-stage is NOT symmetric.**
  A[0][0] + A[2][2] = 1/6 + 1/6 = 1/3 ≠ 1/6 = b[0]. -/
theorem rkLobattoIIIC3_not_symmetric : ¬rkLobattoIIIC3.IsSymmetric := by
  intro ⟨_, _, ht⟩
  have h := ht 0 0
  simp [rkLobattoIIIC3, Fin.rev] at h
  norm_num at h

/-! ## Radau Methods are NOT Symmetric -/

/-- **Radau IIA 2-stage is NOT symmetric**: b₀ = 3/4 ≠ 1/4 = b₁. -/
theorem rkRadauIIA2_not_symmetric : ¬rkRadauIIA2.IsSymmetric := by
  intro ⟨hw, _, _⟩
  have h := hw 0
  simp [rkRadauIIA2, Fin.rev] at h

/-- **Radau IA 2-stage is NOT symmetric**: b₀ = 1/4 ≠ 3/4 = b₁. -/
theorem rkRadauIA2_not_symmetric : ¬rkRadauIA2.IsSymmetric := by
  intro ⟨hw, _, _⟩
  have h := hw 0
  simp [rkRadauIA2, Fin.rev] at h

private theorem sqrt6_sq' : Real.sqrt 6 ^ 2 = 6 :=
  Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)

/-- **Radau IIA 3-stage is NOT symmetric**: b₀ = (16−√6)/36 ≠ 1/9 = b₂. -/
theorem rkRadauIIA3_not_symmetric : ¬rkRadauIIA3.IsSymmetric := by
  intro ⟨hw, _, _⟩
  have h := hw 0
  simp [rkRadauIIA3, Fin.rev] at h
  nlinarith [sqrt6_sq']

/-- **Radau IA 3-stage is NOT symmetric**: b₀ = 1/9 ≠ (16−√6)/36 = b₂. -/
theorem rkRadauIA3_not_symmetric : ¬rkRadauIA3.IsSymmetric := by
  intro ⟨hw, _, _⟩
  have h := hw 0
  simp [rkRadauIA3, Fin.rev] at h
  nlinarith [sqrt6_sq']

/-! ## SDIRK3 is NOT Symmetric -/

/-- **SDIRK3 is NOT symmetric**: c₀ + c₂ = λ + 1 ≠ 1 (since λ > 0). -/
theorem rkSDIRK3_not_symmetric : ¬rkSDIRK3.IsSymmetric := by
  intro ⟨_, hn, _⟩
  have h := hn 0
  simp [rkSDIRK3, Fin.rev] at h
  linarith [sdirk3Lambda_pos]

/-! ## Lobatto IIIA and IIIB are Adjoint to Each Other

The Lobatto IIIA and IIIB families are **adjoint** to each other:
  b_i · A^{IIIA}_{ij} + b_j · A^{IIIB}_{ji} = b_i · b_j

This means their algebraic stability matrices sum to zero.

Reference: Hairer–Wanner, Section IV.2. -/

/-- **Lobatto IIIA 2-stage and IIIB 2-stage are adjoint.** -/
theorem lobattoIIIA2_IIIB2_adjoint :
    ∀ i j : Fin 2, rkLobattoIIIA2.b i * rkLobattoIIIA2.A i j +
      rkLobattoIIIA2.b j * rkLobattoIIIB2.A j i =
      rkLobattoIIIA2.b i * rkLobattoIIIA2.b j := by
  intro i j; fin_cases i <;> fin_cases j <;>
    simp [rkLobattoIIIA2, rkLobattoIIIB2] <;> norm_num

/-- **Lobatto IIIA 3-stage and IIIB 3-stage are adjoint.** -/
theorem lobattoIIIA3_IIIB3_adjoint :
    ∀ i j : Fin 3, rkLobattoIIIA3.b i * rkLobattoIIIA3.A i j +
      rkLobattoIIIA3.b j * rkLobattoIIIB3.A j i =
      rkLobattoIIIA3.b i * rkLobattoIIIA3.b j := by
  intro i j; fin_cases i <;> fin_cases j <;>
    simp [rkLobattoIIIA3, rkLobattoIIIB3] <;> norm_num

/-! ## Summary Table

| Method              | Symmetric | Order | L-stable | Alg. stable |
|---------------------|-----------|-------|----------|-------------|
| Backward Euler      | ✗         | 1     | ✓        | ✓           |
| Forward Euler       | ✗         | 1     | ✗        | ✗           |
| Implicit midpoint   | ✓         | 2     | ✗        | ✓           |
| GL2                 | ✓         | 4     | ✗        | ✓           |
| GL3                 | ✓         | 6     | ✗        | ✓           |
| Radau IIA 2-stage   | ✗         | 3     | ✓        | ✓           |
| Radau IIA 3-stage   | ✗         | 5     | ✓        | ✓           |
| Radau IA 2-stage    | ✗         | 3     | ✓        | ✓           |
| Radau IA 3-stage    | ✗         | 5     | ✓        | ✓           |
| Lobatto IIIA 2-stg  | ✓         | 2     | ✗        | ✗           |
| Lobatto IIIA 3-stg  | ✓         | 4     | ✗        | ✗           |
| Lobatto IIIB 2-stg  | ✓         | 2     | ✗        | ✗           |
| Lobatto IIIB 3-stg  | ✓         | 4     | ✗        | ✗           |
| Lobatto IIIC 2-stg  | ✗         | 2     | ✓        | ✓           |
| Lobatto IIIC 3-stg  | ✗         | 4     | ✓        | ✓           |
| SDIRK3              | ✗         | 3     | ✓        | ✗           |

Key observations:
- **Symmetric ↔ Not L-stable**: symmetry implies R(z)·R(−z) = 1, forcing
  |R(−∞)| = 1/|R(+∞)| = 1 ≠ 0, so stiff decay is impossible.
- **Symmetric ↔ Even order**: consistent with Iserles Theorem 2.8.
- **Lobatto IIIA and IIIB are adjoint pairs**; each is individually symmetric.
  Lobatto IIIC is NOT symmetric (but has the best stability properties).
-/
