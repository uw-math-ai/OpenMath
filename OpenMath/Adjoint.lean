import OpenMath.Symmetry

/-!
# Algebraic Adjoint Theory for Runge–Kutta Methods

## Self-Adjoint Methods

A Runge–Kutta method is **self-adjoint** (in the algebraic sense) if
  bᵢ aᵢⱼ + bⱼ aⱼᵢ = bᵢ bⱼ   for all i, j

This is equivalent to the algebraic stability matrix M being identically zero.
Self-adjoint methods are automatically algebraically stable (since M = 0 is PSD).

## Adjoint Pairs

Two RK methods form an **adjoint pair** if they share the same weights and
  bᵢ a'ᵢⱼ + bⱼ aⱼᵢ = bᵢ bⱼ   for all i, j

The adjoint pair relation is symmetric: if (t, t') is an adjoint pair, so is (t', t).

## Key Results

- Self-adjoint methods are algebraically stable
- Gauss methods (GL2, GL3) have M = 0 (self-adjoint)
- Forward Euler ↔ Backward Euler form an adjoint pair
- Lobatto IIIA ↔ IIIB form adjoint pairs

Reference: Hairer–Nørsett–Wanner, *Solving ODEs I*, Section II.8;
Iserles, *A First Course in the Numerical Analysis of Differential Equations*, Section 4.2.
-/

open Finset Real

namespace ButcherTableau

variable {s : ℕ}

/-! ## Self-Adjoint Definition -/

/-- A RK method is **self-adjoint** (algebraically) if
  bᵢ aᵢⱼ + bⱼ aⱼᵢ = bᵢ bⱼ for all i, j.
  Equivalently, the algebraic stability matrix M is identically zero.
  Reference: Hairer–Nørsett–Wanner, Section II.8. -/
def IsSelfAdjoint (t : ButcherTableau s) : Prop :=
  ∀ i j : Fin s, t.b i * t.A i j + t.b j * t.A j i = t.b i * t.b j

/-- Self-adjoint is equivalent to the algebraic stability matrix being zero. -/
theorem isSelfAdjoint_iff_algStabMatrix_zero (t : ButcherTableau s) :
    t.IsSelfAdjoint ↔ ∀ i j : Fin s, t.algStabMatrix i j = 0 := by
  simp only [IsSelfAdjoint, algStabMatrix]
  constructor
  · intro h i j; linarith [h i j]
  · intro h i j; linarith [h i j]

/-- Self-adjoint methods are algebraically stable (M = 0 is trivially PSD). -/
theorem IsSelfAdjoint.toAlgStable (t : ButcherTableau s)
    (hsa : t.IsSelfAdjoint) (hw : t.HasNonNegWeights) : t.IsAlgStable where
  nonneg_weights := hw
  posdef_M := by
    intro v
    have hM : ∀ i j, t.algStabMatrix i j = 0 :=
      (isSelfAdjoint_iff_algStabMatrix_zero t).mp hsa
    simp only [hM, mul_zero]; simp

/-! ## Adjoint Pairs -/

/-- Two s-stage RK methods form an **adjoint pair** if they share the same weights
  and their coefficient matrices satisfy:
    bᵢ a'ᵢⱼ + bⱼ aⱼᵢ = bᵢ bⱼ   for all i, j
  This is the algebraic adjoint relation involving the "transpose" of A.
  Reference: Hairer–Nørsett–Wanner, Section II.8 / Iserles, Section 4.2. -/
structure IsAdjointPair (t t' : ButcherTableau s) : Prop where
  same_weights : ∀ i : Fin s, t.b i = t'.b i
  adjoint_rel : ∀ i j : Fin s, t.b i * t'.A i j + t.b j * t.A j i = t.b i * t.b j

/-- The adjoint pair relation is symmetric. -/
theorem IsAdjointPair.symm {t t' : ButcherTableau s}
    (h : IsAdjointPair t t') : IsAdjointPair t' t where
  same_weights := fun i => (h.same_weights i).symm
  adjoint_rel := by
    intro i j
    -- From h.adjoint_rel at (j, i): b[j]·A'[j][i] + b[i]·A[i][j] = b[j]·b[i]
    have h1 := h.adjoint_rel j i
    -- We need: b'[i]·A[i][j] + b'[j]·A'[j][i] = b'[i]·b'[j]
    -- Since b' = b: b[i]·A[i][j] + b[j]·A'[j][i] = b[i]·b[j]
    rw [← h.same_weights i, ← h.same_weights j]
    linarith

/-- A method is self-adjoint iff it forms an adjoint pair with itself. -/
theorem isSelfAdjoint_iff_adjointPair_self (t : ButcherTableau s) :
    t.IsSelfAdjoint ↔ IsAdjointPair t t :=
  ⟨fun h => ⟨fun _ => rfl, h⟩, fun h => h.adjoint_rel⟩

/-- An adjoint pair shares the same consistency property: if both are consistent,
  then both have the same weight sum. -/
theorem IsAdjointPair.consistent_iff {t t' : ButcherTableau s}
    (h : IsAdjointPair t t') : t.order1 ↔ t'.order1 := by
  simp only [order1]
  have hsame : ∑ i, t'.b i = ∑ i, t.b i :=
    Finset.sum_congr rfl (fun i _ => (h.same_weights i).symm)
  constructor <;> intro h1 <;> linarith

end ButcherTableau

/-! ## Concrete Self-Adjoint Verifications -/

/-! ### Implicit Midpoint is Self-Adjoint -/

/-- **Implicit midpoint is self-adjoint**: M = 0. -/
theorem rkImplicitMidpoint_selfAdjoint : rkImplicitMidpoint.IsSelfAdjoint := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [rkImplicitMidpoint] <;> ring

/-- Implicit midpoint algebraic stability follows from self-adjointness. -/
theorem rkImplicitMidpoint_algStable' : rkImplicitMidpoint.IsAlgStable :=
  rkImplicitMidpoint_selfAdjoint.toAlgStable _
    (by intro i; fin_cases i; simp [rkImplicitMidpoint])

/-! ### GL2 is Self-Adjoint -/

/-- **GL2 is self-adjoint**: the algebraic stability matrix is identically zero.
  This follows from the existing `rkGaussLegendre2_algStabMatrix_zero` result. -/
theorem rkGaussLegendre2_selfAdjoint : rkGaussLegendre2.IsSelfAdjoint := by
  rw [ButcherTableau.isSelfAdjoint_iff_algStabMatrix_zero]
  exact rkGaussLegendre2_algStabMatrix_zero

/-! ### GL3 is Self-Adjoint -/

private theorem sqrt15_sq' : Real.sqrt 15 ^ 2 = 15 :=
  Real.sq_sqrt (by norm_num : (15 : ℝ) ≥ 0)

/-- **GL3 algebraic stability matrix is identically zero.** This is a stronger
  result than algebraic stability: Gauss methods are self-adjoint, meaning
  M_{ij} = b_i a_{ij} + b_j a_{ji} - b_i b_j = 0 for all i, j.
  Reference: Hairer–Nørsett–Wanner, Theorem IV.5.2 (Gauss methods satisfy D(s)). -/
theorem rkGaussLegendre3_algStabMatrix_zero (i j : Fin 3) :
    rkGaussLegendre3.algStabMatrix i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [ButcherTableau.algStabMatrix, rkGaussLegendre3] <;> nlinarith [sqrt15_sq']

/-- **GL3 is self-adjoint**: M = 0. -/
theorem rkGaussLegendre3_selfAdjoint : rkGaussLegendre3.IsSelfAdjoint := by
  rw [ButcherTableau.isSelfAdjoint_iff_algStabMatrix_zero]
  exact rkGaussLegendre3_algStabMatrix_zero

/-- GL3 algebraic stability follows from self-adjointness (alternative proof). -/
theorem rkGaussLegendre3_algStable' : rkGaussLegendre3.IsAlgStable :=
  rkGaussLegendre3_selfAdjoint.toAlgStable _
    rkGaussLegendre3_nonNegWeights

/-! ### Lobatto IIIA/IIIB 2-stage are NOT Self-Adjoint

The 2-stage Lobatto IIIA (trapezoidal rule) has M₀₀ = −1/4 ≠ 0, so it is not self-adjoint.
Similarly, Lobatto IIIB 2-stage has M₀₀ = 1/4 ≠ 0. -/

/-- **Lobatto IIIA 2-stage is NOT self-adjoint**: M₀₀ = −1/4 ≠ 0. -/
theorem rkLobattoIIIA2_not_selfAdjoint : ¬rkLobattoIIIA2.IsSelfAdjoint := by
  intro h; have := h 0 0; simp [rkLobattoIIIA2] at this

/-- **Lobatto IIIB 2-stage is NOT self-adjoint**: M₀₀ = 1/4 ≠ 0. -/
theorem rkLobattoIIIB2_not_selfAdjoint : ¬rkLobattoIIIB2.IsSelfAdjoint := by
  intro h; have := h 0 0; simp [rkLobattoIIIB2] at this

/-! ### Lobatto IIIC is NOT Self-Adjoint

Lobatto IIIC methods are algebraically stable (M is PSD) but NOT self-adjoint
(M ≠ 0). This distinguishes self-adjointness from algebraic stability. -/

/-- **Lobatto IIIC 3-stage is NOT self-adjoint**: M₀₀ = 1/36 ≠ 0.
  Compare with `rkLobattoIIIC3_algStable` which shows M ≥ 0. -/
theorem rkLobattoIIIC3_not_selfAdjoint : ¬rkLobattoIIIC3.IsSelfAdjoint := by
  rw [ButcherTableau.isSelfAdjoint_iff_algStabMatrix_zero]
  intro h
  have := h 0 0
  simp [ButcherTableau.algStabMatrix, rkLobattoIIIC3] at this

/-! ## Concrete Adjoint Pair Verifications -/

/-! ### Forward Euler ↔ Backward Euler -/

/-- **Forward Euler and Backward Euler form an adjoint pair.**
  Both have b = [1], so b₀·A_FE[0][0] + b₀·A_BE[0][0] = 1·0 + 1·1 = 1 = b₀·b₀. -/
theorem euler_adjointPair : ButcherTableau.IsAdjointPair rkEuler rkImplicitEuler where
  same_weights := by intro i; fin_cases i; simp [rkEuler, rkImplicitEuler]
  adjoint_rel := by
    intro i j; fin_cases i <;> fin_cases j <;>
      simp [rkEuler, rkImplicitEuler] <;> ring

/-- Forward Euler is NOT self-adjoint. -/
theorem rkEuler_not_selfAdjoint : ¬rkEuler.IsSelfAdjoint := by
  intro h
  have := h 0 0
  simp [rkEuler] at this

/-- Backward Euler is NOT self-adjoint. -/
theorem rkImplicitEuler_not_selfAdjoint : ¬rkImplicitEuler.IsSelfAdjoint := by
  intro h
  have := h 0 0
  simp [rkImplicitEuler] at this

/-! ### Lobatto IIIA ↔ IIIB Adjoint Pairs -/

/-- **Lobatto IIIA 2-stage and IIIB 2-stage form an adjoint pair.** -/
theorem lobattoIIIA2_IIIB2_adjointPair :
    ButcherTableau.IsAdjointPair rkLobattoIIIA2 rkLobattoIIIB2 where
  same_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIA2, rkLobattoIIIB2]
  adjoint_rel := by
    intro i j; fin_cases i <;> fin_cases j <;>
      simp [rkLobattoIIIA2, rkLobattoIIIB2] <;> norm_num

/-- **Lobatto IIIA 3-stage and IIIB 3-stage form an adjoint pair.**
  This is the fundamental adjoint relationship:
    A_IIIA + diag(b)⁻¹ · A_IIIB^T · diag(b) = 𝟙·b^T
  Reference: Hairer–Wanner, Section IV.2. -/
theorem lobattoIIIA3_IIIB3_adjointPair :
    ButcherTableau.IsAdjointPair rkLobattoIIIA3 rkLobattoIIIB3 where
  same_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIA3, rkLobattoIIIB3]
  adjoint_rel := by
    intro i j; fin_cases i <;> fin_cases j <;>
      simp [rkLobattoIIIA3, rkLobattoIIIB3] <;> norm_num

/-! ### Lobatto IIIA/IIIB 3-stage are NOT Self-Adjoint

Symmetric (Nørsett) does NOT imply self-adjoint. The symmetry condition uses the
rev permutation: A[i][j] + A[rev(i)][rev(j)] = b[j], while self-adjointness uses
the transpose: b[i]·A[i][j] + b[j]·A[j][i] = b[i]·b[j]. These coincide for Gauss
methods but not in general. -/

/-- **Lobatto IIIA 3-stage is NOT self-adjoint**: M₀₀ = −1/36 ≠ 0. -/
theorem rkLobattoIIIA3_not_selfAdjoint : ¬rkLobattoIIIA3.IsSelfAdjoint := by
  intro h
  have := h 0 0
  simp [rkLobattoIIIA3] at this

/-- **Lobatto IIIB 3-stage is NOT self-adjoint**: M₂₂ = −1/36 ≠ 0. -/
theorem rkLobattoIIIB3_not_selfAdjoint : ¬rkLobattoIIIB3.IsSelfAdjoint := by
  intro h
  have := h 2 2
  simp [rkLobattoIIIB3] at this

/-! ### Radau Methods are NOT Self-Adjoint -/

private theorem sqrt6_sq' : Real.sqrt 6 ^ 2 = 6 :=
  Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)

/-- **Radau IIA 3-stage is NOT self-adjoint**: the algebraic stability matrix is
  strictly positive definite (not zero). -/
theorem rkRadauIIA3_not_selfAdjoint : ¬rkRadauIIA3.IsSelfAdjoint := by
  rw [ButcherTableau.isSelfAdjoint_iff_algStabMatrix_zero]
  intro h
  have := h 0 0
  simp [ButcherTableau.algStabMatrix, rkRadauIIA3] at this
  nlinarith [sqrt6_sq']

/-! ## Structural Theorems -/

namespace ButcherTableau

/-- **Adjoint pairs preserve the weight-sum condition (order 1).**
  If one method in an adjoint pair is consistent, so is the other. -/
theorem IsAdjointPair.order1_of_order1 {t t' : ButcherTableau s}
    (h : IsAdjointPair t t') (h1 : t.order1) : t'.order1 := by
  rw [← h.consistent_iff]; exact h1

/-- **Self-adjoint implies D(1) for methods with positive weights.**
  From b[i]·A[i][j] + b[j]·A[j][i] = b[i]·b[j], sum over i:
  (∑ᵢ bᵢ aᵢⱼ) + bⱼ · (∑ᵢ aⱼᵢ) = bⱼ · (∑ᵢ bᵢ)
  If row-sum consistent (∑ᵢ aⱼᵢ = cⱼ) and ∑ bᵢ = 1:
  (∑ᵢ bᵢ aᵢⱼ) + bⱼ · cⱼ = bⱼ
  i.e., ∑ᵢ bᵢ aᵢⱼ = bⱼ(1 − cⱼ), which is D(1). -/
theorem IsSelfAdjoint.satisfiesD1 {t : ButcherTableau s}
    (hsa : t.IsSelfAdjoint) (hc : t.IsConsistent) : t.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; simp
  -- From self-adjoint: ∑ᵢ (bᵢ·aᵢⱼ + bⱼ·aⱼᵢ) = ∑ᵢ bᵢ·bⱼ
  have h_sum : ∑ i : Fin s, (t.b i * t.A i j + t.b j * t.A j i) =
      ∑ i : Fin s, t.b i * t.b j := by
    congr 1; ext i; exact hsa i j
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at h_sum
  rw [← hc.row_sum j, hc.weights_sum] at h_sum
  -- h_sum: (∑ᵢ bᵢ aᵢⱼ) + bⱼ · cⱼ = 1 · bⱼ
  nlinarith

/-- **In an adjoint pair, the adjoint D(1)-like identity holds.**
  If (t, t') is an adjoint pair and t is consistent, then
  ∑ᵢ bᵢ a'ᵢⱼ = bⱼ(1 − cⱼ) for all j.
  This is the "complementary" D condition for the adjoint method.
  Reference: Hairer–Wanner, Section IV.2. -/
theorem IsAdjointPair.adjoint_D1_sum {t t' : ButcherTableau s}
    (h : IsAdjointPair t t') (hc : t.IsConsistent) :
    ∀ j : Fin s, ∑ i : Fin s, t.b i * t'.A i j = t.b j * (1 - t.c j) := by
  intro j
  -- Sum adjoint_rel over i: ∑ᵢ (bᵢ·a'ᵢⱼ + bⱼ·aⱼᵢ) = ∑ᵢ bᵢ·bⱼ
  have h_sum : ∑ i : Fin s, (t.b i * t'.A i j + t.b j * t.A j i) =
      ∑ i : Fin s, t.b i * t.b j := by
    congr 1; ext i; exact h.adjoint_rel i j
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at h_sum
  -- h_sum: (∑ᵢ bᵢ a'ᵢⱼ) + bⱼ · cⱼ = 1 · bⱼ
  rw [← hc.row_sum j, hc.weights_sum] at h_sum
  nlinarith

/-- **Adjoint row sum identity**: For an adjoint pair (t, t') with ∑ bᵢ = 1,
  the row sums of A' satisfy: bᵢ · (∑ⱼ A'ᵢⱼ) = bᵢ − ∑ⱼ bⱼ · Aⱼᵢ.
  This determines the adjoint method's nodes from the original method's column sums. -/
theorem IsAdjointPair.adjoint_row_sum {t t' : ButcherTableau s}
    (h : IsAdjointPair t t') (h1 : t.order1) :
    ∀ i : Fin s, t.b i * ∑ j : Fin s, t'.A i j =
      t.b i - ∑ j : Fin s, t.b j * t.A j i := by
  intro i
  have h_sum : ∑ j : Fin s, (t.b i * t'.A i j + t.b j * t.A j i) =
      ∑ j : Fin s, t.b i * t.b j := by
    congr 1; ext j; exact h.adjoint_rel i j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h_sum
  rw [h1] at h_sum; linarith

/-- **Adjoint nodes theorem**: If (t, t') is an adjoint pair, t is consistent,
  t satisfies D(1), and t' is row-sum consistent, then b[i]·c'[i] = b[i]·c[i].
  In particular, when all weights are positive, c' = c (the adjoint has the same nodes).

  **Proof**: Summing the adjoint relation b[i]·A'[i][j] + b[j]·A[j][i] = b[i]·b[j]
  over j gives b[i]·c'[i] = b[i] − ∑ⱼ bⱼ·Aⱼᵢ. By D(1), the sum equals b[i]·(1−c[i]),
  so b[i]·c'[i] = b[i]·c[i].

  **Example**: GL2 is self-adjoint, so trivially c' = c.
  Lobatto IIIA ↔ IIIB share nodes [0, 1/2, 1] — this is because IIIA satisfies D(1).
  Forward Euler does NOT satisfy D(1), so its adjoint (backward Euler) has c' = [1] ≠ c = [0].

  Reference: Hairer–Nørsett–Wanner, Section II.8. -/
theorem IsAdjointPair.adjoint_nodes_eq {t t' : ButcherTableau s}
    (h : IsAdjointPair t t') (hc : t.IsConsistent) (hD : t.SatisfiesD 1)
    (hc' : t'.IsRowSumConsistent) :
    ∀ i : Fin s, t.b i * t'.c i = t.b i * t.c i := by
  intro i
  -- D(1): ∑ⱼ bⱼ·Aⱼᵢ = bᵢ·(1−cᵢ)
  have hD1 : ∑ j : Fin s, t.b j * t.A j i = t.b i * (1 - t.c i) := by
    have h' := hD 1 (by omega) le_rfl i; simpa using h'
  -- Sum the adjoint relation over j
  have h_sum : ∑ j : Fin s, (t.b i * t'.A i j + t.b j * t.A j i) =
      ∑ j : Fin s, t.b i * t.b j := by
    congr 1; ext j; exact h.adjoint_rel i j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h_sum
  -- h_sum: bᵢ·(∑ⱼ A'ᵢⱼ) + (∑ⱼ bⱼ·Aⱼᵢ) = bᵢ·(∑ⱼ bⱼ)
  rw [hc.weights_sum, hD1] at h_sum
  -- h_sum: bᵢ·(∑ⱼ A'ᵢⱼ) + bᵢ·(1−cᵢ) = bᵢ
  -- So bᵢ·(∑ⱼ A'ᵢⱼ) = bᵢ·cᵢ
  -- And bᵢ·c'ᵢ = bᵢ·(∑ⱼ A'ᵢⱼ) by row-sum consistency
  have hc'i : t.b i * t'.c i = t.b i * ∑ j : Fin s, t'.A i j := by
    congr 1; exact hc' i
  linarith

/-- **Adjoint involution** (weighted form): If (t, t') and (t', t'') are adjoint pairs,
  then bᵢ·A''ᵢⱼ = bᵢ·Aᵢⱼ for all i, j. When all weights are positive, A'' = A,
  so the adjoint operation is an involution (taking the adjoint twice recovers the original).

  **Proof**: From (t, t'): bⱼ·A'ⱼᵢ = bⱼ·bᵢ − bᵢ·Aᵢⱼ.
  From (t', t''): bᵢ·A''ᵢⱼ = bᵢ·bⱼ − bⱼ·A'ⱼᵢ = bᵢ·Aᵢⱼ.

  Reference: Hairer–Nørsett–Wanner, Section II.8. -/
theorem IsAdjointPair.involution_bA {t t' t'' : ButcherTableau s}
    (h1 : IsAdjointPair t t') (h2 : IsAdjointPair t' t'') :
    ∀ i j : Fin s, t.b i * t''.A i j = t.b i * t.A i j := by
  intro i j
  -- From h1 at (j, i): bⱼ·A'ⱼᵢ + bᵢ·Aᵢⱼ = bⱼ·bᵢ
  have h1ji := h1.adjoint_rel j i
  -- From h2 at (i, j): b'ᵢ·A''ᵢⱼ + b'ⱼ·A'ⱼᵢ = b'ᵢ·b'ⱼ
  -- Rewrite b' = b (since h1.same_weights)
  have h2ij : t.b i * t''.A i j + t.b j * t'.A j i = t.b i * t.b j := by
    have := h2.adjoint_rel i j
    rwa [← h1.same_weights i, ← h1.same_weights j] at this
  -- From h1ji: bⱼ·A'ⱼᵢ = bⱼ·bᵢ − bᵢ·Aᵢⱼ
  -- Substituting into h2ij: bᵢ·A''ᵢⱼ + (bⱼ·bᵢ − bᵢ·Aᵢⱼ) = bᵢ·bⱼ
  linarith

end ButcherTableau

/-! ## Summary Table

| Method              | Self-Adjoint (M=0) | Alg. Stable (M≥0) | Symmetric (Nørsett) |
|---------------------|:------------------:|:------------------:|:-------------------:|
| Forward Euler       | ✗                  | ✗                  | ✗                   |
| Backward Euler      | ✗                  | ✓                  | ✗                   |
| Implicit midpoint   | ✓                  | ✓                  | ✓                   |
| GL2                 | ✓                  | ✓                  | ✓                   |
| GL3                 | ✓                  | ✓                  | ✓                   |
| Lobatto IIIA 2-stg  | ✗                  | ✗                  | ✓                   |
| Lobatto IIIA 3-stg  | ✗                  | ✗                  | ✓                   |
| Lobatto IIIB 2-stg  | ✗                  | ✗                  | ✓                   |
| Lobatto IIIB 3-stg  | ✗                  | ✗                  | ✓                   |
| Lobatto IIIC 3-stg  | ✗                  | ✓                  | ✗                   |
| Radau IIA 3-stg     | ✗                  | ✓                  | ✗                   |

Key observations:
- **Self-adjoint ⊂ Alg. stable** but the converse fails (backward Euler, IIIC, Radau IIA)
- **Symmetric ⊄ Self-adjoint**: Lobatto IIIA/IIIB are symmetric but NOT self-adjoint
  (the rev-permutation symmetry differs from transpose-based self-adjointness)
- **Gauss methods are both symmetric AND self-adjoint** (special property)
- **Adjoint pairs**: (Forward Euler, Backward Euler), (IIIA, IIIB)
-/
