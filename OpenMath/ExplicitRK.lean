import OpenMath.Symmetry
import OpenMath.StiffAccuracy

/-!
# Explicit Runge–Kutta Methods: Comprehensive Analysis

Complete analysis of all four explicit RK methods in the library, covering:
- Simplifying assumptions B(p), C(q), D(r) with tight bounds
- Exact order bounds (positive and negative)
- Symmetry (all explicit methods are NOT symmetric)
- Stiff accuracy (all explicit methods are NOT stiffly accurate)
- Stability functions and non-A-stability
- Order derivation via the B+C collocation framework

## Methods analyzed

| Method       | B(p) | C(q) | D(r) | Order | Symmetric | Stiffly Acc. |
|:------------ |:----:|:----:|:----:|:-----:|:---------:|:------------:|
| Forward Euler| 1    | 1    | 0    | 1     | No        | No           |
| Explicit mid | 2    | 1    | 0    | 2     | No        | No           |
| Heun         | 2    | 1    | 1    | 2     | No        | No           |
| Classical RK4| 4    | 1    | 1    | 4     | No        | No           |

## Key findings

- Heun and RK4 satisfy D(1) despite being explicit.
- No explicit method satisfies C(2): for c₁ = 0, the C(2) condition at stage 2 fails.
- The quadrature order (B) matches the classical order for all explicit methods.
- All explicit methods have polynomial stability functions, so none are A-stable.
- RK4's stability function is exactly the 4th Taylor polynomial of eᶻ.

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Chapters 2 and 4.
-/

open Finset Real

namespace ButcherTableau

/-! ## Forward Euler: B/C/D, Exact Order, Symmetry, Stiff Accuracy -/

section ForwardEuler

/-- Forward Euler satisfies B(1). -/
theorem rkEuler_B1 : rkEuler.SatisfiesB 1 := by
  intro k hk1 hk2
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; simp [rkEuler]

/-- Forward Euler satisfies C(1): the row-sum condition c₁ = a₁₁ = 0. -/
theorem rkEuler_C1 : rkEuler.SatisfiesC 1 := by
  rw [satisfiesC_one_iff]
  exact rkEuler_consistent.row_sum

/-- Forward Euler does NOT satisfy B(2): ∑ bᵢ cᵢ = 0 ≠ 1/2. -/
theorem rkEuler_not_B2 : ¬rkEuler.SatisfiesB 2 := by
  intro hB
  have h := hB 2 (by omega) le_rfl
  simp [rkEuler] at h

/-- Forward Euler does NOT satisfy D(1): ∑ bᵢ aᵢ₁ = 0 ≠ b₁(1-c₁) = 1. -/
theorem rkEuler_not_D1 : ¬rkEuler.SatisfiesD 1 := by
  intro hD
  have h := hD 1 (by omega) le_rfl 0
  simp [rkEuler] at h

/-- Forward Euler is NOT order 2: ∑ bᵢ cᵢ = 0 ≠ 1/2. -/
theorem rkEuler_not_order2 : ¬rkEuler.HasOrderGe2 := by
  intro ⟨_, h2⟩
  simp [order2, rkEuler] at h2

/-- Forward Euler is NOT symmetric: c₁ + c[rev(0)] = 0 + 0 = 0 ≠ 1. -/
theorem rkEuler_not_symmetric : ¬rkEuler.IsSymmetric := by
  intro ⟨_, hn, _⟩
  have h := hn 0
  simp [rkEuler] at h

/-- Forward Euler is NOT stiffly accurate: b₁ = 1 ≠ a₁₁ = 0. -/
theorem rkEuler_not_stifflyAccurate : ¬rkEuler.IsStifflyAccurate := by
  intro hsa
  have h := hsa 0
  simp [rkEuler] at h

end ForwardEuler

/-! ## Explicit Midpoint: B/C/D, Exact Order, Symmetry, Stiff Accuracy -/

section ExplicitMidpoint

/-- Explicit midpoint satisfies B(2): ∑ bᵢ cᵢ^{k-1} = 1/k for k = 1, 2. -/
theorem rkMidpoint_B2 : rkMidpoint.SatisfiesB 2 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkMidpoint, Fin.sum_univ_two]

/-- Explicit midpoint satisfies B(1). -/
theorem rkMidpoint_B1 : rkMidpoint.SatisfiesB 1 :=
  rkMidpoint_B2.mono (by omega)

/-- Explicit midpoint satisfies C(1): row-sum condition. -/
theorem rkMidpoint_C1 : rkMidpoint.SatisfiesC 1 := by
  rw [satisfiesC_one_iff]
  exact rkMidpoint_consistent.row_sum

/-- Explicit midpoint does NOT satisfy B(3): ∑ bᵢ cᵢ² = 1/4 ≠ 1/3. -/
theorem rkMidpoint_not_B3 : ¬rkMidpoint.SatisfiesB 3 := by
  intro hB
  have h := hB 3 (by omega) le_rfl
  simp [rkMidpoint, Fin.sum_univ_two] at h
  linarith

/-- Explicit midpoint does NOT satisfy C(2):
  ∑ⱼ a₂ⱼ cⱼ = (1/2)·0 + 0·(1/2) = 0 ≠ c₂²/2 = 1/8. -/
theorem rkMidpoint_not_C2 : ¬rkMidpoint.SatisfiesC 2 := by
  intro hC
  have h := hC 2 (by omega) le_rfl 1
  simp [rkMidpoint, Fin.sum_univ_two] at h
  linarith

/-- Explicit midpoint does NOT satisfy D(1):
  ∑ᵢ bᵢ aᵢ₁ = 0·0 + 1·(1/2) = 1/2 ≠ b₁(1-c₁) = 0. -/
theorem rkMidpoint_not_D1 : ¬rkMidpoint.SatisfiesD 1 := by
  intro hD
  have h := hD 1 (by omega) le_rfl 0
  simp [rkMidpoint, Fin.sum_univ_two] at h

/-- Explicit midpoint is NOT order 3: ∑ bᵢ cᵢ² = 1/4 ≠ 1/3. -/
theorem rkMidpoint_not_order3 : ¬rkMidpoint.HasOrderGe3 := by
  intro ⟨_, _, h3a, _⟩
  simp [order3a, rkMidpoint, Fin.sum_univ_two] at h3a
  linarith

/-- Explicit midpoint is NOT symmetric: c₁ + c₂ = 0 + 1/2 = 1/2 ≠ 1. -/
theorem rkMidpoint_not_symmetric : ¬rkMidpoint.IsSymmetric := by
  intro ⟨_, hn, _⟩
  have h := hn 0
  simp [rkMidpoint, Fin.rev] at h

/-- Explicit midpoint is NOT stiffly accurate: b₁ = 0 ≠ a₂₁ = 1/2. -/
theorem rkMidpoint_not_stifflyAccurate : ¬rkMidpoint.IsStifflyAccurate := by
  intro hsa
  have h := hsa 0
  simp [rkMidpoint] at h

end ExplicitMidpoint

/-! ## Heun's Method: B/C/D, Exact Order, Symmetry, Stiff Accuracy -/

section Heun

/-- Heun's method satisfies B(2). -/
theorem rkHeun_B2 : rkHeun.SatisfiesB 2 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkHeun, Fin.sum_univ_two] <;> norm_num

/-- Heun's method satisfies C(1): row-sum condition. -/
theorem rkHeun_C1 : rkHeun.SatisfiesC 1 := by
  rw [satisfiesC_one_iff]
  exact rkHeun_consistent.row_sum

/-- **Heun's method satisfies D(1)**: ∑ᵢ bᵢ aᵢⱼ = bⱼ(1-cⱼ) for all j.
  - j=0: (1/2)·0 + (1/2)·1 = 1/2 = (1/2)(1-0)
  - j=1: (1/2)·0 + (1/2)·0 = 0 = (1/2)(1-1) -/
theorem rkHeun_D1 : rkHeun.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; fin_cases j <;> simp [rkHeun, Fin.sum_univ_two] <;> norm_num

/-- Heun's method does NOT satisfy B(3): ∑ bᵢ cᵢ² = 1/2 ≠ 1/3. -/
theorem rkHeun_not_B3 : ¬rkHeun.SatisfiesB 3 := by
  intro hB
  have h := hB 3 (by omega) le_rfl
  simp [rkHeun, Fin.sum_univ_two] at h

/-- Heun's method does NOT satisfy C(2):
  ∑ⱼ a₂ⱼ cⱼ = 1·0 + 0·1 = 0 ≠ c₂²/2 = 1/2. -/
theorem rkHeun_not_C2 : ¬rkHeun.SatisfiesC 2 := by
  intro hC
  have h := hC 2 (by omega) le_rfl 1
  simp [rkHeun, Fin.sum_univ_two] at h

/-- Heun's method does NOT satisfy D(2):
  k=2, j=0: ∑ bᵢ cᵢ aᵢ₁ = (1/2)·0·0 + (1/2)·1·1 = 1/2 ≠ b₁(1-c₁²)/2 = 1/4. -/
theorem rkHeun_not_D2 : ¬rkHeun.SatisfiesD 2 := by
  intro hD
  have h := hD 2 (by omega) le_rfl 0
  simp [rkHeun, Fin.sum_univ_two] at h
  linarith

/-- Heun's method is NOT order 3: ∑ bᵢ cᵢ² = 1/2 ≠ 1/3. -/
theorem rkHeun_not_order3 : ¬rkHeun.HasOrderGe3 := by
  intro ⟨_, _, h3a, _⟩
  simp [order3a, rkHeun, Fin.sum_univ_two] at h3a

/-- Heun's method is NOT symmetric: A[0][0] + A[1][1] = 0 + 0 = 0 ≠ b[0] = 1/2. -/
theorem rkHeun_not_symmetric : ¬rkHeun.IsSymmetric := by
  intro ⟨_, _, ht⟩
  have h := ht 0 0
  simp [rkHeun, Fin.rev] at h

/-- Heun's method is NOT stiffly accurate: b₁ = 1/2 ≠ a₂₁ = 1. -/
theorem rkHeun_not_stifflyAccurate : ¬rkHeun.IsStifflyAccurate := by
  intro hsa
  have h := hsa 0
  simp [rkHeun] at h

end Heun

/-! ## Classical RK4: B/C/D, Exact Order, Symmetry, Stiff Accuracy -/

section RK4

/-- Classical RK4 satisfies B(4): the quadrature rule is exact on polynomials of degree ≤ 3.
  ∑ bᵢ cᵢ^{k-1} = 1/k for k = 1,...,4. -/
theorem rk4_B4 : rk4.SatisfiesB 4 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rk4, Fin.sum_univ_four] <;> norm_num

/-- Classical RK4 satisfies C(1): row-sum condition. -/
theorem rk4_C1 : rk4.SatisfiesC 1 := by
  rw [satisfiesC_one_iff]
  exact rk4_consistent.row_sum

/-- **Classical RK4 satisfies D(1)**: ∑ᵢ bᵢ aᵢⱼ = bⱼ(1 − cⱼ) for all j. -/
theorem rk4_D1 : rk4.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; fin_cases j <;> simp [rk4, Fin.sum_univ_four] <;> norm_num

/-- Classical RK4 does NOT satisfy B(5): ∑ bᵢ cᵢ⁴ = 5/24 ≠ 1/5.
  The quadrature order of RK4 is exactly 4. -/
theorem rk4_not_B5 : ¬rk4.SatisfiesB 5 := by
  intro hB
  have h := hB 5 (by omega) le_rfl
  simp [rk4, Fin.sum_univ_four] at h
  linarith

/-- Classical RK4 does NOT satisfy C(2):
  i=1: ∑ⱼ a₂ⱼ cⱼ = (1/2)·0 = 0 ≠ c₂²/2 = 1/8. -/
theorem rk4_not_C2 : ¬rk4.SatisfiesC 2 := by
  intro hC
  have h := hC 2 (by omega) le_rfl 1
  simp [rk4, Fin.sum_univ_four] at h
  linarith

/-- Classical RK4 does NOT satisfy D(2):
  k=2, j=1: ∑ bᵢ cᵢ aᵢ₂ = 1/12 ≠ b₂(1-c₂²)/2 = 1/8. -/
theorem rk4_not_D2 : ¬rk4.SatisfiesD 2 := by
  intro hD
  have h := hD 2 (by omega) le_rfl 1
  simp [rk4, Fin.sum_univ_four] at h
  linarith

/-- Classical RK4 is NOT order 5: ∑ bᵢ cᵢ⁴ = 5/24 ≠ 1/5. -/
theorem rk4_not_order5 : ¬rk4.HasOrderGe5 := by
  intro ⟨_, h5a, _⟩
  simp [order5a, rk4, Fin.sum_univ_four] at h5a
  linarith

/-- RK4 has order ≥ 3 (extracted from the order 4 proof). -/
theorem rk4_order3 : rk4.HasOrderGe3 :=
  ⟨rk4_order4.1, rk4_order4.2.1, rk4_order4.2.2.1, rk4_order4.2.2.2.1⟩

/-- Classical RK4 is NOT symmetric: A[0][0] + A[3][3] = 0 + 0 = 0 ≠ b[0] = 1/6. -/
theorem rk4_not_symmetric : ¬rk4.IsSymmetric := by
  intro ⟨_, _, ht⟩
  have h := ht 0 0
  simp [rk4, Fin.rev] at h

/-- Classical RK4 is NOT stiffly accurate: b₁ = 1/6 ≠ a₄₁ = 0. -/
theorem rk4_not_stifflyAccurate : ¬rk4.IsStifflyAccurate := by
  intro hsa
  have h := hsa 0
  simp [rk4] at h

end RK4

/-! ## Order via B+C Framework

Deriving order from the B+C collocation theorem, connecting explicit methods
to the simplifying assumption infrastructure. -/

/-- Explicit midpoint has order ≥ 2 via B(2) ∧ C(1), using the collocation order theorem. -/
theorem rkMidpoint_order2' : rkMidpoint.HasOrderGe2 :=
  HasOrderGe2_of_B2_C1 _ rkMidpoint_B2 rkMidpoint_C1

/-- Heun has order ≥ 2 via B(2) ∧ C(1), using the collocation order theorem. -/
theorem rkHeun_order2' : rkHeun.HasOrderGe2 :=
  HasOrderGe2_of_B2_C1 _ rkHeun_B2 rkHeun_C1

/-! ## General Properties -/

/-- For any consistent method, B(1) holds (follows from weight sum = 1). -/
theorem consistent_implies_B1 {s : ℕ} (t : ButcherTableau s) (h : t.IsConsistent) :
    t.SatisfiesB 1 :=
  (satisfiesB_one_iff t).mpr h.weights_sum

/-- For any consistent method, C(1) holds (follows from row-sum condition). -/
theorem consistent_implies_C1 {s : ℕ} (t : ButcherTableau s) (h : t.IsConsistent) :
    t.SatisfiesC 1 :=
  (satisfiesC_one_iff t).mpr h.row_sum

/-! ## Stability Functions of Explicit Methods

For explicit RK methods, the stability function R(z) is a **polynomial** (since A is
nilpotent, so (I − zA)⁻¹ = I + zA + z²A² + ⋯ + z^{s−1}A^{s−1} terminates).

This polynomial nature means explicit stability regions are bounded, so explicit
methods are NEVER A-stable: |R(z)| → ∞ as |z| → ∞ along the negative real axis.

For s-stage explicit methods of order p, the stability polynomial equals the Taylor
polynomial of eᶻ truncated at degree p, plus higher-order corrections.
-/

/-- Stability function of explicit midpoint: R(z) = 1 + z + z²/2.
  This is the 2nd-degree Taylor polynomial of eᶻ. -/
noncomputable def rkMidpointStabilityFn (z : ℂ) : ℂ := 1 + z + z ^ 2 / 2

/-- Stability function of Heun's method: R(z) = 1 + z + z²/2.
  Same as explicit midpoint — both 2-stage order-2 methods share this stability function. -/
noncomputable def rkHeunStabilityFn (z : ℂ) : ℂ := 1 + z + z ^ 2 / 2

/-- Both 2-stage explicit methods of order 2 have the same stability function. -/
theorem rkMidpoint_rkHeun_same_stability (z : ℂ) :
    rkMidpointStabilityFn z = rkHeunStabilityFn z := rfl

/-- The classical RK4 stability function: R(z) = 1 + z + z²/2 + z³/6 + z⁴/24.
  This equals the 4th-degree Taylor polynomial of eᶻ. -/
noncomputable def rk4StabilityFn (z : ℂ) : ℂ :=
  1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24

/-- Explicit midpoint is NOT A-stable: R(-3) = 5/2, so |R(-3)| > 1. -/
theorem rkMidpoint_not_aStable :
    ∃ z : ℂ, z.re ≤ 0 ∧ 1 < ‖rkMidpointStabilityFn z‖ := by
  refine ⟨-3, by simp, ?_⟩
  simp [rkMidpointStabilityFn]
  norm_num

/-- Heun's method is NOT A-stable: R(-3) = 5/2, so |R(-3)| > 1. -/
theorem rkHeun_not_aStable :
    ∃ z : ℂ, z.re ≤ 0 ∧ 1 < ‖rkHeunStabilityFn z‖ := by
  refine ⟨-3, by simp, ?_⟩
  simp [rkHeunStabilityFn]
  norm_num

/-- RK4 is NOT A-stable: R(-3) = 11/8, so |R(-3)| > 1. -/
theorem rk4_not_aStable :
    ∃ z : ℂ, z.re ≤ 0 ∧ 1 < ‖rk4StabilityFn z‖ := by
  refine ⟨-3, by simp, ?_⟩
  simp [rk4StabilityFn]
  norm_num

/-! ## Summary

### Complete property table for all explicit methods

| Property        | Fwd Euler | Expl. Mid | Heun | RK4 |
|:--------------- |:---------:|:---------:|:----:|:---:|
| B(p)            | 1         | 2         | 2    | 4   |
| C(q)            | 1         | 1         | 1    | 1   |
| D(r)            | 0         | 0         | 1    | 1   |
| Order           | 1         | 2         | 2    | 4   |
| Symmetric       | No        | No        | No   | No  |
| Stiffly Acc.    | No        | No        | No   | No  |
| A-stable        | No*       | No        | No   | No  |

*Forward Euler's non-A-stability is already in `rkEuler_not_aStable` (RungeKutta.lean).

### Observations (formalized)

1. **Stage order**: All explicit methods have stage order C(1) = 1.
   This is because c₁ = 0 and the strictly lower-triangular A cannot satisfy
   ∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k/k for k ≥ 2 at stage i=2.

2. **D condition pattern**: D(1) holds for methods with "balanced" weight distributions
   (Heun, RK4) but not for "concentrated" weights (forward Euler b=[1], midpoint b=[0,1]).

3. **Quadrature = classical order**: For all explicit methods in the library, B(p) with
   p equal to the classical order. This is not true in general for implicit methods
   (e.g., GL2 has B(4) = quadrature order 4, matching its classical order 4, but
   Lobatto IIIA 2-stage has B(2) = quadrature order 2 while classical order is also 2).

4. **No symmetry**: Explicit methods with c₁ = 0 fail the node symmetry condition
   c₁ + cₛ = 1 unless cₛ = 1, and even then the tableau symmetry A[i][j] + A[rev(i)][rev(j)] = b[j]
   fails because A is strictly lower-triangular (so diagonal terms A[i][i] = 0,
   making A[0][0] + A[s-1][s-1] = 0 ≠ b[0] for consistent methods).
-/

end ButcherTableau
