import OpenMath.Collocation

/-!
# Order Barriers for Explicit Runge–Kutta Methods

## Butcher's Order Barrier Theorem

For an s-stage **explicit** consistent Runge–Kutta method, the maximum achievable order p
satisfies p ≤ s for s ≤ 4. (For s ≥ 5, the stronger barrier p ≤ s − 1 holds, but is
not proved here as it requires deeper combinatorial arguments.)

The key structural insight: for any explicit consistent method, c₀ = 0 (the first
abscissa is always zero, since A is strictly lower triangular and c₀ = ∑ⱼ a₀ⱼ = 0).
This forces certain "maximal chain" order conditions to vanish identically:
- The tree τ_{s+1} = [[[⋯[•]⋯]]] (the "tall tree" of depth s) has elementary weight
  Φ(τ) = ∑ bᵢ aᵢⱼ aⱼₖ ⋯ cₗ, and every surviving chain must pass through c₀ = 0.

## Results

- `explicit_c_zero`: explicit + row-sum consistent → c₀ = 0
- `explicit_first_row_zero`: explicit → A[0][j] = 0 for all j
- `explicit_order_barrier_1`: 1-stage explicit consistent → order ≤ 1
- `explicit_order_barrier_2`: 2-stage explicit consistent → order ≤ 2
- `explicit_order_barrier_3`: 3-stage explicit consistent → order ≤ 3
- `explicit_order_barrier_4`: 4-stage explicit consistent → order ≤ 4

Each barrier is tight: forward Euler (order 1), Heun/explicit midpoint (order 2),
Kutta's 3rd-order method (order 3), and classical RK4 (order 4) achieve the bounds.

Reference: Iserles, Section 2.3; Butcher, *Numerical Methods for ODEs*, Theorem 325A;
Hairer–Nørsett–Wanner, *Solving ODEs I*, Section II.2.
-/

open Finset Real

namespace ButcherTableau

variable {s : ℕ}

/-! ## Structural Properties of Explicit Methods -/

/-- For an explicit RK method, A[0][j] = 0 for all j.
  This is immediate from the definition: A[i][j] = 0 for j ≥ i, and 0 ≤ j for all j. -/
theorem explicit_first_row_zero (t : ButcherTableau (s + 1)) (hE : t.IsExplicit)
    (j : Fin (s + 1)) : t.A 0 j = 0 :=
  hE 0 j (Fin.zero_le j)

/-- For an explicit consistent RK method, the first node c₀ = 0.
  Proof: c₀ = ∑ⱼ a₀ⱼ = ∑ⱼ 0 = 0 by explicit + row-sum consistency. -/
theorem explicit_c_zero (t : ButcherTableau (s + 1)) (hE : t.IsExplicit)
    (hRS : t.IsRowSumConsistent) : t.c 0 = 0 := by
  rw [hRS 0]
  apply Finset.sum_eq_zero
  intro j _
  exact hE 0 j (Fin.zero_le j)

/-- For an explicit RK method, any product involving A[i][j] with j ≥ i is zero. -/
theorem explicit_A_zero (t : ButcherTableau s) (hE : t.IsExplicit)
    (i j : Fin s) (hij : i ≤ j) : t.A i j = 0 :=
  hE i j hij

/-! ## 1-Stage Barrier: explicit consistent → order ≤ 1

A 1-stage explicit method has A = [[0]], c = [0], b = [1].
The second-order condition ∑ bᵢ cᵢ = b₀ · 0 = 0 ≠ 1/2, so order ≤ 1. -/

/-- **Order barrier for 1-stage explicit methods.**
  No 1-stage explicit consistent RK method can achieve order 2. -/
theorem explicit_order_barrier_1 (t : ButcherTableau 1) (hE : t.IsExplicit)
    (hC : t.IsConsistent) : ¬t.HasOrderGe2 := by
  intro ⟨_, h2⟩
  simp only [order2] at h2
  have hc0 : t.c 0 = 0 := by
    rw [hC.row_sum 0]
    apply Finset.sum_eq_zero
    intro j _
    exact hE 0 j (Fin.zero_le j)
  have : ∑ i : Fin 1, t.b i * t.c i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    fin_cases i
    simp [hc0]
  linarith

/-! ## 2-Stage Barrier: explicit consistent → order ≤ 2

A 2-stage explicit method has A strictly lower triangular: a₀₀ = a₀₁ = a₁₁ = 0.
Thus c₀ = 0, and the third-order condition (τ₂):
  ∑ᵢⱼ bᵢ aᵢⱼ cⱼ = b₁ · a₁₀ · c₀ = 0 ≠ 1/6. -/

/-- **Order barrier for 2-stage explicit methods.**
  No 2-stage explicit consistent RK method can achieve order 3. -/
theorem explicit_order_barrier_2 (t : ButcherTableau 2) (hE : t.IsExplicit)
    (hC : t.IsConsistent) : ¬t.HasOrderGe3 := by
  intro ⟨_, _, _, h3b⟩
  simp only [order3b] at h3b
  have hc0 : t.c 0 = 0 := by
    rw [hC.row_sum 0]
    apply Finset.sum_eq_zero
    intro j _
    exact hE 0 j (Fin.zero_le j)
  -- Show ∑ᵢⱼ bᵢ aᵢⱼ cⱼ = 0
  have : ∑ i : Fin 2, ∑ j : Fin 2, t.b i * t.A i j * t.c j = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    fin_cases i <;> fin_cases j
    -- i=0, j=0: a₀₀ = 0
    · simp [hE 0 0 le_rfl]
    -- i=0, j=1: a₀₁ = 0
    · simp [hE 0 1 (by omega : (0 : Fin 2) ≤ 1)]
    -- i=1, j=0: c₀ = 0
    · simp [hc0]
    -- i=1, j=1: a₁₁ = 0
    · simp [hE 1 1 le_rfl]
  linarith

/-! ## 3-Stage Barrier: explicit consistent → order ≤ 3

A 3-stage explicit method has A strictly lower triangular. The fourth-order
condition (τ₄ = order4d):
  ∑ᵢⱼₖ bᵢ aᵢⱼ aⱼₖ cₖ = 1/24

For explicit 3-stage, every chain (i, j, k) with aᵢⱼ ≠ 0 and aⱼₖ ≠ 0 requires
j < i and k < j. The only possible chain is (2, 1, 0), giving
b₂ · a₂₁ · a₁₀ · c₀ = 0 since c₀ = 0. -/

/-- **Order barrier for 3-stage explicit methods.**
  No 3-stage explicit consistent RK method can achieve order 4. -/
theorem explicit_order_barrier_3 (t : ButcherTableau 3) (hE : t.IsExplicit)
    (hC : t.IsConsistent) : ¬t.HasOrderGe4 := by
  intro ⟨_, _, _, _, _, _, _, h4d⟩
  simp only [order4d] at h4d
  have hc0 : t.c 0 = 0 := by
    rw [hC.row_sum 0]
    apply Finset.sum_eq_zero
    intro j _
    exact hE 0 j (Fin.zero_le j)
  -- Show ∑ᵢⱼₖ bᵢ aᵢⱼ aⱼₖ cₖ = 0
  have : ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      t.b i * t.A i j * t.A j k * t.c k = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    apply Finset.sum_eq_zero; intro k _
    -- Either aᵢⱼ = 0 (j ≥ i) or aⱼₖ = 0 (k ≥ j) or cₖ = 0 (k = 0)
    by_cases hij : i ≤ j
    · simp [hE i j hij]
    · push_neg at hij
      by_cases hjk : j ≤ k
      · simp [hE j k hjk]
      · push_neg at hjk
        -- k < j < i, so k ≤ i - 2. For 3 stages: i ≤ 2, j ≤ 1, k = 0.
        have hk0 : k = 0 := by omega
        subst hk0; simp [hc0]
  linarith

/-! ## 4-Stage Barrier: explicit consistent → order ≤ 4

A 4-stage explicit method has A strictly lower triangular. The fifth-order
condition (τ₉ = order5i):
  ∑ᵢⱼₖ bᵢ aᵢⱼ aⱼₖ (∑ₗ aₖₗ cₗ) = 1/120

For explicit 4-stage, any chain (i, j, k) with i > j > k requires k ≤ 1.
The innermost sum ∑ₗ aₖₗ cₗ always involves c₀ = 0:
- k = 0: all a₀ₗ = 0 (first row is zero), so sum = 0.
- k = 1: only l = 0 survives, giving a₁₀ · c₀ = 0.
Hence the entire condition evaluates to 0 ≠ 1/120. -/

/-- **Order barrier for 4-stage explicit methods.**
  No 4-stage explicit consistent RK method can achieve order 5. -/
theorem explicit_order_barrier_4 (t : ButcherTableau 4) (hE : t.IsExplicit)
    (hC : t.IsConsistent) : ¬t.HasOrderGe5 := by
  intro ⟨_, _, _, _, _, _, _, _, _, h5i⟩
  simp only [order5i] at h5i
  have hc0 : t.c 0 = 0 := by
    rw [hC.row_sum 0]
    apply Finset.sum_eq_zero
    intro j _
    exact hE 0 j (Fin.zero_le j)
  -- Direct proof: enumerate all (i,j,k) triples
  have : ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
      t.b i * t.A i j * t.A j k * (∑ l : Fin 4, t.A k l * t.c l) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    apply Finset.sum_eq_zero; intro k _
    by_cases hij : i ≤ j
    · simp [hE i j hij]
    · push_neg at hij
      by_cases hjk : j ≤ k
      · simp [hE j k hjk]
      · push_neg at hjk
        -- k < j < i, with stages in Fin 4. So k ≤ 1.
        -- Show the innermost sum ∑ₗ aₖₗ cₗ = 0
        have inner : ∑ l : Fin 4, t.A k l * t.c l = 0 := by
          apply Finset.sum_eq_zero; intro l _
          by_cases hkl : k ≤ l
          · simp [hE k l hkl]
          · push_neg at hkl
            -- l < k ≤ 1, so l = 0
            have hl0 : l = 0 := by omega
            subst hl0; simp [hc0]
        simp [inner]
  linarith

/-! ## Tightness of the Barriers

The barriers are tight: there exist explicit methods achieving each bound.
These existence results follow from specific methods already formalized:
- Forward Euler: 1-stage, order 1 (in RungeKutta.lean)
- Heun's method: 2-stage, order 2 (in ExplicitRK.lean)
- Classical RK4: 4-stage, order 4 (in ExplicitRK.lean)
-/

/-! ## Non-existence of Explicit C(2) Methods

A structural consequence of c₀ = 0: no explicit consistent method can satisfy C(2).
This is because C(2) at k = 2, i = 0 requires ∑ⱼ a₀ⱼ cⱼ = c₀²/2, but the LHS is 0
(all a₀ⱼ = 0) while requiring c₀²/2 = 0, which is consistent. However, for i = 1:
∑ⱼ a₁ⱼ cⱼ = c₁²/2, and a₁ⱼ = 0 for j ≥ 1, so a₁₀ · c₀ = 0 = c₁²/2.
This forces c₁ = 0, but then the method degenerates (two coincident nodes). -/

/-- No explicit consistent method with s ≥ 2 stages and distinct nodes can satisfy C(2).
  Proof: C(2) at k=2 gives ∑ⱼ a₁ⱼ cⱼ = c₁²/2. For explicit, a₁ⱼ = 0 for j ≥ 1,
  so LHS = a₁₀ · c₀ = 0 (since c₀ = 0). Hence c₁ = 0, violating distinctness. -/
theorem explicit_not_C2_distinct (t : ButcherTableau (s + 2)) (hE : t.IsExplicit)
    (hRS : t.IsRowSumConsistent) (hC2 : t.SatisfiesC 2)
    (h_distinct : t.c 0 ≠ t.c 1) : False := by
  have hc0 := explicit_c_zero t hE hRS
  -- C(2) at k = 2, i = 1: ∑ⱼ a₁ⱼ cⱼ = c₁²/2
  have hC2_1 := hC2 2 (by omega) le_rfl (1 : Fin (s + 2))
  simp at hC2_1
  -- LHS: ∑ⱼ a₁ⱼ cⱼ. For explicit, a₁ⱼ = 0 for j ≥ 1.
  have lhs_zero : ∑ j : Fin (s + 2), t.A 1 j * t.c j = 0 := by
    apply Finset.sum_eq_zero; intro j _
    by_cases hj0 : j = 0
    · subst hj0; simp [hc0]
    · have hj_ge : (1 : Fin (s + 2)) ≤ j := by
        apply Fin.mk_le_mk.mpr
        exact Nat.succ_le_of_lt <| Nat.pos_of_ne_zero fun h => hj0 (Fin.ext h)
      simp [hE 1 j hj_ge]
  rw [lhs_zero] at hC2_1
  -- So c₁²/2 = 0, hence c₁ = 0
  have hc1_zero : t.c 1 = 0 := by nlinarith
  exact h_distinct (by rw [hc0, hc1_zero])

end ButcherTableau
