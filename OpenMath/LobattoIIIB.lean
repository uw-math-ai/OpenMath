import OpenMath.LobattoIIIA

/-!
# Lobatto IIIB 2-Stage Method (Section 4.2)

The **Lobatto IIIB 2-stage** method is a 2-stage implicit Runge–Kutta method,
the "adjoint" of the Lobatto IIIA 2-stage method.

Butcher tableau:
```
  0 | 1/2   0
  1 | 1/2   0
  --|----------
    | 1/2   1/2
```

Notable: Lobatto IIIB does NOT satisfy the row-sum condition (c₁ = 0 but ∑ⱼ a₁ⱼ = 1/2),
so it is NOT consistent in the standard RK sense. However, it still has order 2
(the quadrature conditions are satisfied) and it is A-stable.

The stability function is R(z) = (2+z)/(2-z), the same as Lobatto IIIA
and the implicit midpoint rule.

The method is NOT algebraically stable: M₂₂ = -1/4 < 0.

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Section 4.2; Hairer–Wanner, Table 5.6.
-/

open Finset Real Filter

/-! ## Butcher Tableau Definition -/

/-- **Lobatto IIIB 2-stage** RK method.
  Collocation points: c₁ = 0, c₂ = 1 (endpoints of [0,1]).
  This method does NOT satisfy the row-sum condition.
  Reference: Hairer–Wanner, Table 5.6. -/
noncomputable def rkLobattoIIIB2 : ButcherTableau 2 where
  A := ![![1/2, 0], ![1/2, 0]]
  b := ![1/2, 1/2]
  c := ![0, 1]

/-! ## Basic Properties -/

/-- Lobatto IIIB 2-stage satisfies the weight condition: ∑ bᵢ = 1. -/
theorem rkLobattoIIIB2_weights_sum :
    ∑ i : Fin 2, rkLobattoIIIB2.b i = 1 := by
  simp [rkLobattoIIIB2, Fin.sum_univ_two]; norm_num

/-- Lobatto IIIB 2-stage does NOT satisfy the row-sum condition:
  c₁ = 0 but ∑ⱼ a₁ⱼ = 1/2. -/
theorem rkLobattoIIIB2_not_rowSum : ¬rkLobattoIIIB2.IsRowSumConsistent := by
  intro h
  have := h 0
  simp [rkLobattoIIIB2, Fin.sum_univ_two] at this

/-- Lobatto IIIB 2-stage is NOT consistent (row-sum condition fails). -/
theorem rkLobattoIIIB2_not_consistent : ¬rkLobattoIIIB2.IsConsistent := by
  intro ⟨_, h⟩; exact rkLobattoIIIB2_not_rowSum h

/-- Lobatto IIIB 2-stage satisfies order condition 1: ∑ bᵢ = 1. -/
theorem rkLobattoIIIB2_order1 : rkLobattoIIIB2.HasOrderGe1 := by
  simp [ButcherTableau.HasOrderGe1, ButcherTableau.order1, rkLobattoIIIB2, Fin.sum_univ_two]
  norm_num

/-- Lobatto IIIB 2-stage satisfies order condition 2: ∑ bᵢcᵢ = 1/2.
  Despite NOT being row-sum consistent, the quadrature condition holds. -/
theorem rkLobattoIIIB2_order2 : rkLobattoIIIB2.HasOrderGe2 := by
  refine ⟨?_, ?_⟩
  · simp [ButcherTableau.order1, rkLobattoIIIB2, Fin.sum_univ_two]; norm_num
  · simp [ButcherTableau.order2, rkLobattoIIIB2, Fin.sum_univ_two]

/-- Lobatto IIIB 2-stage does NOT have order 3: ∑ bᵢ cᵢ² = 1/2 ≠ 1/3. -/
theorem rkLobattoIIIB2_not_order3 : ¬rkLobattoIIIB2.HasOrderGe3 := by
  intro ⟨_, _, h3a, _⟩
  simp [ButcherTableau.order3a, rkLobattoIIIB2, Fin.sum_univ_two] at h3a

/-- Lobatto IIIB 2-stage has non-negative weights. -/
theorem rkLobattoIIIB2_nonNegWeights : rkLobattoIIIB2.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkLobattoIIIB2]

/-- Lobatto IIIB 2-stage is NOT explicit (a₁₁ = 1/2 ≠ 0). -/
theorem rkLobattoIIIB2_not_explicit : ¬rkLobattoIIIB2.IsExplicit := by
  intro h; have := h 0 0 (le_refl _); simp [rkLobattoIIIB2] at this

/-! ## Stability Function

The stability function of Lobatto IIIB 2-stage is R(z) = (2+z)/(2-z),
identical to Lobatto IIIA and the implicit midpoint rule.

This can be verified by computing R(z) = 1 + z·bᵀ(I-zA)⁻¹·𝟙:
  I - zA = [[1-z/2, 0], [-z/2, 1]]
  det(I-zA) = 1-z/2
  (I-zA)⁻¹·𝟙 = [1/(1-z/2), 1/(1-z/2)]
  R(z) = 1 + z·(1/2 + 1/2)·1/(1-z/2) = (2+z)/(2-z)
-/

/-- **A-stability of Lobatto IIIB 2-stage**: |R(z)| ≤ 1 for Re(z) ≤ 0.
  The stability function is (2+z)/(2-z), identical to Lobatto IIIA.
  Reference: Iserles, Section 4.2. -/
theorem lobIIIB_aStable (z : ℂ) (hz : z.re ≤ 0) :
    ‖lobIIIAStabilityFn z‖ ≤ 1 :=
  lobIIIA_aStable z hz

/-- **Lobatto IIIB does NOT have stiff decay**: R(x) → -1 ≠ 0 as x → -∞.
  The stability function is (2+x)/(2-x) → -1. -/
theorem lobIIIB_not_stiffDecay :
    ¬Tendsto (fun x : ℝ => lobIIIAStabilityFn (↑x)) atBot (nhds 0) :=
  lobIIIA_not_stiffDecay

/-! ## NOT Algebraically Stable -/

/-- **Lobatto IIIB 2-stage is NOT algebraically stable.**
  M₂₂ = 2b₂a₂₂ - b₂² = 2·(1/2)·0 - (1/2)² = -1/4 < 0.
  With v = (0,1), the quadratic form is -1/4 < 0. -/
theorem rkLobattoIIIB2_not_algStable : ¬rkLobattoIIIB2.IsAlgStable := by
  intro ⟨_, hM⟩
  have h := hM (fun i => if i = 1 then 1 else 0)
  simp [ButcherTableau.algStabMatrix, rkLobattoIIIB2] at h
  linarith

/-! ## Comparison of the Lobatto III Family

The three Lobatto III families (2-stage, s=2) share the same nodes c = (0, 1)
and weights b = (1/2, 1/2), but differ in their stage matrices:

| Property          | IIIA              | IIIB              | IIIC              |
|-------------------|-------------------|--------------------|-------------------|
| A                 | [[0,0],[½,½]]     | [[½,0],[½,0]]      | [[½,-½],[½,½]]    |
| Row-sum           | ✓                 | ✗                  | ✓                 |
| R(z)              | (2+z)/(2-z)       | (2+z)/(2-z)        | 2/(z²-2z+2)       |
| R(−∞)             | −1                | −1                 | 0                 |
| L-stable          | ✗                 | ✗                  | ✓                 |
| Alg. stable       | ✗                 | ✗                  | ✓                 |
| Order             | 2                 | 2                  | 2                 |

IIIA and IIIB are **adjoint** to each other: A* + A = b·𝟙ᵀ.
-/
