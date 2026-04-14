import OpenMath.StiffAccuracy
import OpenMath.Collocation

/-!
# Embedded Runge–Kutta Pairs (Section 2.7 / Chapter 5)

## Error Estimation via Embedded Pairs

An **embedded Runge–Kutta pair** of order p(p̂) consists of two s-stage RK methods
sharing the same coefficient matrix A and nodes c, but with different weights:
- b : the main method of order p
- b̂ : the embedding method of order p̂ (typically p̂ = p ± 1)

Since both methods share the stage values kᵢ = f(tₙ + cᵢh, yₙ + h∑ⱼ aᵢⱼkⱼ),
the difference yₙ₊₁ − ŷₙ₊₁ = h · ∑ᵢ (bᵢ − b̂ᵢ) kᵢ provides a local error estimate
at essentially no extra cost.

## FSAL Property

A pair has the **First Same As Last (FSAL)** property if the last stage of step n
equals the first stage of step n+1. This occurs when:
- The main method is stiffly accurate: bᵢ = a_{s,i}
- c₁ = 0 (first node at the beginning)

## Examples

### Heun–Euler 2(1)
The simplest embedded pair:
- Main: Heun's method (order 2), b = [1/2, 1/2]
- Embedding: Forward Euler (order 1), b̂ = [1, 0]
- Shared: A = [[0,0],[1,0]], c = [0, 1]

### Bogacki–Shampine 3(2)
A 4-stage, order 3(2) pair with the FSAL property:
```
  0   |
  1/2 | 1/2
  3/4 | 0     3/4
  1   | 2/9   1/3   4/9
  ----|-------------------------
      | 2/9   1/3   4/9   0      (order 3)
      | 7/24  1/4   1/3   1/8    (order 2)
```

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 2.7 and Chapter 5; Bogacki & Shampine (1989).
-/

open Finset Real

/-! ## Embedded Pair Definition -/

/-- An **embedded Runge–Kutta pair** of two s-stage methods sharing A and c
  but with different weights b (main) and b̂ (embedding).
  Reference: Iserles, Section 2.7. -/
structure EmbeddedRKPair (s : ℕ) where
  /-- Stage coefficient matrix a_{ij} (shared by both methods). -/
  A : Fin s → Fin s → ℝ
  /-- Weights for the main method. -/
  b : Fin s → ℝ
  /-- Weights for the embedding method. -/
  bHat : Fin s → ℝ
  /-- Nodes (shared by both methods). -/
  c : Fin s → ℝ

namespace EmbeddedRKPair

variable {s : ℕ}

/-- The **main method** of an embedded pair, as a Butcher tableau. -/
def mainMethod (p : EmbeddedRKPair s) : ButcherTableau s where
  A := p.A
  b := p.b
  c := p.c

/-- The **embedding method** of an embedded pair, as a Butcher tableau. -/
def embedMethod (p : EmbeddedRKPair s) : ButcherTableau s where
  A := p.A
  b := p.bHat
  c := p.c

/-- The **error weight vector** d = b − b̂, whose inner product with the stage
  derivatives gives the local error estimate. -/
def errorWeights (p : EmbeddedRKPair s) (i : Fin s) : ℝ := p.b i - p.bHat i

/-- The main method and embedding share the same A matrix. -/
theorem same_A (p : EmbeddedRKPair s) : p.mainMethod.A = p.embedMethod.A := rfl

/-- The main method and embedding share the same nodes c. -/
theorem same_c (p : EmbeddedRKPair s) : p.mainMethod.c = p.embedMethod.c := rfl

/-- Both methods in the pair are consistent. -/
structure IsConsistent (p : EmbeddedRKPair s) : Prop where
  main_consistent : p.mainMethod.IsConsistent
  embed_consistent : p.embedMethod.IsConsistent

/-- An embedded pair is **explicit** if A is strictly lower triangular. -/
def IsExplicit (p : EmbeddedRKPair s) : Prop := p.mainMethod.IsExplicit

/-- The error weights sum to zero for a consistent pair (since ∑bᵢ = ∑b̂ᵢ = 1). -/
theorem errorWeights_sum_zero (p : EmbeddedRKPair s)
    (hc : p.IsConsistent) : ∑ i : Fin s, p.errorWeights i = 0 := by
  simp only [errorWeights, Finset.sum_sub_distrib]
  have h1 := hc.main_consistent.weights_sum
  have h2 := hc.embed_consistent.weights_sum
  simp only [mainMethod] at h1; simp only [embedMethod] at h2
  linarith

/-- An embedded pair has the **FSAL (First Same As Last)** property if:
  1. The main method is stiffly accurate (bᵢ = a_{s,i})
  2. The first node is c₁ = 0
  This means the last stage value of step n equals the first stage value of step n+1,
  saving one function evaluation per step.
  Reference: Bogacki–Shampine (1989); Dormand–Prince (1980). -/
structure HasFSAL (p : EmbeddedRKPair (s + 1)) : Prop where
  stiffly_accurate : p.mainMethod.IsStifflyAccurate
  first_node_zero : p.c 0 = 0

end EmbeddedRKPair

/-! ## Heun–Euler 2(1) Embedded Pair -/

/-- The **Heun–Euler 2(1)** embedded pair.
  Main: Heun's method (order 2), b = [1/2, 1/2].
  Embedding: Forward Euler (order 1), b̂ = [1, 0].
  Shared: A = [[0,0],[1,0]], c = [0, 1].
  Reference: Standard textbook pair. -/
noncomputable def rkHeunEuler21 : EmbeddedRKPair 2 where
  A := ![![0, 0], ![1, 0]]
  b := ![1/2, 1/2]
  bHat := ![1, 0]
  c := ![0, 1]

/-- The main method of Heun–Euler equals Heun's method. -/
theorem rkHeunEuler21_main_eq_heun :
    rkHeunEuler21.mainMethod = rkHeun := by
  simp only [rkHeunEuler21, EmbeddedRKPair.mainMethod, rkHeun]

/-- Heun–Euler 2(1) is explicit. -/
theorem rkHeunEuler21_explicit : rkHeunEuler21.IsExplicit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [rkHeunEuler21, EmbeddedRKPair.mainMethod]

/-- Heun–Euler 2(1) is consistent (both methods). -/
theorem rkHeunEuler21_consistent : rkHeunEuler21.IsConsistent where
  main_consistent := by
    exact ⟨by simp [rkHeunEuler21, EmbeddedRKPair.mainMethod, Fin.sum_univ_two]; norm_num,
           fun i => by fin_cases i <;> simp [rkHeunEuler21, EmbeddedRKPair.mainMethod,
                                              Fin.sum_univ_two]⟩
  embed_consistent := by
    exact ⟨by simp [rkHeunEuler21, EmbeddedRKPair.embedMethod, Fin.sum_univ_two],
           fun i => by fin_cases i <;> simp [rkHeunEuler21, EmbeddedRKPair.embedMethod,
                                              Fin.sum_univ_two]⟩

/-- The Heun–Euler main method has order 2. -/
theorem rkHeunEuler21_main_order2 : rkHeunEuler21.mainMethod.HasOrderGe2 := by
  rw [rkHeunEuler21_main_eq_heun]; exact rkHeun_order2

/-- The Heun–Euler main method does NOT have order 3.
  The third-order condition ∑ bᵢcᵢ² = 1/3 fails: (1/2)·0² + (1/2)·1² = 1/2 ≠ 1/3. -/
theorem rkHeunEuler21_main_not_order3 : ¬rkHeunEuler21.mainMethod.HasOrderGe3 := by
  rw [rkHeunEuler21_main_eq_heun]
  intro ⟨_, _, h3a, _⟩
  simp [ButcherTableau.order3a, rkHeun, Fin.sum_univ_two] at h3a

/-- The embedding (Euler) has order 1. -/
theorem rkHeunEuler21_embed_order1 : rkHeunEuler21.embedMethod.HasOrderGe1 := by
  simp [ButcherTableau.HasOrderGe1, ButcherTableau.order1, rkHeunEuler21,
    EmbeddedRKPair.embedMethod, Fin.sum_univ_two]

/-- The embedding does NOT have order 2: ∑ b̂ᵢcᵢ = 1·0 + 0·1 = 0 ≠ 1/2. -/
theorem rkHeunEuler21_embed_not_order2 : ¬rkHeunEuler21.embedMethod.HasOrderGe2 := by
  intro ⟨_, h2⟩
  simp [ButcherTableau.order2, rkHeunEuler21, EmbeddedRKPair.embedMethod,
    Fin.sum_univ_two] at h2

/-- Error weights of Heun–Euler: d = [−1/2, 1/2]. -/
theorem rkHeunEuler21_errorWeights :
    ∀ i : Fin 2, rkHeunEuler21.errorWeights i = ![(-1)/2, 1/2] i := by
  intro i; fin_cases i <;> simp [EmbeddedRKPair.errorWeights, rkHeunEuler21] <;> norm_num

/-- Error weights sum to zero. -/
theorem rkHeunEuler21_errorWeights_sum :
    ∑ i : Fin 2, rkHeunEuler21.errorWeights i = 0 :=
  rkHeunEuler21.errorWeights_sum_zero rkHeunEuler21_consistent

/-! ## Bogacki–Shampine 3(2) Embedded Pair -/

/-- The **Bogacki–Shampine 3(2)** embedded pair with FSAL property.
  4-stage explicit pair with order 3 main method and order 2 embedding.
  ```
    0   |
    1/2 | 1/2
    3/4 | 0     3/4
    1   | 2/9   1/3   4/9
    ----|-------------------------
        | 2/9   1/3   4/9   0      (order 3, main)
        | 7/24  1/4   1/3   1/8    (order 2, embedding)
  ```
  Reference: Bogacki & Shampine, "A 3(2) pair of Runge–Kutta formulas",
  Appl. Math. Lett. 2 (1989), 321–325. -/
noncomputable def rkBS32 : EmbeddedRKPair 4 where
  A := ![![0,   0,   0,   0],
         ![1/2, 0,   0,   0],
         ![0,   3/4, 0,   0],
         ![2/9, 1/3, 4/9, 0]]
  b := ![2/9, 1/3, 4/9, 0]
  bHat := ![7/24, 1/4, 1/3, 1/8]
  c := ![0, 1/2, 3/4, 1]

/-- BS3(2) is explicit. -/
theorem rkBS32_explicit : rkBS32.IsExplicit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [rkBS32, EmbeddedRKPair.mainMethod]

/-- BS3(2) is consistent (both methods). -/
theorem rkBS32_consistent : rkBS32.IsConsistent where
  main_consistent := by
    exact ⟨by simp [rkBS32, EmbeddedRKPair.mainMethod, Fin.sum_univ_four]; norm_num,
           fun i => by fin_cases i <;>
             simp [rkBS32, EmbeddedRKPair.mainMethod, Fin.sum_univ_four] <;> norm_num⟩
  embed_consistent := by
    exact ⟨by simp [rkBS32, EmbeddedRKPair.embedMethod, Fin.sum_univ_four]; norm_num,
           fun i => by fin_cases i <;>
             simp [rkBS32, EmbeddedRKPair.embedMethod, Fin.sum_univ_four] <;> norm_num⟩

/-- The BS3(2) main method has order 3. -/
theorem rkBS32_main_order3 : rkBS32.mainMethod.HasOrderGe3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- order1: ∑ bᵢ = 2/9 + 1/3 + 4/9 + 0 = 1
    simp [ButcherTableau.order1, rkBS32, EmbeddedRKPair.mainMethod, Fin.sum_univ_four]; norm_num
  · -- order2: ∑ bᵢcᵢ = 0 + 1/6 + 1/3 + 0 = 1/2
    simp [ButcherTableau.order2, rkBS32, EmbeddedRKPair.mainMethod, Fin.sum_univ_four]; norm_num
  · -- order3a: ∑ bᵢcᵢ² = 0 + 1/12 + 3/16·4/9 = 1/3
    simp [ButcherTableau.order3a, rkBS32, EmbeddedRKPair.mainMethod, Fin.sum_univ_four]; norm_num
  · -- order3b: ∑ᵢⱼ bᵢ aᵢⱼ cⱼ = 1/6
    simp [ButcherTableau.order3b, rkBS32, EmbeddedRKPair.mainMethod, Fin.sum_univ_four]; norm_num

/-- The BS3(2) main method does NOT have order 4: ∑ bᵢcᵢ³ = 11/48 ≠ 1/4. -/
theorem rkBS32_main_not_order4 : ¬rkBS32.mainMethod.HasOrderGe4 := by
  intro ⟨_, _, _, _, h4a, _, _, _⟩
  simp [ButcherTableau.order4a, rkBS32, EmbeddedRKPair.mainMethod, Fin.sum_univ_four] at h4a
  norm_num at h4a

/-- The BS3(2) embedding has order 2. -/
theorem rkBS32_embed_order2 : rkBS32.embedMethod.HasOrderGe2 := by
  constructor
  · simp [ButcherTableau.order1, rkBS32, EmbeddedRKPair.embedMethod, Fin.sum_univ_four]; norm_num
  · simp [ButcherTableau.order2, rkBS32, EmbeddedRKPair.embedMethod, Fin.sum_univ_four]; norm_num

/-- The BS3(2) embedding does NOT have order 3: ∑ b̂ᵢcᵢ² = 3/8 ≠ 1/3. -/
theorem rkBS32_embed_not_order3 : ¬rkBS32.embedMethod.HasOrderGe3 := by
  intro ⟨_, _, h3a, _⟩
  simp [ButcherTableau.order3a, rkBS32, EmbeddedRKPair.embedMethod, Fin.sum_univ_four] at h3a
  norm_num at h3a

/-- The BS3(2) main method is stiffly accurate: b = last row of A. -/
theorem rkBS32_main_stifflyAccurate : rkBS32.mainMethod.IsStifflyAccurate := by
  intro i; fin_cases i <;> simp [rkBS32, EmbeddedRKPair.mainMethod]

/-- The BS3(2) main method has non-negative weights. -/
theorem rkBS32_main_nonNegWeights : rkBS32.mainMethod.HasNonNegWeights := by
  intro i; fin_cases i <;> simp [rkBS32, EmbeddedRKPair.mainMethod] <;> norm_num

/-- The BS3(2) embedding has strictly positive weights. -/
theorem rkBS32_embed_posWeights : ∀ i : Fin 4, 0 < rkBS32.bHat i := by
  intro i; fin_cases i <;> simp [rkBS32] <;> norm_num

/-- **BS3(2) has the FSAL property**: the main method is stiffly accurate
  and the first node is c₁ = 0. This means only 3 new function evaluations
  per step instead of 4.
  Reference: Bogacki & Shampine (1989). -/
theorem rkBS32_FSAL : EmbeddedRKPair.HasFSAL rkBS32 where
  stiffly_accurate := rkBS32_main_stifflyAccurate
  first_node_zero := by simp [rkBS32]

/-- Error weights sum to zero. -/
theorem rkBS32_errorWeights_sum :
    ∑ i : Fin 4, rkBS32.errorWeights i = 0 :=
  rkBS32.errorWeights_sum_zero rkBS32_consistent

/-! ## Simplifying Assumptions for BS3(2)

The BS3(2) main method satisfies B(3) and C(1), consistent with order 3.
It does NOT satisfy C(2), showing that the stage order is exactly 1. -/

/-- BS3(2) main method satisfies B(3): weights integrate polynomials of degree ≤ 2. -/
theorem rkBS32_main_B3 : rkBS32.mainMethod.SatisfiesB 3 := by
  intro k hk1 hk2
  interval_cases k <;>
    simp [rkBS32, EmbeddedRKPair.mainMethod, Fin.sum_univ_four] <;> norm_num

/-- BS3(2) main method satisfies C(1): row-sum condition. -/
theorem rkBS32_main_C1 : rkBS32.mainMethod.SatisfiesC 1 := by
  rw [ButcherTableau.satisfiesC_one_iff]
  exact rkBS32_consistent.main_consistent.row_sum

/-- BS3(2) main method does NOT satisfy C(2): stage order is 1.
  At i = 0: ∑ⱼ a₀ⱼcⱼ = 0 but c₀²/2 = 0. OK.
  At i = 1: ∑ⱼ a₁ⱼcⱼ = 0 but c₁²/2 = 1/8. Fails! -/
theorem rkBS32_main_not_C2 : ¬rkBS32.mainMethod.SatisfiesC 2 := by
  intro hC
  have h := hC 2 (by omega) le_rfl 1
  simp [rkBS32, EmbeddedRKPair.mainMethod, Fin.sum_univ_four] at h
  norm_num at h

/-! ## Summary Table

| Pair        | Stages | Main Order | Embed Order | FSAL? | Explicit? |
|-------------|--------|------------|-------------|-------|-----------|
| Heun–Euler  | 2      | 2          | 1           | ✗     | ✓         |
| BS3(2)      | 4      | 3          | 2           | ✓     | ✓         |

Key properties:
- Both pairs are explicit and consistent
- Error estimate comes "for free" from the weight difference d = b − b̂
- BS3(2) has FSAL: only 3 new function evaluations per step (not 4)
- The error weights always sum to zero for consistent pairs

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 2.7 and Chapter 5.
-/
