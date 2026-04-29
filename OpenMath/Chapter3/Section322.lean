import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Frontend

/-!
# Butcher §322 — Methods of order 4 (Lemma 322A)

This file formalises Lemma 322A from Butcher's *Numerical Methods for
Ordinary Differential Equations* (3rd ed., page 197).

## Textbook statement (Lemma 322A, quoted verbatim from `lem_322A.json`)

> If `P` and `Q` are each `3 × 3` matrices such that their product has
> the form
>
>     PQ = ⎡ r₁₁  r₁₂  0 ⎤
>          ⎢ r₂₁  r₂₂  0 ⎥
>          ⎣  0    0   0 ⎦
>
> where `det [r₁₁ r₁₂ ; r₂₁ r₂₂] ≠ 0`, then either the last row of `P`
> is zero or the last column of `Q` is zero.

## Textbook proof

> Because `PQ` is singular, either `P` is singular or `Q` is singular.
> In the first case, let `u ≠ 0` be such that `uᵀP = 0`, and therefore
> `uᵀPQ = 0`; in the second case, let `v ≠ 0` be such that `Qv = 0`,
> and therefore `PQv = 0`. Because of the form of `PQ`, this implies
> that the first two components of `u` (or, respectively, the first
> two components of `v`) are zero.

## Faithfulness notes

* The textbook works over an unspecified field (the surrounding RK
  context is over `ℝ`); we specialise to `ℝ`. Generalising to any
  field would be straightforward (`ℝ` is used only to invoke
  `IsDomain` for `exists_vecMul_eq_zero_iff`).
* The hypothesis `(P*Q) i 2 = 0 ∧ (P*Q) 2 i = 0` for all `i : Fin 3`
  literally encodes "the last row and last column of `PQ` are zero".
* The hypothesis `h_det` literally encodes the textbook's
  `det [[r₁₁, r₁₂], [r₂₁, r₂₂]] ≠ 0`, where `rᵢⱼ = (P*Q)(i-1)(j-1)`.
-/

namespace OpenMath.Chapter3.Section322

open Matrix

/-- **Lemma 322A** — If `P` and `Q` are `3 × 3` real matrices whose
product has the block form
```
PQ = ⎡ r₁₁ r₁₂ 0 ⎤
     ⎢ r₂₁ r₂₂ 0 ⎥
     ⎣  0   0  0 ⎦
```
with non-singular `2 × 2` upper-left block, then either the last row
of `P` is zero or the last column of `Q` is zero. -/
theorem order_four_block_zero_decomposition
    (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (h_block : ∀ i, (P * Q) i 2 = 0 ∧ (P * Q) 2 i = 0)
    (h_det :
        (P * Q) 0 0 * (P * Q) 1 1 - (P * Q) 0 1 * (P * Q) 1 0 ≠ 0) :
    (∀ j, P 2 j = 0) ∨ (∀ i, Q i 2 = 0) := by
  -- Step 1: det (P*Q) = 0 since the third row (and column) of P*Q is zero.
  have hPQ_22 : (P * Q) 2 2 = 0 := (h_block 2).1
  have hPQ_02 : (P * Q) 0 2 = 0 := (h_block 0).1
  have hPQ_12 : (P * Q) 1 2 = 0 := (h_block 1).1
  have hPQ_20 : (P * Q) 2 0 = 0 := (h_block 0).2
  have hPQ_21 : (P * Q) 2 1 = 0 := (h_block 1).2
  have hdet_PQ : (P * Q).det = 0 := by
    rw [Matrix.det_fin_three]
    rw [hPQ_02, hPQ_12, hPQ_20, hPQ_21, hPQ_22]
    ring
  -- Step 2: det P * det Q = 0 ⇒ det P = 0 ∨ det Q = 0.
  have hdetPQ_split : P.det = 0 ∨ Q.det = 0 := by
    have : P.det * Q.det = 0 := by
      rw [← Matrix.det_mul]; exact hdet_PQ
    exact mul_eq_zero.mp this
  -- Step 3: case split.
  rcases hdetPQ_split with hP | hQ
  · -- Case det P = 0: ∃ u ≠ 0 with u ᵥ* P = 0.
    left
    have hu : ∃ u ≠ 0, u ᵥ* P = 0 :=
      Matrix.exists_vecMul_eq_zero_iff.mpr hP
    obtain ⟨u, hu_ne, hu_vec⟩ := hu
    -- Step 4: u ᵥ* (P*Q) = 0 too.
    have hu_PQ : u ᵥ* (P * Q) = 0 := by
      rw [← Matrix.vecMul_vecMul, hu_vec, Matrix.zero_vecMul]
    -- Step 5: extract the components of `u ᵥ* (P*Q)`.
    -- The j-th component is ∑ k, u k * (P*Q) k j.
    have hPQ_comp : ∀ j : Fin 3,
        u 0 * (P * Q) 0 j + u 1 * (P * Q) 1 j + u 2 * (P * Q) 2 j = 0 := by
      intro j
      have hj : (u ᵥ* (P * Q)) j = 0 := by rw [hu_PQ]; rfl
      have : (u ᵥ* (P * Q)) j =
          u 0 * (P * Q) 0 j + u 1 * (P * Q) 1 j + u 2 * (P * Q) 2 j := by
        show ∑ i : Fin 3, u i * (P * Q) i j =
            u 0 * (P * Q) 0 j + u 1 * (P * Q) 1 j + u 2 * (P * Q) 2 j
        rw [Fin.sum_univ_three]
      linarith [this ▸ hj]
    -- Step 6: combining hPQ_20, hPQ_21 (3rd row of P*Q is 0) gives a
    -- 2x2 system in (u 0, u 1) with non-singular coefficient matrix.
    have hsys0 : u 0 * (P * Q) 0 0 + u 1 * (P * Q) 1 0 = 0 := by
      have := hPQ_comp 0
      rw [hPQ_20, mul_zero, add_zero] at this
      exact this
    have hsys1 : u 0 * (P * Q) 0 1 + u 1 * (P * Q) 1 1 = 0 := by
      have := hPQ_comp 1
      rw [hPQ_21, mul_zero, add_zero] at this
      exact this
    -- From h_det ((P*Q)00 * (P*Q)11 - (P*Q)01 * (P*Q)10 ≠ 0):
    -- multiply hsys0 by (P*Q) 1 1 and hsys1 by (P*Q) 1 0 and subtract.
    have hu0_zero : u 0 = 0 := by
      have e0 : u 0 * ((P * Q) 0 0 * (P * Q) 1 1) +
          u 1 * ((P * Q) 1 0 * (P * Q) 1 1) = 0 := by
        have := congrArg (· * (P * Q) 1 1) hsys0
        simp only [add_mul, mul_assoc, zero_mul] at this
        linarith
      have e1 : u 0 * ((P * Q) 0 1 * (P * Q) 1 0) +
          u 1 * ((P * Q) 1 1 * (P * Q) 1 0) = 0 := by
        have := congrArg (· * (P * Q) 1 0) hsys1
        simp only [add_mul, mul_assoc, zero_mul] at this
        linarith
      have e2 : u 0 * ((P * Q) 0 0 * (P * Q) 1 1 -
          (P * Q) 0 1 * (P * Q) 1 0) = 0 := by
        have key : u 0 * ((P * Q) 0 0 * (P * Q) 1 1) -
            u 0 * ((P * Q) 0 1 * (P * Q) 1 0) = 0 := by
          have := sub_eq_zero.mpr (e0.trans e1.symm)
          nlinarith [this]
        linarith [key]
      rcases mul_eq_zero.mp e2 with h | h
      · exact h
      · exact (h_det h).elim
    have hu1_zero : u 1 = 0 := by
      -- From hsys0 with u 0 = 0: u 1 * (P*Q) 1 0 = 0.
      -- From hsys1 with u 0 = 0: u 1 * (P*Q) 1 1 = 0.
      -- So u 1 * det = 0, hence u 1 = 0.
      have e0 : u 1 * (P * Q) 1 0 = 0 := by
        have := hsys0; rw [hu0_zero, zero_mul, zero_add] at this; exact this
      have e1 : u 1 * (P * Q) 1 1 = 0 := by
        have := hsys1; rw [hu0_zero, zero_mul, zero_add] at this; exact this
      -- u 1 * (PQ 0 0 * PQ 1 1 - PQ 0 1 * PQ 1 0). Using e0 and e1:
      -- multiplying e1 by (PQ) 0 0 and e0 by (PQ) 0 1 gives the det.
      have e2 : u 1 * ((P * Q) 0 0 * (P * Q) 1 1 -
          (P * Q) 0 1 * (P * Q) 1 0) = 0 := by
        have h1 : u 1 * (P * Q) 1 1 * (P * Q) 0 0 = 0 := by
          rw [e1]; ring
        have h0 : u 1 * (P * Q) 1 0 * (P * Q) 0 1 = 0 := by
          rw [e0]; ring
        nlinarith [h1, h0]
      rcases mul_eq_zero.mp e2 with h | h
      · exact h
      · exact (h_det h).elim
    -- Step 7: u 2 ≠ 0 (since u ≠ 0 and u 0 = u 1 = 0).
    have hu2_ne : u 2 ≠ 0 := by
      intro h2
      apply hu_ne
      funext i
      fin_cases i
      · exact hu0_zero
      · exact hu1_zero
      · exact h2
    -- Step 8: from u ᵥ* P = 0, the j-th component:
    --   u 0 * P 0 j + u 1 * P 1 j + u 2 * P 2 j = 0.
    -- With u 0 = u 1 = 0, this is u 2 * P 2 j = 0, so P 2 j = 0.
    intro j
    have hj : (u ᵥ* P) j = 0 := by rw [hu_vec]; rfl
    have hj_expand : u 0 * P 0 j + u 1 * P 1 j + u 2 * P 2 j = 0 := by
      have : (u ᵥ* P) j = u 0 * P 0 j + u 1 * P 1 j + u 2 * P 2 j := by
        show ∑ i : Fin 3, u i * P i j =
            u 0 * P 0 j + u 1 * P 1 j + u 2 * P 2 j
        rw [Fin.sum_univ_three]
      linarith [this ▸ hj]
    rw [hu0_zero, hu1_zero, zero_mul, zero_mul, zero_add, zero_add] at hj_expand
    exact (mul_eq_zero.mp hj_expand).resolve_left hu2_ne
  · -- Case det Q = 0 (symmetric): ∃ v ≠ 0 with Q *ᵥ v = 0.
    right
    have hv : ∃ v ≠ 0, Q *ᵥ v = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hQ
    obtain ⟨v, hv_ne, hv_vec⟩ := hv
    -- (P*Q) *ᵥ v = 0 too.
    have hv_PQ : (P * Q) *ᵥ v = 0 := by
      rw [← Matrix.mulVec_mulVec, hv_vec, Matrix.mulVec_zero]
    -- The i-th component is ∑ k, (P*Q) i k * v k.
    have hPQ_comp : ∀ i : Fin 3,
        (P * Q) i 0 * v 0 + (P * Q) i 1 * v 1 + (P * Q) i 2 * v 2 = 0 := by
      intro i
      have hi : ((P * Q) *ᵥ v) i = 0 := by rw [hv_PQ]; rfl
      have : ((P * Q) *ᵥ v) i =
          (P * Q) i 0 * v 0 + (P * Q) i 1 * v 1 + (P * Q) i 2 * v 2 := by
        show ∑ j : Fin 3, (P * Q) i j * v j =
            (P * Q) i 0 * v 0 + (P * Q) i 1 * v 1 + (P * Q) i 2 * v 2
        rw [Fin.sum_univ_three]
      linarith [this ▸ hi]
    -- Using third column of PQ = 0: (PQ) i 2 = 0 ⇒ system in (v 0, v 1).
    have hsys0 : (P * Q) 0 0 * v 0 + (P * Q) 0 1 * v 1 = 0 := by
      have := hPQ_comp 0
      rw [hPQ_02, zero_mul, add_zero] at this
      exact this
    have hsys1 : (P * Q) 1 0 * v 0 + (P * Q) 1 1 * v 1 = 0 := by
      have := hPQ_comp 1
      rw [hPQ_12, zero_mul, add_zero] at this
      exact this
    -- Mirror the case-1 algebra: solve the 2×2 system.
    have hv0_zero : v 0 = 0 := by
      -- multiply hsys0 by (PQ) 1 1 and hsys1 by (PQ) 0 1, subtract:
      -- v 0 * ((PQ) 0 0 * (PQ) 1 1 - (PQ) 0 1 * (PQ) 1 0) = 0.
      have e2 : v 0 * ((P * Q) 0 0 * (P * Q) 1 1 -
          (P * Q) 0 1 * (P * Q) 1 0) = 0 := by
        have e0 : ((P * Q) 0 0 * v 0 + (P * Q) 0 1 * v 1) * (P * Q) 1 1 = 0 := by
          rw [hsys0]; ring
        have e1 : ((P * Q) 1 0 * v 0 + (P * Q) 1 1 * v 1) * (P * Q) 0 1 = 0 := by
          rw [hsys1]; ring
        nlinarith [e0, e1]
      rcases mul_eq_zero.mp e2 with h | h
      · exact h
      · exact (h_det h).elim
    have hv1_zero : v 1 = 0 := by
      have e0 : (P * Q) 0 1 * v 1 = 0 := by
        have := hsys0; rw [hv0_zero, mul_zero, zero_add] at this; exact this
      have e1 : (P * Q) 1 1 * v 1 = 0 := by
        have := hsys1; rw [hv0_zero, mul_zero, zero_add] at this; exact this
      have e2 : v 1 * ((P * Q) 0 0 * (P * Q) 1 1 -
          (P * Q) 0 1 * (P * Q) 1 0) = 0 := by
        have h1 : (P * Q) 1 1 * v 1 * (P * Q) 0 0 = 0 := by rw [e1]; ring
        have h0 : (P * Q) 0 1 * v 1 * (P * Q) 1 0 = 0 := by rw [e0]; ring
        nlinarith [h1, h0]
      rcases mul_eq_zero.mp e2 with h | h
      · exact h
      · exact (h_det h).elim
    have hv2_ne : v 2 ≠ 0 := by
      intro h2
      apply hv_ne
      funext i
      fin_cases i
      · exact hv0_zero
      · exact hv1_zero
      · exact h2
    -- From Q *ᵥ v = 0, the i-th component: Q i 0 * v 0 + Q i 1 * v 1 + Q i 2 * v 2 = 0.
    -- With v 0 = v 1 = 0, this is Q i 2 * v 2 = 0, so Q i 2 = 0.
    intro i
    have hi : (Q *ᵥ v) i = 0 := by rw [hv_vec]; rfl
    have hi_expand : Q i 0 * v 0 + Q i 1 * v 1 + Q i 2 * v 2 = 0 := by
      have : (Q *ᵥ v) i = Q i 0 * v 0 + Q i 1 * v 1 + Q i 2 * v 2 := by
        show ∑ j : Fin 3, Q i j * v j =
            Q i 0 * v 0 + Q i 1 * v 1 + Q i 2 * v 2
        rw [Fin.sum_univ_three]
      linarith [this ▸ hi]
    rw [hv0_zero, hv1_zero, mul_zero, mul_zero, zero_add, zero_add] at hi_expand
    exact (mul_eq_zero.mp hi_expand).resolve_right hv2_ne

/-! ### Sanity-check witness

Concrete `P` and `Q` for which the lemma's hypotheses hold and the
disjunction is non-vacuous. We take `Q = I` (identity) and `P` equal
to the `3 × 3` matrix with the standard basis 2×2 block in the upper
left and zeros in the third row and third column. Then `P * Q = P`,
the third row and column of `P` are zero, the upper-left 2×2 block
is the identity (det = 1 ≠ 0), and the conclusion `∀ j, P 2 j = 0`
holds. -/
example :
    let P : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
    let Q : Matrix (Fin 3) (Fin 3) ℝ := 1
    (∀ j, P 2 j = 0) ∨ (∀ i, Q i 2 = 0) := by
  intro P _
  left
  intro j
  fin_cases j <;> rfl

end OpenMath.Chapter3.Section322
