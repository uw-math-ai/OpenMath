/-
Cycle 138 Aristotle Job B: close `doublyCompanionMatrix_det_factorization`
specifically at `n = 2` (Butcher Theorem 550A specialized).

## Theorem statement at n = 2

For the doubly companion matrix X built from α, β : Fin 2 → ℂ,
the matrix is

    X = [[-α 0, -α 1 - β 1],
         [1,    -β 0       ]]

so by Matrix.det_fin_two,
    det(I - z X) = (1 + z α 0)(1 + z β 0) - z² · (-α 1 - β 1) · 1
                 = 1 + (α 0 + β 0) z + (α 0 · β 0 + α 1 + β 1) z²

while the polynomial product is
    α(z) · β(z) = (1 + α 0 · z + α 1 · z²)(1 + β 0 · z + β 1 · z²)
                = 1 + (α 0 + β 0) z
                  + (α 0 β 0 + α 1 + β 1) z²
                  + (α 0 β 1 + α 1 β 0) z³
                  + (α 1 β 1) z⁴

So the residue is:
    -[(α 0 β 1 + α 1 β 0) z³ + (α 1 β 1) z⁴]
This is `O(z³) = O(z^{2+1})` as z → 0 in ℂ.

## Suggested proof structure

1. Compute the LHS residue as a pointwise polynomial in z by
   `Matrix.det_fin_two` + `simp [doublyCompanionMatrix]` followed by
   `ring`.
2. Express the residue as `g(z) * z^3` for an explicit polynomial g
   in z, α, β.
3. Use `Asymptotics.IsBigO.const_mul_left` (or
   `isBigO_refl.const_mul_left`) to conclude.

This is parallel to the n = 1 case already closed in Section550.lean
(`doublyCompanionMatrix_det_factorization_n_one`).
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace OpenMath.Chapter5.Section550

open Asymptotics

def doublyCompanionMatrix {n : ℕ} (α β : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if h0 : i.val = 0 then
    if hj : j.val + 1 = n then
      -α ⟨n - 1, by omega⟩ - β ⟨n - 1, by omega⟩
    else
      -α j
  else if hj : j.val + 1 = n then
    -β ⟨n - i.val - 1, by omega⟩
  else if i.val = j.val + 1 then
    1
  else
    0

noncomputable def alphaPoly {n : ℕ} (α : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, α i * z ^ (i.val + 1)

noncomputable def betaPoly {n : ℕ} (β : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, β i * z ^ (i.val + 1)

theorem doublyCompanionMatrix_det_factorization_n_two
    (α β : Fin 2 → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ 3) := by
  sorry

end OpenMath.Chapter5.Section550
