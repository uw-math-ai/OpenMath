import Mathlib

namespace QuadraticLyapunov

open Matrix

variable {n : ℕ}

def QFPosDef (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Pᵀ = P ∧ ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ P.mulVec v

-- helper: continuous function
example (P : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun x : Fin n → ℝ => x ⬝ᵥ P.mulVec x) := by
  unfold dotProduct Matrix.mulVec
  apply continuous_finset_sum
  intro i _
  apply Continuous.mul (continuous_apply i)
  apply continuous_finset_sum
  intro j _
  exact (continuous_apply j).const_smul _ |>.const_smul _

example : IsCompact ({x : Fin n → ℝ | ∑ i, (x i)^2 = 1}) := by
  sorry

end QuadraticLyapunov
