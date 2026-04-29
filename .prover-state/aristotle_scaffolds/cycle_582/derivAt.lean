import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

namespace LinearODE

variable {n : ℕ}

/-- Closed-form solution `y(x) := exp((x − x₀) • A) · y₀` of the linear
IVP `y' = A y`, `y(x₀) = y₀`. -/
noncomputable def closedFormSolution
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : ℝ) (y₀ : Fin n → ℝ)
    (x : ℝ) : Fin n → ℝ :=
  NormedSpace.exp ((x - x₀) • A) *ᵥ y₀

/-- Time derivative: `(d/dx) y(x) = A · y(x)`. -/
theorem closedFormSolution_hasDerivAt
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : ℝ) (y₀ : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun t => closedFormSolution A x₀ y₀ t)
      (A *ᵥ closedFormSolution A x₀ y₀ x) x := by
  sorry

end LinearODE
