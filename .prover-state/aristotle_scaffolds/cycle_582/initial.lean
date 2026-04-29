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

/-- The closed-form solution attains the initial condition at `x = x₀`. -/
theorem closedFormSolution_initial
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : ℝ) (y₀ : Fin n → ℝ) :
    closedFormSolution A x₀ y₀ x₀ = y₀ := by
  sorry

end LinearODE
