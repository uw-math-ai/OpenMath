import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Linear systems of differential equations (Butcher §111)
-/

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

/-- Time derivative: `(d/dx) y(x) = A · y(x)`. -/
theorem closedFormSolution_hasDerivAt
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : ℝ) (y₀ : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun t => closedFormSolution A x₀ y₀ t)
      (A *ᵥ closedFormSolution A x₀ y₀ x) x := by
  sorry

/-- One-parameter group law for the matrix exponential of `A`. -/
theorem exp_smul_add (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • A) =
      NormedSpace.exp (s • A) * NormedSpace.exp (t • A) := by
  sorry

end LinearODE
