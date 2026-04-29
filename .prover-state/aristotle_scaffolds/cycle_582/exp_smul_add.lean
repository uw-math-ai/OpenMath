import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

namespace LinearODE

variable {n : ℕ}

/-- One-parameter group law for the matrix exponential of `A`. -/
theorem exp_smul_add (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • A) =
      NormedSpace.exp (s • A) * NormedSpace.exp (t • A) := by
  sorry

end LinearODE
