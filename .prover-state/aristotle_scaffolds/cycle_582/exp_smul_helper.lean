import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

namespace LinearODE

variable {n : ℕ}

/-- Time-derivative helper: `(d/dt) exp(t • A) = A · exp(t • A)`. -/
theorem hasDerivAt_exp_smul_matrix
    (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A))
      (A * NormedSpace.exp (t • A)) t := by
  sorry

end LinearODE
