import OpenMath.ANStability

open Finset

noncomputable section

namespace ButcherTableau

variable {s : ℕ}

private def cycle111_imagBasis (v : Fin s → ℝ) (τ : ℝ) : Fin s → ℂ :=
  fun i => Complex.I * (τ : ℂ) * (v i : ℂ)

/--
For the purely imaginary diagonal perturbation `Z = iτ diag(v)`, the determinant
`det (I - A Z)` is nonzero for sufficiently small positive `τ`.
-/
theorem cycle111_imagBasis_det_ne_zero_small (t : ButcherTableau s) (v : Fin s → ℝ) :
    ∃ τ : ℝ, 0 < τ ∧
      (1 - t.Aℂ * Matrix.diagonal (cycle111_imagBasis v τ)).det ≠ 0 := by
  sorry

end ButcherTableau
