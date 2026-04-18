import OpenMath.ANStability

open Finset

noncomputable section

namespace ButcherTableau

variable {s : ℕ}

private def cycle111_imagBasis (v : Fin s → ℝ) (τ : ℝ) : Fin s → ℂ :=
  fun i => Complex.I * (τ : ℂ) * (v i : ℂ)

/--
Standalone version of the remaining cycle-111 sorry. The intended proof is the
small-`τ` expansion of `|R(iτ diag(v))|²`.
-/
theorem cycle111_norm_stabilityFn_imagBasis_gt_one
    (t : ButcherTableau s) (v : Fin s → ℝ)
    (hv : ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j < 0) :
    ∃ τ : ℝ, 0 < τ ∧
      (1 - t.Aℂ * Matrix.diagonal (cycle111_imagBasis v τ)).det ≠ 0 ∧
      1 < ‖t.stabilityFnDiag (cycle111_imagBasis v τ)‖ := by
  sorry

end ButcherTableau
