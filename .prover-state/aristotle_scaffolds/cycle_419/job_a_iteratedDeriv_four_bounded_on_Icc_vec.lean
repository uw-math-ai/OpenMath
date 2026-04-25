import OpenMath.LMMAB3Convergence

namespace LMM

theorem cycle419_iteratedDeriv_four_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 4 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 4 y t‖ ≤ M := by
  sorry

end LMM
