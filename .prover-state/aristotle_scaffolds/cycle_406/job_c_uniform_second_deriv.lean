import OpenMath.LMMTruncationOp

/-! Cycle 406, Job C: uniform bound on `|y''|` over a compact interval,
given `ContDiff ℝ 3 y`. Useful glue lemma for the forward-Euler local
truncation residual bound. -/

namespace LMM

/-- A `C^3` function has its second derivative bounded on every compact
interval. -/
theorem cycle406_iteratedDeriv_two_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 y t| ≤ M := by
  sorry

/-- A `C^3` function has its third derivative bounded on every compact
interval. -/
theorem cycle406_iteratedDeriv_three_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 3 y t| ≤ M := by
  sorry

end LMM
