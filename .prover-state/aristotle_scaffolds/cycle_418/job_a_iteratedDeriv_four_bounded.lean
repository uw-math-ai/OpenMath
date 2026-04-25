import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Cycle 418, Job A: A `C^4` function has its fourth derivative bounded
on every compact interval `[a, b]`.

Mirror of `iteratedDeriv_three_bounded_on_Icc` from
`OpenMath/LMMAB2Convergence.lean` (lines 251–263), one Taylor order
higher. -/

namespace LMM

theorem cycle418_iteratedDeriv_four_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 y t| ≤ M := by
  sorry

end LMM
