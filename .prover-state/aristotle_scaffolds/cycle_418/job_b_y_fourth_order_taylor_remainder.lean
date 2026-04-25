import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Cycle 418, Job B: Fourth-order Taylor (Lagrange) remainder for `y`.

Mirror of `y_third_order_taylor_remainder` from
`OpenMath/LMMAB2Convergence.lean` (lines 269–335), one Taylor order
higher. -/

namespace LMM

theorem cycle418_y_fourth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t|
      ≤ M / 24 * r ^ 4 := by
  sorry

end LMM
