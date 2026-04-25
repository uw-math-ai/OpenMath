import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Cycle 418, Job C: Third-order Taylor (Lagrange) remainder for
`deriv y`.

Mirror of `derivY_second_order_taylor_remainder` from
`OpenMath/LMMAB2Convergence.lean` (lines 341–412), one Taylor order
higher. -/

namespace LMM

theorem cycle418_derivY_third_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t|
      ≤ M / 6 * r ^ 3 := by
  sorry

end LMM
