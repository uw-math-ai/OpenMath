import OpenMath.LMMTruncationOp

/-! Cycle 406, Job D: pointwise Taylor residual bound for the forward-Euler
one-step truncation on a `C^3` function.

Given `ContDiff ℝ 3 y` and a uniform bound `M` on `|y''|` over a compact
sample interval, the textbook quadratic remainder
`|y(t+h) - y(t) - h * y'(t)| ≤ M/2 * h^2` holds for `h ≥ 0` and `t, t+h`
in the sample interval. -/

namespace LMM

/-- Pointwise Lagrange remainder: if `y` is `C^3` and `|y''| ≤ M` on
`[a, b]`, then for `t, t + h ∈ [a, b]` with `h ≥ 0` we have
`|y(t+h) - y(t) - h * y'(t)| ≤ M / 2 * h^2`. -/
theorem cycle406_forwardEuler_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) {a b M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b) (hth : t + h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + h) - y t - h * deriv y t| ≤ M / 2 * h ^ 2 := by
  sorry

end LMM
