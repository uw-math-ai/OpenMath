import OpenMath.LMMTruncationOp

/-! Cycle 406, Job A: forward-Euler local truncation residual bound on a
finite horizon, given a `C^3` solution.

Goal: provide uniform constants `(C, δ)` such that the textbook
forward-Euler one-step residual `y(t+h) - y(t) - h * y'(t)` is bounded by
`C * h^2` for all `0 < h ≤ δ` and all sample points
`t = t₀ + n*h ∈ [t₀, t₀+T]`. -/

namespace LMM

theorem cycle406_forwardEuler_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (t₀ T : ℝ) (hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        t₀ + (n : ℝ) * h ∈ Set.Icc t₀ (t₀ + T) →
        |y (t₀ + ((n : ℝ) + 1) * h) - y (t₀ + (n : ℝ) * h)
            - h * deriv y (t₀ + (n : ℝ) * h)|
          ≤ C * h ^ 2 := by
  sorry

end LMM
