import OpenMath.LMMTruncationOp

/-! Cycle 406, Job B: forward-Euler global error bound on a finite
horizon, assembled from the one-step Lipschitz error recurrence and the
local truncation residual bound, via
`lmm_error_bound_from_local_truncation`.

Hypotheses:
- `y : ℝ → ℝ` is `C^3` (so the local residual is `O(h^2)`).
- `f : ℝ → ℝ → ℝ` is Lipschitz in its second argument with constant `L`.
- `y' = f(t, y)` along the trajectory: `deriv y t = f t (y t)` for all `t`.

Goal: produce constants `(K, δ)` such that for all `0 < h ≤ δ` and all
`N : ℕ` with `N * h ≤ T`, the global error of the Forward-Euler iteration
starting from `y₀ = y t₀` is bounded by `K * h`. -/

namespace LMM

theorem cycle406_forwardEuler_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ N : ℕ, (N : ℝ) * h ≤ T →
        |forwardEulerIter h f t₀ (y t₀) N - y (t₀ + (N : ℝ) * h)|
          ≤ K * h := by
  sorry

end LMM
