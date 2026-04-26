import Mathlib

/-! # Scalar AB6 iteration

Defines the 6-step Adams–Bashforth iteration with explicit scalar arguments
(no vector / `Fin` packaging).
-/

namespace LMM

/-- Scalar 6-step Adams–Bashforth iteration.

Takes the step size `h`, ODE right-hand side `f(t, y)`, initial time `t₀`,
and the six starting values `y₀, …, y₅` individually.  Returns the `n`-th
iterate. -/
noncomputable def ab6Iter (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) :
    ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | (n + 6) =>
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5) +
      h * ((4277 / 1440) * f (t₀ + (↑n + 5) * h) (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5))
          - (7923 / 1440) * f (t₀ + (↑n + 4) * h) (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4))
          + (9982 / 1440) * f (t₀ + (↑n + 3) * h) (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3))
          - (7298 / 1440) * f (t₀ + (↑n + 2) * h) (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2))
          + (2877 / 1440) * f (t₀ + (↑n + 1) * h) (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1))
          - (475 / 1440) * f (t₀ + ↑n * h) (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n))

end LMM
