import OpenMath.LMMABGenericConvergence

/-! # Adams–Bashforth 5-step method – scalar definitions

Defines the explicit scalar AB5 iteration `ab5Iter`.
-/

namespace LMM

/-! ## Scalar AB5 iteration -/

/-- Explicit scalar AB5 iteration with five named initial values. -/
noncomputable def ab5Iter (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then y₀
  else if n = 1 then y₁
  else if n = 2 then y₂
  else if n = 3 then y₃
  else if n = 4 then y₄
  else
    ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n - 1) +
      h * ((251 / 720) * f (t₀ + ↑(n - 5) * h) (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n - 5))
         + (-1274 / 720) * f (t₀ + ↑(n - 4) * h) (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n - 4))
         + (2616 / 720) * f (t₀ + ↑(n - 3) * h) (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n - 3))
         + (-2774 / 720) * f (t₀ + ↑(n - 2) * h) (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n - 2))
         + (1901 / 720) * f (t₀ + ↑(n - 1) * h) (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n - 1)))
termination_by n

end LMM
