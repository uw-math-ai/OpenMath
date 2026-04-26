import Mathlib

/-! # Adams–Bashforth 6-step method – vector formulation

Defines the concrete AB6 iteration and residual with the standard AB6 coefficients.
-/

open Finset BigOperators

namespace LMM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Concrete AB6 iteration.

  `y(n+6) = y(n+5) + h • (−475/1440 · f(t₀+n·h, y(n)) + 2877/1440 · f(…, y(n+1))
            − 7298/1440 · f(…, y(n+2)) + 9982/1440 · f(…, y(n+3))
            − 7923/1440 · f(…, y(n+4)) + 4277/1440 · f(…, y(n+5)))`.
-/
noncomputable def ab6IterVec
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) : ℕ → E
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | (n + 6) =>
    ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
      + h • ((-475 / 1440 : ℝ) • f (t₀ + (↑n) * h)
               (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n)
           + (2877 / 1440 : ℝ) • f (t₀ + (↑n + 1) * h)
               (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1))
           + (-7298 / 1440 : ℝ) • f (t₀ + (↑n + 2) * h)
               (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2))
           + (9982 / 1440 : ℝ) • f (t₀ + (↑n + 3) * h)
               (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3))
           + (-7923 / 1440 : ℝ) • f (t₀ + (↑n + 4) * h)
               (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4))
           + (4277 / 1440 : ℝ) • f (t₀ + (↑n + 5) * h)
               (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)))

/-- Concrete AB6 residual at base-point `t`.

  `τ(t) = y(t+6h) − y(t+5h) − h • ∑ (AB6 coeffs) · y′(t+j·h)`.
-/
noncomputable def ab6VecResidual (h : ℝ) (t : ℝ) (y : ℝ → E) : E :=
  y (t + 6 * h) - y (t + 5 * h)
    - h • ((-475 / 1440 : ℝ) • deriv y t
         + (2877 / 1440 : ℝ) • deriv y (t + 1 * h)
         + (-7298 / 1440 : ℝ) • deriv y (t + 2 * h)
         + (9982 / 1440 : ℝ) • deriv y (t + 3 * h)
         + (-7923 / 1440 : ℝ) • deriv y (t + 4 * h)
         + (4277 / 1440 : ℝ) • deriv y (t + 5 * h))

end LMM
