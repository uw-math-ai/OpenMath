import Mathlib
import OpenMath.LMMABGenericConvergence

/-! Adams–Bashforth 4-step (AB4) specific definitions. -/

namespace LMM

open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- AB4 iteration with explicit pattern-matching on the four seed values. -/
noncomputable def ab4IterVec (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ : E) : ℕ → E
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | (n + 4) =>
    ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3) +
      h • ((55 / 24 : ℝ) • f (t₀ + (↑(n + 3) : ℝ) * h)
              (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)) +
           (-(59 : ℝ) / 24) • f (t₀ + (↑(n + 2) : ℝ) * h)
              (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 2)) +
           ((37 : ℝ) / 24) • f (t₀ + (↑(n + 1) : ℝ) * h)
              (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 1)) +
           (-(9 : ℝ) / 24) • f (t₀ + (↑n : ℝ) * h)
              (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n))

/-- AB4 residual at a given time point `t`, written out explicitly. -/
noncomputable def ab4VecResidual (h : ℝ) (t : ℝ) (y : ℝ → E) : E :=
  y (t + h) - y t -
    h • ((55 / 24 : ℝ) • deriv y t +
         (-(59 : ℝ) / 24) • deriv y (t - h) +
         ((37 : ℝ) / 24) • deriv y (t - 2 * h) +
         (-(9 : ℝ) / 24) • deriv y (t - 3 * h))

end LMM
