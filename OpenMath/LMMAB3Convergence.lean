import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp

/-! ## Adams–Bashforth 3-step Convergence Chain (Iserles §1.2)

Order-3 explicit 3-step LMM convergence scaffold. Mirrors the AB2 chain
in `OpenMath.LMMAB2Convergence`. Cycle 416 lands the iteration definition
and the textbook LTE rewrite; remaining declarations (Lipschitz one-step
recurrence, local residual bound, headline global error bound) follow in
later cycles. -/

namespace LMM

/-- AB3 iteration with three starting samples `y₀, y₁, y₂`:
`y_{n+3} = y_{n+2} + h · (23/12 · f(t_{n+2}, y_{n+2})
  − 16/12 · f(t_{n+1}, y_{n+1}) + 5/12 · f(t_n, y_n))`. -/
noncomputable def ab3Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | n + 3 =>
      ab3Iter h f t₀ y₀ y₁ y₂ (n + 2)
        + h * (23 / 12 * f (t₀ + ((n : ℝ) + 2) * h)
                (ab3Iter h f t₀ y₀ y₁ y₂ (n + 2))
              - 16 / 12 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab3Iter h f t₀ y₀ y₁ y₂ (n + 1))
              + 5 / 12 * f (t₀ + (n : ℝ) * h)
                (ab3Iter h f t₀ y₀ y₁ y₂ n))

@[simp] lemma ab3Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) :
    ab3Iter h f t₀ y₀ y₁ y₂ 0 = y₀ := rfl

@[simp] lemma ab3Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) :
    ab3Iter h f t₀ y₀ y₁ y₂ 1 = y₁ := rfl

@[simp] lemma ab3Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) :
    ab3Iter h f t₀ y₀ y₁ y₂ 2 = y₂ := rfl

lemma ab3Iter_succ_succ_succ
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) (n : ℕ) :
    ab3Iter h f t₀ y₀ y₁ y₂ (n + 3)
      = ab3Iter h f t₀ y₀ y₁ y₂ (n + 2)
          + h * (23 / 12 * f (t₀ + ((n : ℝ) + 2) * h)
                  (ab3Iter h f t₀ y₀ y₁ y₂ (n + 2))
                - 16 / 12 * f (t₀ + ((n : ℝ) + 1) * h)
                    (ab3Iter h f t₀ y₀ y₁ y₂ (n + 1))
                + 5 / 12 * f (t₀ + (n : ℝ) * h)
                    (ab3Iter h f t₀ y₀ y₁ y₂ n)) := rfl

/-- AB3 local truncation operator reduces to the textbook 3-step residual
`y(t + 3h) − y(t + 2h) − h · (23/12 · y'(t + 2h) − 16/12 · y'(t + h)
  + 5/12 · y'(t))`. -/
theorem ab3_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth3.localTruncationError h t y
      = y (t + 3 * h) - y (t + 2 * h)
          - h * (23 / 12 * deriv y (t + 2 * h)
                  - 16 / 12 * deriv y (t + h)
                  + 5 / 12 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth3, Fin.sum_univ_four, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

end LMM
