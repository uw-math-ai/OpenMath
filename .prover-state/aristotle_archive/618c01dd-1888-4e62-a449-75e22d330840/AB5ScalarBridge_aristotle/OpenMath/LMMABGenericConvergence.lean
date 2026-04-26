import Mathlib

/-! # Generic Adams–Bashforth s-step method (scalar)

Defines the generic AB iteration `abIter`, the truncation residual `abResidual`,
and the AB5-specific coefficient vector `ab5GenericCoeff`.
-/

namespace LMM

open Finset BigOperators

/-! ## AB5 coefficient vector -/

/-- The 5-step Adams–Bashforth coefficients indexed by `Fin 5`. -/
noncomputable def ab5GenericCoeff : Fin 5 → ℝ :=
  ![251 / 720, -1274 / 720, 2616 / 720, -2774 / 720, 1901 / 720]

/-! ## Generic s-step Adams–Bashforth iteration (scalar) -/

/-- Generic s-step Adams–Bashforth iteration.
  For `n < s`, returns `init ⟨n, _⟩`.
  For `n ≥ s`, applies the AB recurrence. -/
noncomputable def abIter (s : ℕ) (coeffs : Fin s → ℝ) (h : ℝ) (f : ℝ → ℝ → ℝ)
    (t₀ : ℝ) (init : Fin s → ℝ) (n : ℕ) : ℝ :=
  if hn : n < s then init ⟨n, hn⟩
  else if _hs : s = 0 then 0
  else
    abIter s coeffs h f t₀ init (n - 1) +
      h * ∑ j : Fin s, coeffs j *
        f (t₀ + ↑((n - s) + j.val) * h)
          (abIter s coeffs h f t₀ init ((n - s) + j.val))
termination_by n
decreasing_by all_goals simp_wf; omega

/-! ## Generic AB truncation residual (scalar) -/

/-- The local truncation residual of the s-step AB method at grid point `t₀ + n·h`. -/
noncomputable def abResidual (s : ℕ) (coeffs : Fin s → ℝ) (h : ℝ) (y : ℝ → ℝ)
    (t₀ : ℝ) (n : ℕ) : ℝ :=
  y (t₀ + (↑n + ↑s) * h) - y (t₀ + (↑n + ↑(s - 1 : ℕ)) * h)
    - h * ∑ j : Fin s, coeffs j * deriv y (t₀ + (↑n + ↑j.val) * h)

end LMM
