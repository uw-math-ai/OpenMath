import Mathlib

/-! # Generic Adams–Bashforth (AB) multi-step method – vector formulation

This file defines the generic `s`-step Adams–Bashforth iteration and residual
parameterised by an arbitrary coefficient vector `c : Fin s → ℝ`.
-/

open Finset BigOperators

namespace LMM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Generic `s`-step Adams–Bashforth iteration (vector form).

For `n < s` the value comes from the initial-value vector `inits`.
For `n ≥ s` the standard AB recurrence is applied:

  `y(n) = y(n−1) + h • ∑ i, c(i) • f(t₀ + (n−s+i)·h, y(n−s+i))`.
-/
noncomputable def abIterVec
    (s : ℕ) (c : Fin s → ℝ) (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (inits : Fin s → E) (n : ℕ) : E :=
  if hn : n < s then inits ⟨n, hn⟩
  else if _hs : s = 0 then 0
  else
    abIterVec s c h f t₀ inits (n - 1)
      + h • ∑ i : Fin s, c i • f (t₀ + ((n - s + (i : ℕ) : ℕ) : ℝ) * h)
            (abIterVec s c h f t₀ inits (n - s + (i : ℕ)))
termination_by n
decreasing_by all_goals omega

/-- Generic `s`-step Adams–Bashforth residual (vector form).

Measures how well a smooth curve `y` satisfies the AB recurrence at base-point
`t₀ + n·h`:

  `τ(n) = y(t₀+(n+s)·h) − y(t₀+(n+s−1)·h) − h • ∑ i, c(i) • y′(t₀+(n+i)·h)`.
-/
noncomputable def abResidualVec
    (s : ℕ) (c : Fin s → ℝ) (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) : E :=
  y (t₀ + (↑n + ↑s) * h) - y (t₀ + (↑n + ↑s - 1) * h)
    - h • ∑ i : Fin s, c i • deriv y (t₀ + (↑n + ↑(i : ℕ)) * h)

end LMM
