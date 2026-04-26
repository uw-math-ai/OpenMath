import Mathlib

/-! Generic Adams–Bashforth (AB) multi-step definitions. -/

namespace LMM

open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lipschitz-like constant for the generic AB method:
    `abLip k c L = (∑ i, |c i|) * L`. -/
noncomputable def abLip (k : ℕ) (c : Fin k → ℝ) (L : ℝ) : ℝ :=
  (∑ i : Fin k, |c i|) * L

/-- Generic AB k-step iteration. For `n < k` returns the seed value
    `inits ⟨n, _⟩`; for `n ≥ k` applies the AB recurrence. -/
noncomputable def abIterVec (k : ℕ) (c : Fin k → ℝ) (h : ℝ)
    (f : ℝ → E → E) (t₀ : ℝ) (inits : Fin k → E) (n : ℕ) : E :=
  if _hk : k = 0 then 0
  else if hn : n < k then inits ⟨n, hn⟩
  else
    abIterVec k c h f t₀ inits (n - 1) +
      h • ∑ j : Fin k, c j • f (t₀ + ((n - k + ↑j : ℕ) : ℝ) * h)
        (abIterVec k c h f t₀ inits (n - k + ↑j))
termination_by n
decreasing_by all_goals omega

/-- Generic AB k-step residual.  Measures how well an exact solution
    `y` satisfies the AB recurrence at step `n`. -/
noncomputable def abResidualVec (k : ℕ) (c : Fin k → ℝ) (h : ℝ)
    (y : ℝ → E) (t₀ : ℝ) (n : ℕ) : E :=
  y (t₀ + (↑n + 1) * h) - y (t₀ + ↑n * h) -
    h • ∑ j : Fin k, c j • deriv y (t₀ + (↑n - (↑k - 1) + ↑j) * h)

end LMM
