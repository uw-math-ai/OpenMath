import Mathlib

open Complex Set Real

/-- Up-arrow direction for a stability function. -/
def IsUpArrowDir (R : ℂ → ℂ) (θ : ℝ) : Prop :=
  ∃ ε > 0, ∀ t ∈ Set.Ioo (0 : ℝ) ε,
    1 < ‖R (↑t * exp (↑θ * I)) * exp (-(↑t * exp (↑θ * I)))‖

/-- Trapezoidal rule stability function: R(z) = (1 + z/2)/(1 - z/2). -/
noncomputable def trapezoidalR (z : ℂ) : ℂ := (1 + z / 2) / (1 - z / 2)

/-- Trapezoidal rule: θ = 0 is an up-arrow direction.
    Key fact: (2+t)/(2-t) > exp(t) for small positive t
    (since (2+t)/(2-t) = 1 + t + t²/2 + t³/4 + ... while exp(t) = 1 + t + t²/2 + t³/6 + ...) -/
theorem trapezoidal_isUpArrowDir_zero :
    IsUpArrowDir trapezoidalR 0 := by
  sorry
