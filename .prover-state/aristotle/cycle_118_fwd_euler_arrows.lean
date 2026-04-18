import Mathlib

open Complex Set Real

/-- Forward Euler stability function: `R(z) = 1 + z`. -/
noncomputable def forwardEulerR (z : ℂ) : ℂ := 1 + z

/-- Down-arrow direction for a stability function. -/
def IsDownArrowDir (R : ℂ → ℂ) (θ : ℝ) : Prop :=
  ∃ ε > 0, ∀ t ∈ Set.Ioo (0 : ℝ) ε,
    ‖R (↑t * exp (↑θ * I)) * exp (-(↑t * exp (↑θ * I)))‖ < 1

/-- Forward Euler: θ = 0 is a down-arrow direction.
    Key fact: (1+t)·exp(-t) < 1 for t > 0, since exp(t) > 1+t. -/
theorem forwardEuler_isDownArrowDir_zero :
    IsDownArrowDir forwardEulerR 0 := by
  sorry

/-- Forward Euler: θ = π is a down-arrow direction.
    Key fact: (1-t)·exp(t) < 1 for 0 < t < 1. -/
theorem forwardEuler_isDownArrowDir_pi :
    IsDownArrowDir forwardEulerR π := by
  sorry
