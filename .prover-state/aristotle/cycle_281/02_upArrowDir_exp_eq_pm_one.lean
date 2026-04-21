import OpenMath.OrderStars

namespace OpenMath

open Complex Set Real

/-- Up-arrow companion to `cycle281_downArrowDir_exp_eq_pm_one`. -/
theorem cycle281_upArrowDir_exp_eq_pm_one
    (R : ℂ → ℂ) (p : ℕ) (C K δ₀ : ℝ)
    (hC : C ≠ 0) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2))
    (θ : ℝ) (hθ : IsUpArrowDir R θ) :
    exp (↑((((p + 1 : ℕ) : ℝ) * θ)) * I) = 1 ∨
      exp (↑((((p + 1 : ℕ) : ℝ) * θ)) * I) = -1 := by
  sorry

end OpenMath
