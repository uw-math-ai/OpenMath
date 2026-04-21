import OpenMath.OrderStars

namespace OpenMath

open Complex Set Real

/-- The inverse-classification seed needed for the cycle-281 down-arrow bridge:
if `θ` is a down-arrow direction for the `1 - C z^(p+1) + O(|z|^(p+2))`
asymptotic model, then the leading oscillatory factor must be `±1`. -/
theorem cycle281_downArrowDir_exp_eq_pm_one
    (R : ℂ → ℂ) (p : ℕ) (C K δ₀ : ℝ)
    (hC : C ≠ 0) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2))
    (θ : ℝ) (hθ : IsDownArrowDir R θ) :
    exp (↑((((p + 1 : ℕ) : ℝ) * θ)) * I) = 1 ∨
      exp (↑((((p + 1 : ℕ) : ℝ) * θ)) * I) = -1 := by
  sorry

end OpenMath
