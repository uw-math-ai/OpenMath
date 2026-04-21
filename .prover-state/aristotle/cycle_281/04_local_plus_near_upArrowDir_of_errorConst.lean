import OpenMath.OrderStars

namespace OpenMath

open Complex Set Real

/-- Up-arrow companion to the cycle-281 generic down-arrow bridge. -/
theorem cycle281_local_plus_near_upArrowDir_of_errorConst
    (R : ℂ → ℂ) (p : ℕ) (C K δ₀ : ℝ)
    (hC : C ≠ 0) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2))
    (θ : ℝ) (hθ : IsUpArrowDir R θ) :
    ∃ aperture > 0, ∃ radius > 0,
      ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
        1 < ‖R z * exp (-z)‖ := by
  sorry

end OpenMath
