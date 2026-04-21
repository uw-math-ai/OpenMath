import OpenMath.OrderStars

open Complex Set Real

/-- Cycle 279 Aristotle target: the odd-angle, negative-error-constant cone
control needed for the down-arrow side of the contradiction. -/
theorem cycle279_local_minus_near_odd_angle_of_neg_errorConst
    (R : ℂ → ℂ) (p k : ℕ) (C K δ₀ : ℝ)
    (hC : C < 0) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2)) :
    ∃ aperture > 0, ∃ radius > 0,
      ∀ z : ℂ, z ∈ rayConeNearOrigin ((2 * ↑k + 1) * π / (↑p + 1)) aperture radius →
        ‖R z * exp (-z)‖ < 1 := by
  sorry
