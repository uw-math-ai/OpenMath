import OpenMath.OrderStars

open Complex Set Real

/-- Cycle 279 Aristotle target: mirror the new live cone-control lemma for the
even-angle, negative-error-constant case. This is the up-arrow analogue of
`local_minus_near_even_angle_of_pos_errorConst`. -/
theorem cycle279_local_plus_near_even_angle_of_neg_errorConst
    (R : ℂ → ℂ) (p k : ℕ) (C K δ₀ : ℝ)
    (hC : C < 0) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2)) :
    ∃ aperture > 0, ∃ radius > 0,
      ∀ z : ℂ, z ∈ rayConeNearOrigin (2 * ↑k * π / (↑p + 1)) aperture radius →
        1 < ‖R z * exp (-z)‖ := by
  sorry
