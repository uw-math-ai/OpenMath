import OpenMath.OrderStars

namespace OpenMath

open Complex Set Real

/-- Cycle-281 generic down-arrow bridge: dispatch an arbitrary down-arrow tangent
direction to the correct concrete cone-control lemma, without changing any live
interfaces. -/
theorem cycle281_local_minus_near_downArrowDir_of_errorConst
    (R : ℂ → ℂ) (p : ℕ) (C K δ₀ : ℝ)
    (hC : C ≠ 0) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2))
    (θ : ℝ) (hθ : IsDownArrowDir R θ) :
    ∃ aperture > 0, ∃ radius > 0,
      ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
        ‖R z * exp (-z)‖ < 1 := by
  sorry

end OpenMath
