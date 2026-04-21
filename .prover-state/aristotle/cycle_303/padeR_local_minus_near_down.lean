import OpenMath.PadeOrderStars

open Complex

namespace OpenMath.Cycle303Aristotle

/-- Candidate cycle-303 local cone-sign feeder for realized down-arrow germs. -/
theorem padeR_local_minus_near_down_candidate
    (n d : ℕ) :
    ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
      ∃ aperture > 0, ∃ radius > 0,
        ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
          ‖padeR n d z * exp (-z)‖ < 1 := by
  sorry

end OpenMath.Cycle303Aristotle
