import OpenMath.PadeOrderStars

open Complex

namespace OpenMath.Cycle303Aristotle

/-- Candidate cycle-303 local cone-sign feeder for realized up-arrow germs. -/
theorem padeR_local_plus_near_up_candidate
    (n d : ℕ) :
    ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
      ∃ aperture > 0, ∃ radius > 0,
        ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
          1 < ‖padeR n d z * exp (-z)‖ := by
  sorry

end OpenMath.Cycle303Aristotle
