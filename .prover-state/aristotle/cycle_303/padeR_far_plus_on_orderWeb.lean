import OpenMath.PadeOrderStars

open Complex

namespace OpenMath.Cycle303Aristotle

/-- Candidate cycle-303 far-field sign feeder for the down-arrow contradiction. -/
theorem padeR_far_plus_on_orderWeb_candidate
    (n d : ℕ) :
    ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
      1 < ‖padeR n d z * exp (-z)‖ := by
  sorry

end OpenMath.Cycle303Aristotle
