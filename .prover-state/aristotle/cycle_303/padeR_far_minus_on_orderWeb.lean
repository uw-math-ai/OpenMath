import OpenMath.PadeOrderStars

open Complex

namespace OpenMath.Cycle303Aristotle

/-- Candidate cycle-303 far-field sign feeder for the up-arrow contradiction. -/
theorem padeR_far_minus_on_orderWeb_candidate
    (n d : ℕ) :
    ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
      ‖padeR n d z * exp (-z)‖ < 1 := by
  sorry

end OpenMath.Cycle303Aristotle
