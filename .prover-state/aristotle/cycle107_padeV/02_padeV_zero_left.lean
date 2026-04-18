import OpenMath.Pade

open Complex

/-- Cycle 107 Aristotle job: explicit left-edge self-adjointness defect. -/
theorem cycle107_padeV_zero_left (m : ℕ) (z : ℂ) :
    padeV 0 m z = 1 - padeQ 0 m z * padeQ 0 m (-z) := by
  sorry
