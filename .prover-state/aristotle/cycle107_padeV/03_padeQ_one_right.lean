import OpenMath.Pade

open Complex

/-- Cycle 107 Aristotle job: explicit right-edge denominator for `m = 1`. -/
theorem cycle107_padeQ_one_right (l : ℕ) (z : ℂ) :
    padeQ l 1 z = 1 - z / (l + 1 : ℂ) := by
  sorry
