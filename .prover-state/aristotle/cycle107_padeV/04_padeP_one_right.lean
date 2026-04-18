import OpenMath.Pade

open Complex

/-- Cycle 107 Aristotle job: explicit right-edge numerator recurrence for `m = 1`. -/
theorem cycle107_padeP_one_right (l : ℕ) (hl : 0 < l) (z : ℂ) :
    padeP l 1 z = expTaylor l z - z / (l + 1 : ℂ) * expTaylor (l - 1) z := by
  sorry
