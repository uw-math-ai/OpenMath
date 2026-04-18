import OpenMath.Pade

open Complex

/-- Cycle 107 Aristotle job: explicit right-edge self-adjointness defect for `m = 1`. -/
theorem cycle107_padeV_one_right (l : ℕ) (hl : 0 < l) (z : ℂ) :
    padeV l 1 z =
      (expTaylor l z - z / (l + 1 : ℂ) * expTaylor (l - 1) z) *
        (expTaylor l (-z) + z / (l + 1 : ℂ) * expTaylor (l - 1) (-z)) -
      (1 - z / (l + 1 : ℂ)) * (1 + z / (l + 1 : ℂ)) := by
  sorry
