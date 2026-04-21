import OpenMath.Pade

namespace Cycle301Aristotle01

open Complex

theorem pade_expTaylor_defect_leading_term
    (n d : ℕ) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      padeP n d z - padeQ n d z * expTaylor (n + d) z -
        padeExpTaylorDefectCoeff n d * z ^ (n + d + 1) =
      z ^ (n + d + 2) * h z := by
  sorry

end Cycle301Aristotle01
