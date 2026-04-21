import OpenMath.Pade

namespace Cycle301Aristotle02

open Complex

theorem expTaylor_exp_neg_leading_term
    (m : ℕ) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      expTaylor m z * exp (-z) -
        (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1)) =
      z ^ (m + 2) * h z := by
  sorry

end Cycle301Aristotle02
