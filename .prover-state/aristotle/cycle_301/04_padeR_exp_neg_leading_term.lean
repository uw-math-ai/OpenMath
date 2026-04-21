import OpenMath.Pade

namespace Cycle301Aristotle04

open Complex

theorem padeR_exp_neg_leading_term
    (n d : ℕ) :
    ∃ g : ℂ → ℂ, ∀ z : ℂ,
      padeR n d z * exp (-z) -
        (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) =
      z ^ (n + d + 2) * g z := by
  sorry

end Cycle301Aristotle04
