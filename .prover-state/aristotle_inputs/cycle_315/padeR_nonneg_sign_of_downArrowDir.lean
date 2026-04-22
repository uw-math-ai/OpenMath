import OpenMath.PadeOrderStars

open Complex

namespace Cycle315Aristotle

theorem padeR_nonneg_sign_of_downArrowDir (n d : ℕ) :
    ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
      0 ≤ padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) := by
  sorry

end Cycle315Aristotle
