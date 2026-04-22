import OpenMath.PadeOrderStars

open Complex

namespace Cycle315Aristotle

theorem padeR_nonpos_sign_of_upArrowDir (n d : ℕ) :
    ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
      padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≤ 0 := by
  sorry

end Cycle315Aristotle
