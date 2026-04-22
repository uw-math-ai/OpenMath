import OpenMath.PadeOrderStars

open Complex

namespace Cycle315Aristotle

theorem padeR_downArrowSignBridge_of_nonneg_and_zeroCosExclusion
    (n d : ℕ)
    (hnonneg : ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
      0 ≤ padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ))
    (hzero : ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
      padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≠ 0) :
    PadeRDownArrowSignBridge n d := by
  sorry

end Cycle315Aristotle
