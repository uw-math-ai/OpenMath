import OpenMath.PadeOrderStars

open Complex

namespace Cycle315Aristotle

theorem padeR_upArrowSignBridge_of_nonpos_and_zeroCosExclusion
    (n d : ℕ)
    (hnonpos : ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
      padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≤ 0)
    (hzero : ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
      padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≠ 0) :
    PadeRUpArrowSignBridge n d := by
  sorry

end Cycle315Aristotle
