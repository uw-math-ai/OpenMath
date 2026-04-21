import OpenMath.Pade
import OpenMath.OrderStars

open Complex Set Real

theorem cycle286_padeR_zero_not_mem_realizedUpArrowInfinityBranch_support
    (n d : ℕ) :
    ∀ branch : RealizedUpArrowInfinityBranch (padeR n d),
      (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support := by
  sorry
