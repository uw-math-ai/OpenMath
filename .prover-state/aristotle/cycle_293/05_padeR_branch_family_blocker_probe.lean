import OpenMath.PadeOrderStars

open Complex

theorem padeR_nonempty_realizedDownArrowInfinityBranch_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    Nonempty (RealizedDownArrowInfinityBranch (padeR n d)) := by
  sorry

theorem padeR_nonempty_realizedUpArrowInfinityBranch_of_upArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.upArrowsAtInfinity) :
    Nonempty (RealizedUpArrowInfinityBranch (padeR n d)) := by
  sorry
