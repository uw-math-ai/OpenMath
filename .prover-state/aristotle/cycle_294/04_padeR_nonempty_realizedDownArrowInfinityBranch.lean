import OpenMath.PadeOrderStars

open Complex

theorem padeR_nonempty_realizedDownArrowInfinityBranch_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    Nonempty (RealizedDownArrowInfinityBranch (padeR n d)) := by
  sorry
