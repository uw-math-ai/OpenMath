import OpenMath.PadeOrderStars

open Complex

theorem padeR_exists_globalDownArrowBranch_with_tracking_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    ∃ branch : GlobalDownArrowBranch (padeR n d),
      BranchTracksRayNearOrigin branch.toGlobalOrderArrowBranch branch.tangentAngle := by
  sorry
