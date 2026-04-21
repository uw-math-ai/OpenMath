import OpenMath.PadeOrderStars

open Complex

theorem padeR_exists_globalDownArrowBranch_with_tracking_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    ∃ branch : GlobalDownArrowBranch (padeR n d),
      BranchTracksRayNearOrigin branch.toGlobalOrderArrowBranch branch.tangentAngle := by
  have hdir : ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ := by
    sorry
  rcases
      padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos_of_exists_downArrowDir
        n d data hpos hdir with
    ⟨branch⟩
  refine ⟨branch, ?_⟩
  sorry
