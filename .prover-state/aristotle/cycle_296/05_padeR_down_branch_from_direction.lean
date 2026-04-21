import OpenMath.PadeOrderStars

open Complex

noncomputable section

theorem padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    Nonempty (GlobalDownArrowBranch (padeR n d)) := by
  have hdir : ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ := by
    sorry
  exact
    padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos_of_exists_downArrowDir
      n d data hpos hdir
