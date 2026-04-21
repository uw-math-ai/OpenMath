import OpenMath.PadeOrderStars

open Complex

theorem padeR_exists_downArrowDir_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ := by
  sorry
