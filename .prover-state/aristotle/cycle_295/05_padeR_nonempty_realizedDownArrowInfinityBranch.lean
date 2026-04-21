import OpenMath.PadeOrderStars

open Complex

theorem padeR_nonempty_realizedDownArrowInfinityBranch_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    Nonempty (RealizedDownArrowInfinityBranch (padeR n d)) := by
  have hdir : ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ := by
    sorry
  rcases
      padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos_of_exists_downArrowDir
        n d data hpos hdir with
    ⟨branch⟩
  refine ⟨{ branch := branch, continuesLocalGerm := ?_, escapesEveryClosedBall := ?_ }⟩
  · sorry
  · sorry
