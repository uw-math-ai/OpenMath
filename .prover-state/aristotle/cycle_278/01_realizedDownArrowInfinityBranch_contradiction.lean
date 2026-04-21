import OpenMath.OrderStars

namespace OpenMath

open Complex Set Real

/-- If a connected order-web branch has one support point with amplitude below
`1` and another with amplitude above `1`, continuity should force a support
point with amplitude exactly `1`. This is the currently missing connectedness
step in the down-arrow contradiction. -/
theorem cycle278_connected_orderWeb_branch_has_unit_level_point
    (R : ℂ → ℂ) (branch : GlobalOrderArrowBranch R)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    {zSmall zLarge : ℂ}
    (hzSmall : zSmall ∈ branch.support)
    (hzLarge : zLarge ∈ branch.support)
    (hsmall : ‖R zSmall * exp (-zSmall)‖ < 1)
    (hlarge : 1 < ‖R zLarge * exp (-zLarge)‖) :
    ∃ z ∈ branch.support, ‖R z * exp (-z)‖ = 1 := by
  exact exists_mem_support_unit_level_of_connected_orderWeb_branch
    branch hcont hzSmall hzLarge hsmall hlarge

/-- Local cone-control formulation of the missing down-arrow analytic input:
every sufficiently small point in a cone around a down-arrow tangent has
amplitude strictly below `1`. -/
theorem cycle278_realizedDownArrowInfinityBranch_small_orderWeb_point
    (R : ℂ → ℂ)
    (hlocal_minus_near_down :
      ∀ θ : ℝ, IsDownArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            ‖R z * exp (-z)‖ < 1)
    (branch : RealizedDownArrowInfinityBranch R) :
    ∃ z ∈ branch.branch.toGlobalOrderArrowBranch.support,
      z ∈ orderWeb R ∧ ‖R z * exp (-z)‖ < 1 := by
  obtain ⟨aperture, haperture, radius, hradius, hminus⟩ :=
    hlocal_minus_near_down branch.branch.tangentAngle branch.branch.tangentDown
  obtain ⟨z, hz_support, hz_cone⟩ :=
    exists_mem_inter_rayConeNearOrigin_of_branchTracksRayNearOrigin
      branch.branch.toGlobalOrderArrowBranch branch.continuesLocalGerm
      haperture hradius
  refine ⟨z, hz_support, ?_, hminus z hz_cone⟩
  exact mem_orderWeb_of_mem_globalOrderArrowBranch_support
    branch.branch.toGlobalOrderArrowBranch hz_support

/-- Far-field sign control formulation for the down-arrow contradiction:
sufficiently large order-web points have amplitude strictly above `1`. -/
theorem cycle278_realizedDownArrowInfinityBranch_large_orderWeb_point
    (R : ℂ → ℂ)
    (hfar_plus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        1 < ‖R z * exp (-z)‖)
    (branch : RealizedDownArrowInfinityBranch R) :
    ∃ z ∈ branch.branch.toGlobalOrderArrowBranch.support,
      z ∈ orderWeb R ∧ 1 < ‖R z * exp (-z)‖ := by
  obtain ⟨radius, hradius, hplus⟩ := hfar_plus_on_orderWeb
  obtain ⟨z, hz_support, hz_norm⟩ :=
    exists_mem_support_norm_gt_of_escapesEveryClosedBall
      branch.branch.toGlobalOrderArrowBranch branch.escapesEveryClosedBall
      radius hradius.le
  have hz_orderWeb :
      z ∈ orderWeb R :=
    mem_orderWeb_of_mem_globalOrderArrowBranch_support
      branch.branch.toGlobalOrderArrowBranch hz_support
  refine ⟨z, hz_support, hz_orderWeb, ?_⟩
  exact hplus z hz_orderWeb (le_of_lt hz_norm)

/-- Scratch cycle-278 target: once the local cone-control, far-field sign
control, and connectedness crossing lemma are available, a realized escaping
down-arrow branch yields a nonzero unit-level order-web point, contradicting the
concrete analytic hypothesis on `R`. -/
theorem cycle278_realizedDownArrowInfinityBranch_contradiction
    (R : ℂ → ℂ)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_down_support :
      ∀ branch : RealizedDownArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False)
    (hlocal_minus_near_down :
      ∀ θ : ℝ, IsDownArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            ‖R z * exp (-z)‖ < 1)
    (hfar_plus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        1 < ‖R z * exp (-z)‖)
    (branch : RealizedDownArrowInfinityBranch R) :
    False := by
  obtain ⟨zSmall, hzSmall_support, hzSmall_orderWeb, hzSmall_lt⟩ :=
    cycle278_realizedDownArrowInfinityBranch_small_orderWeb_point
      R hlocal_minus_near_down branch
  obtain ⟨zLarge, hzLarge_support, hzLarge_orderWeb, hzLarge_gt⟩ :=
    cycle278_realizedDownArrowInfinityBranch_large_orderWeb_point
      R hfar_plus_on_orderWeb branch
  obtain ⟨z, hz_support, hz_unit⟩ :=
    cycle278_connected_orderWeb_branch_has_unit_level_point
      R branch.branch.toGlobalOrderArrowBranch hcont
      hzSmall_support hzLarge_support hzSmall_lt hzLarge_gt
  have hz_orderWeb :
      z ∈ orderWeb R :=
    mem_orderWeb_of_mem_globalOrderArrowBranch_support
      branch.branch.toGlobalOrderArrowBranch hz_support
  have hz_ne : z ≠ 0 := by
    intro hz_zero
    exact hzero_not_mem_down_support branch (hz_zero ▸ hz_support)
  exact hno_nonzero_unit_points_on_orderWeb z hz_ne hz_orderWeb hz_unit

theorem cycle278_noRealizedDownArrowInfinityBranch_of_analyticHypotheses
    (R : ℂ → ℂ)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_down_support :
      ∀ branch : RealizedDownArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False)
    (hlocal_minus_near_down :
      ∀ θ : ℝ, IsDownArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            ‖R z * exp (-z)‖ < 1)
    (hfar_plus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        1 < ‖R z * exp (-z)‖) :
    NoRealizedDownArrowInfinityBranch R := by
  intro branch
  exact cycle278_realizedDownArrowInfinityBranch_contradiction
    R hcont hzero_not_mem_down_support hno_nonzero_unit_points_on_orderWeb
    hlocal_minus_near_down hfar_plus_on_orderWeb branch

end OpenMath
