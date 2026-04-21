import OpenMath.OrderStars

namespace OpenMath

open Complex Set Real

/-- Up-arrow analogue of the connectedness crossing lemma: if a connected
order-web branch sees amplitudes both above and below `1`, continuity should
force a unit-level support point. -/
theorem cycle278_connected_orderWeb_branch_has_unit_level_point
    (R : ℂ → ℂ) (branch : GlobalOrderArrowBranch R)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    {zLarge zSmall : ℂ}
    (hzLarge : zLarge ∈ branch.support)
    (hzSmall : zSmall ∈ branch.support)
    (hlarge : 1 < ‖R zLarge * exp (-zLarge)‖)
    (hsmall : ‖R zSmall * exp (-zSmall)‖ < 1) :
    ∃ z ∈ branch.support, ‖R z * exp (-z)‖ = 1 := by
  exact exists_mem_support_unit_level_of_connected_orderWeb_branch
    branch hcont hzSmall hzLarge hsmall hlarge

/-- Local cone-control formulation of the missing up-arrow analytic input:
every sufficiently small point in a cone around an up-arrow tangent has
amplitude strictly above `1`. -/
theorem cycle278_realizedUpArrowInfinityBranch_large_orderWeb_point_near_origin
    (R : ℂ → ℂ)
    (hlocal_plus_near_up :
      ∀ θ : ℝ, IsUpArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            1 < ‖R z * exp (-z)‖)
    (branch : RealizedUpArrowInfinityBranch R) :
    ∃ z ∈ branch.branch.toGlobalOrderArrowBranch.support,
      z ∈ orderWeb R ∧ 1 < ‖R z * exp (-z)‖ := by
  obtain ⟨aperture, haperture, radius, hradius, hplus⟩ :=
    hlocal_plus_near_up branch.branch.tangentAngle branch.branch.tangentUp
  obtain ⟨z, hz_support, hz_cone⟩ :=
    exists_mem_inter_rayConeNearOrigin_of_branchTracksRayNearOrigin
      branch.branch.toGlobalOrderArrowBranch branch.continuesLocalGerm
      haperture hradius
  refine ⟨z, hz_support, ?_, hplus z hz_cone⟩
  exact mem_orderWeb_of_mem_globalOrderArrowBranch_support
    branch.branch.toGlobalOrderArrowBranch hz_support

/-- Far-field sign control formulation for the up-arrow contradiction:
sufficiently large order-web points have amplitude strictly below `1`. -/
theorem cycle278_realizedUpArrowInfinityBranch_small_orderWeb_point_far_out
    (R : ℂ → ℂ)
    (hfar_minus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        ‖R z * exp (-z)‖ < 1)
    (branch : RealizedUpArrowInfinityBranch R) :
    ∃ z ∈ branch.branch.toGlobalOrderArrowBranch.support,
      z ∈ orderWeb R ∧ ‖R z * exp (-z)‖ < 1 := by
  obtain ⟨radius, hradius, hminus⟩ := hfar_minus_on_orderWeb
  obtain ⟨z, hz_support, hz_norm⟩ :=
    exists_mem_support_norm_gt_of_escapesEveryClosedBall
      branch.branch.toGlobalOrderArrowBranch branch.escapesEveryClosedBall
      radius hradius.le
  have hz_orderWeb :
      z ∈ orderWeb R :=
    mem_orderWeb_of_mem_globalOrderArrowBranch_support
      branch.branch.toGlobalOrderArrowBranch hz_support
  refine ⟨z, hz_support, hz_orderWeb, ?_⟩
  exact hminus z hz_orderWeb (le_of_lt hz_norm)

/-- Scratch cycle-278 target: the up-arrow contradiction uses the same
connectedness crossing step as the down-arrow case, but with the local and
far-field inequalities reversed. -/
theorem cycle278_realizedUpArrowInfinityBranch_contradiction
    (R : ℂ → ℂ)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_up_support :
      ∀ branch : RealizedUpArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False)
    (hlocal_plus_near_up :
      ∀ θ : ℝ, IsUpArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            1 < ‖R z * exp (-z)‖)
    (hfar_minus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        ‖R z * exp (-z)‖ < 1)
    (branch : RealizedUpArrowInfinityBranch R) :
    False := by
  obtain ⟨zLarge, hzLarge_support, hzLarge_orderWeb, hzLarge_gt⟩ :=
    cycle278_realizedUpArrowInfinityBranch_large_orderWeb_point_near_origin
      R hlocal_plus_near_up branch
  obtain ⟨zSmall, hzSmall_support, hzSmall_orderWeb, hzSmall_lt⟩ :=
    cycle278_realizedUpArrowInfinityBranch_small_orderWeb_point_far_out
      R hfar_minus_on_orderWeb branch
  obtain ⟨z, hz_support, hz_unit⟩ :=
    cycle278_connected_orderWeb_branch_has_unit_level_point
      R branch.branch.toGlobalOrderArrowBranch hcont
      hzLarge_support hzSmall_support hzLarge_gt hzSmall_lt
  have hz_orderWeb :
      z ∈ orderWeb R :=
    mem_orderWeb_of_mem_globalOrderArrowBranch_support
      branch.branch.toGlobalOrderArrowBranch hz_support
  have hz_ne : z ≠ 0 := by
    intro hz_zero
    exact hzero_not_mem_up_support branch (hz_zero ▸ hz_support)
  exact hno_nonzero_unit_points_on_orderWeb z hz_ne hz_orderWeb hz_unit

theorem cycle278_noRealizedUpArrowInfinityBranch_of_analyticHypotheses
    (R : ℂ → ℂ)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_up_support :
      ∀ branch : RealizedUpArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False)
    (hlocal_plus_near_up :
      ∀ θ : ℝ, IsUpArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            1 < ‖R z * exp (-z)‖)
    (hfar_minus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        ‖R z * exp (-z)‖ < 1) :
    NoRealizedUpArrowInfinityBranch R := by
  intro branch
  exact cycle278_realizedUpArrowInfinityBranch_contradiction
    R hcont hzero_not_mem_up_support hno_nonzero_unit_points_on_orderWeb
    hlocal_plus_near_up hfar_minus_on_orderWeb branch

end OpenMath
