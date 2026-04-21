import OpenMath.OrderStars

namespace OpenMath

open Complex Set Real

/-- Scratch cycle-278 combined constructor: if the concrete analytic hypotheses
on `R` separately rule out realized down/up infinity branches, then the live
`ConcreteRationalApproxToExp` seam is satisfied without changing the main file. -/
theorem cycle278_concreteRationalApproxToExp_builder
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_down_support :
      ∀ branch : RealizedDownArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hzero_not_mem_up_support :
      ∀ branch : RealizedUpArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False)
    (hlocal_minus_near_down :
      ∀ θ : ℝ, IsDownArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            ‖R z * exp (-z)‖ < 1)
    (hlocal_plus_near_up :
      ∀ θ : ℝ, IsUpArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            1 < ‖R z * exp (-z)‖)
    (hfar_plus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        1 < ‖R z * exp (-z)‖)
    (hfar_minus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        ‖R z * exp (-z)‖ < 1) :
    ConcreteRationalApproxToExp R data := by
  refine ⟨?_, ?_⟩
  · intro branch
    obtain ⟨aperture, haperture, radius, hradius, hminus⟩ :=
      hlocal_minus_near_down branch.branch.tangentAngle branch.branch.tangentDown
    obtain ⟨zSmall, hzSmall_support, hzSmall_cone⟩ :=
      exists_mem_inter_rayConeNearOrigin_of_branchTracksRayNearOrigin
        branch.branch.toGlobalOrderArrowBranch branch.continuesLocalGerm
        haperture hradius
    have hzSmall_orderWeb :
        zSmall ∈ orderWeb R :=
      mem_orderWeb_of_mem_globalOrderArrowBranch_support
        branch.branch.toGlobalOrderArrowBranch hzSmall_support
    have hzSmall_lt : ‖R zSmall * exp (-zSmall)‖ < 1 :=
      hminus zSmall hzSmall_cone
    obtain ⟨radius, hradius, hplus⟩ := hfar_plus_on_orderWeb
    obtain ⟨zLarge, hzLarge_support, hzLarge_norm⟩ :=
      exists_mem_support_norm_gt_of_escapesEveryClosedBall
        branch.branch.toGlobalOrderArrowBranch branch.escapesEveryClosedBall
        radius hradius.le
    have hzLarge_orderWeb :
        zLarge ∈ orderWeb R :=
      mem_orderWeb_of_mem_globalOrderArrowBranch_support
        branch.branch.toGlobalOrderArrowBranch hzLarge_support
    have hzLarge_gt : 1 < ‖R zLarge * exp (-zLarge)‖ :=
      hplus zLarge hzLarge_orderWeb (le_of_lt hzLarge_norm)
    obtain ⟨z, hz_support, hz_unit⟩ :=
      exists_mem_support_unit_level_of_connected_orderWeb_branch
        branch.branch.toGlobalOrderArrowBranch hcont
        hzSmall_support hzLarge_support hzSmall_lt hzLarge_gt
    have hz_orderWeb :
        z ∈ orderWeb R :=
      mem_orderWeb_of_mem_globalOrderArrowBranch_support
        branch.branch.toGlobalOrderArrowBranch hz_support
    have hz_ne : z ≠ 0 := by
      intro hz_zero
      exact hzero_not_mem_down_support branch (hz_zero ▸ hz_support)
    exact hno_nonzero_unit_points_on_orderWeb z hz_ne hz_orderWeb hz_unit
  · intro branch
    obtain ⟨aperture, haperture, radius, hradius, hplus⟩ :=
      hlocal_plus_near_up branch.branch.tangentAngle branch.branch.tangentUp
    obtain ⟨zLarge, hzLarge_support, hzLarge_cone⟩ :=
      exists_mem_inter_rayConeNearOrigin_of_branchTracksRayNearOrigin
        branch.branch.toGlobalOrderArrowBranch branch.continuesLocalGerm
        haperture hradius
    have hzLarge_orderWeb :
        zLarge ∈ orderWeb R :=
      mem_orderWeb_of_mem_globalOrderArrowBranch_support
        branch.branch.toGlobalOrderArrowBranch hzLarge_support
    have hzLarge_gt : 1 < ‖R zLarge * exp (-zLarge)‖ :=
      hplus zLarge hzLarge_cone
    obtain ⟨radius, hradius, hminus⟩ := hfar_minus_on_orderWeb
    obtain ⟨zSmall, hzSmall_support, hzSmall_norm⟩ :=
      exists_mem_support_norm_gt_of_escapesEveryClosedBall
        branch.branch.toGlobalOrderArrowBranch branch.escapesEveryClosedBall
        radius hradius.le
    have hzSmall_orderWeb :
        zSmall ∈ orderWeb R :=
      mem_orderWeb_of_mem_globalOrderArrowBranch_support
        branch.branch.toGlobalOrderArrowBranch hzSmall_support
    have hzSmall_lt : ‖R zSmall * exp (-zSmall)‖ < 1 :=
      hminus zSmall hzSmall_orderWeb (le_of_lt hzSmall_norm)
    obtain ⟨z, hz_support, hz_unit⟩ :=
      exists_mem_support_unit_level_of_connected_orderWeb_branch
        branch.branch.toGlobalOrderArrowBranch hcont
        hzSmall_support hzLarge_support hzSmall_lt hzLarge_gt
    have hz_orderWeb :
        z ∈ orderWeb R :=
      mem_orderWeb_of_mem_globalOrderArrowBranch_support
        branch.branch.toGlobalOrderArrowBranch hz_support
    have hz_ne : z ≠ 0 := by
      intro hz_zero
      exact hzero_not_mem_up_support branch (hz_zero ▸ hz_support)
    exact hno_nonzero_unit_points_on_orderWeb z hz_ne hz_orderWeb hz_unit

end OpenMath
