import OpenMath.OrderStars

namespace OpenMath

open Complex Set Real

/-- Cycle-281 theorem-local contradiction shape for a realized escaping
down-arrow branch. This should reuse the live cycle-278 helper layer unchanged. -/
theorem cycle281_realizedDownArrowInfinityBranch_contradiction
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
  sorry

end OpenMath
