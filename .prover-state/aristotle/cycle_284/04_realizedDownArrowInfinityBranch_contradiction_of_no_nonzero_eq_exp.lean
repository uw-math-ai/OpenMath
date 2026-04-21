import OpenMath.OrderStars

open Complex Set Real

theorem cycle284_realizedDownArrowInfinityBranch_contradiction_of_no_nonzero_eq_exp
    (R : ℂ → ℂ)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_down_support :
      ∀ branch : RealizedDownArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_eq_exp :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → R z = exp z → False)
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
