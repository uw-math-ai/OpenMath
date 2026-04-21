import OpenMath.OrderStars

open Complex Set Real

/-- Cycle 279 Aristotle target: up-arrow analogue of the concrete even-angle
contradiction shape, again without changing the live seam. -/
theorem cycle279_realizedUpArrowInfinityBranch_contradiction_even
    (R : ℂ → ℂ) (p k : ℕ) (C K δ₀ : ℝ)
    (hC : C < 0) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2))
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_up_support :
      ∀ branch : RealizedUpArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False)
    (hfar_minus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        ‖R z * exp (-z)‖ < 1)
    (branch : RealizedUpArrowInfinityBranch R)
    (htangent :
      branch.branch.tangentAngle = 2 * ↑k * π / (↑p + 1)) :
    False := by
  sorry
