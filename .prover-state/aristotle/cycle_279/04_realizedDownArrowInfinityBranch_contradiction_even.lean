import OpenMath.OrderStars

open Complex Set Real

/-- Cycle 279 Aristotle target: keep the live contradiction shape, but specialize
the local tangent to one concrete even 355B angle and reuse the live helper
layer. This should not redesign `OrderStars`; it should only close the
theorem-local contradiction. -/
theorem cycle279_realizedDownArrowInfinityBranch_contradiction_even
    (R : ℂ → ℂ) (p k : ℕ) (C K δ₀ : ℝ)
    (hC : 0 < C) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2))
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_down_support :
      ∀ branch : RealizedDownArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False)
    (hfar_plus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        1 < ‖R z * exp (-z)‖)
    (branch : RealizedDownArrowInfinityBranch R)
    (htangent :
      branch.branch.tangentAngle = 2 * ↑k * π / (↑p + 1)) :
    False := by
  sorry
