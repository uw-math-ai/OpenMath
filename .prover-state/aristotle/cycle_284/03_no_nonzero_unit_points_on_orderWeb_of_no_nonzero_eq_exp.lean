import OpenMath.OrderStars

open Complex Set Real

theorem cycle284_no_nonzero_unit_points_on_orderWeb_of_no_nonzero_eq_exp
    {R : ℂ → ℂ}
    (hno_nonzero_eq_exp :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → R z = exp z → False) :
    ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False := by
  sorry
