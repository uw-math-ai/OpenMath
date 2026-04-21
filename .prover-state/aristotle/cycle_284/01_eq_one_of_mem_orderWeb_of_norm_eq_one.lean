import OpenMath.OrderStars

open Complex Set Real

theorem cycle284_eq_one_of_mem_orderWeb_of_norm_eq_one
    {R : ℂ → ℂ} {z : ℂ}
    (hzWeb : z ∈ orderWeb R)
    (hnorm : ‖R z * exp (-z)‖ = 1) :
    R z * exp (-z) = 1 := by
  sorry
