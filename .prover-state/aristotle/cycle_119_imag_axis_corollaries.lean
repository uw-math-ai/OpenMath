import OpenMath.OrderStars

open Complex

private theorem one_sub_ne_zero_of_nonpos_re (z : ℂ) (hz : z.re ≤ 0) :
    (1 : ℂ) - z ≠ 0 := by
  sorry

private theorem one_sub_half_mul_ne_zero_of_nonpos_re (z : ℂ) (hz : z.re ≤ 0) :
    (1 : ℂ) - z * (1 / 2 : ℂ) ≠ 0 := by
  sorry

theorem backwardEuler_imagAxis_not_orderStarPlus_aristotle (y : ℝ) :
    (↑y * I) ∉ orderStarPlus backwardEulerR := by
  sorry

theorem backwardEuler_imagAxis_mem_minus_or_bdry_aristotle (y : ℝ) :
    (↑y * I) ∈ orderStarMinus backwardEulerR ∨ (↑y * I) ∈ orderStarBdry backwardEulerR := by
  sorry

theorem trapezoidal_imagAxis_not_orderStarPlus_aristotle (y : ℝ) :
    (↑y * I) ∉ orderStarPlus trapezoidalR := by
  sorry

