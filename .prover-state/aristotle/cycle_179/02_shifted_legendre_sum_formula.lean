import OpenMath.Legendre
import OpenMath.LegendreHelpers

/-- Cycle 179 Aristotle target: prove the explicit coefficient formula for the
current recursive `shiftedLegendreP`. -/
theorem cycle179_shiftedLegendre_sum_formula (s : ℕ) (x : ℝ) :
    shiftedLegendreP s x =
      ∑ l ∈ Finset.range (s + 1), shiftedLegCoeff s l * x ^ l := by
  sorry
