import OpenMath.LegendreHelpers

/-- Cycle 179 Aristotle target: prove the coefficient-sum recurrence within the
project heartbeat budget. -/
lemma cycle179_shiftedLegCoeff_sum_recurrence (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * ∑ l ∈ Finset.range (n + 3), shiftedLegCoeff (n + 2) l * x ^ l =
    (2 * (n : ℝ) + 3) * (2 * x - 1) *
      ∑ l ∈ Finset.range (n + 2), shiftedLegCoeff (n + 1) l * x ^ l -
    ((n : ℝ) + 1) * ∑ l ∈ Finset.range (n + 1), shiftedLegCoeff n l * x ^ l := by
  sorry
