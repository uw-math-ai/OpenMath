import OpenMath.Legendre

namespace ButcherTableau

variable {s : ℕ} (t : ButcherTableau s)

/-- Cycle 175 Aristotle target for the forward half of Corollary 342D. If this
fails, any returned proof should make explicit which extra hypotheses are
actually needed. -/
theorem cycle175_gaussLegendreNodes_of_B_double
    (hB : t.SatisfiesB (2 * s)) :
    t.HasGaussLegendreNodes := by
  sorry

end ButcherTableau
