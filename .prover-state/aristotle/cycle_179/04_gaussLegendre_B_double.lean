import OpenMath.Legendre
import OpenMath.LegendreHelpers

namespace ButcherTableau

/-- Cycle 179 Aristotle target: close the remaining backward Gauss-Legendre
quadrature sorry in the current repository. -/
theorem cycle179_gaussLegendre_B_double {s : ℕ} (t : ButcherTableau s)
    (hGL : t.HasGaussLegendreNodes)
    (hB : t.SatisfiesB s) :
    t.SatisfiesB (2 * s) := by
  sorry

end ButcherTableau
