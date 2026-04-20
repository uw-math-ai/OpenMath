import OpenMath.Legendre
import OpenMath.LegendreHelpers
import OpenMath.ShiftedLegendreDivision

namespace ButcherTableau

/-- Cycle 181 Aristotle target: close the remaining Gaussian quadrature exactness
sorry in the current `OpenMath.Legendre`. -/
theorem cycle181_gaussLegendre_B_double {s : ℕ} (t : ButcherTableau s)
    (hGL : t.HasGaussLegendreNodes)
    (hB : t.SatisfiesB s) :
    t.SatisfiesB (2 * s) := by
  sorry

end ButcherTableau
