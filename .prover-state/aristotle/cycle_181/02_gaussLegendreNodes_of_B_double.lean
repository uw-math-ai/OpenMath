import OpenMath.Legendre
import OpenMath.LegendreHelpers
import OpenMath.ShiftedLegendreDivision

namespace ButcherTableau

/-- Cycle 181 Aristotle target: close the converse Gauss-Legendre node
characterization in the current repository. -/
theorem cycle181_gaussLegendreNodes_of_B_double {s : ℕ} (t : ButcherTableau s)
    (hB : t.SatisfiesB (2 * s)) :
    t.HasGaussLegendreNodes := by
  sorry

end ButcherTableau
