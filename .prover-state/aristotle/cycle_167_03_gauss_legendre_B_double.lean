import OpenMath.Legendre

open Finset Real
open scoped BigOperators

namespace ButcherTableau

theorem cycle167_gaussLegendre_B_double {s : ℕ} (t : ButcherTableau s)
    (hGL : t.HasGaussLegendreNodes)
    (hB : t.SatisfiesB s) :
    t.SatisfiesB (2 * s) := by
  sorry

end ButcherTableau
