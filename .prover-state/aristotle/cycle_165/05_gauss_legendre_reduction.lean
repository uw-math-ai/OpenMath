import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Polynomial Real
open scoped Interval

namespace OpenMathAristotleCycle165

/-- If `B(2s)` holds, then the shifted Legendre polynomial of degree `s`
vanishes at every node of the tableau. This is the forward half of the
Gauss-Legendre characterization. -/
theorem gaussLegendreNodes_of_B_double_reduction {s : ℕ}
    (t : ButcherTableau s) (hB : t.SatisfiesB (2 * s)) :
    t.HasGaussLegendreNodes := by
  sorry

/-- If the nodes are roots of the degree-`s` shifted Legendre polynomial and
`B(s)` already holds, then exactness extends to `B(2s)`. This is the backward
half of the Gaussian quadrature characterization. -/
theorem gaussLegendre_B_double_reduction {s : ℕ}
    (t : ButcherTableau s)
    (hGL : t.HasGaussLegendreNodes)
    (hB : t.SatisfiesB s) :
    t.SatisfiesB (2 * s) := by
  sorry

end OpenMathAristotleCycle165
