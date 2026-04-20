import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Polynomial Real
open scoped Interval

namespace OpenMathAristotleCycle165

/-- The mapped shifted Legendre polynomial of degree `s` is orthogonal on
`[0,1]` to every polynomial of degree `< s`. -/
theorem shiftedLegendre_orthogonal_on_unit_interval {s : ℕ}
    {q : ℝ[X]} (hq : q.natDegree < s) :
    ∫ x in (0 : ℝ)..1,
      (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).eval x * q.eval x = 0 := by
  sorry

end OpenMathAristotleCycle165
