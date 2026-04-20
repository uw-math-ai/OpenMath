import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

open Polynomial

namespace OpenMathAristotleCycle163

/-- Bridge the recursive real-valued `shiftedLegendreP` to Mathlib's polynomial
`Polynomial.shiftedLegendre`. -/
theorem shiftedLegendreP_eq_aeval_shiftedLegendre (n : ℕ) (x : ℝ) :
    shiftedLegendreP n x =
      aeval x (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n)) := by
  sorry

end OpenMathAristotleCycle163
