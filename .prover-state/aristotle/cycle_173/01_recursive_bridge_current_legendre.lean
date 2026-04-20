import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

namespace OpenMath

/-- Bridge the current recursive `shiftedLegendreP` definition to Mathlib's
`Polynomial.shiftedLegendre`. -/
theorem cycle173_recursive_bridge (n : ℕ) (x : ℝ) :
    shiftedLegendreP n x =
      (-1 : ℝ) ^ n *
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n)).eval x := by
  sorry

end OpenMath
