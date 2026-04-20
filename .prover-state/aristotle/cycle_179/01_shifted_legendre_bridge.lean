import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-- Cycle 179 Aristotle target: prove the bridge from the recursive
`shiftedLegendreP` to Mathlib's mapped `Polynomial.shiftedLegendre`. -/
theorem cycle179_shiftedLegendre_bridge (n : ℕ) (x : ℝ) :
    shiftedLegendreP n x =
      (-1 : ℝ) ^ n *
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n)).eval x := by
  sorry
