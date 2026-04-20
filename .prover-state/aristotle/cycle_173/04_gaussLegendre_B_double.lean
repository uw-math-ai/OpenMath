import OpenMath.Legendre
import OpenMath.ShiftedLegendreDivision
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

namespace OpenMath
namespace ButcherTableau

variable {s : ℕ} (t : ButcherTableau s)

/-- Aristotle target for the remaining `gaussLegendre_B_double` blocker. -/
theorem cycle173_gaussLegendre_B_double
    (hGL : t.HasGaussLegendreNodes)
    (hB : t.SatisfiesB s)
    (hbridge : ∀ n x,
      shiftedLegendreP n x =
        (-1 : ℝ) ^ n *
          (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n)).eval x) :
    t.SatisfiesB (2 * s) := by
  sorry

end ButcherTableau
end OpenMath
