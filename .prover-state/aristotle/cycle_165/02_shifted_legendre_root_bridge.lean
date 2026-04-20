import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

open Polynomial

namespace OpenMathAristotleCycle165

/-- Restate the Gauss-Legendre node condition using evaluation of Mathlib's
shifted Legendre polynomial. -/
theorem hasGaussLegendreNodes_iff_eval_map_shiftedLegendre_zero {s : ℕ}
    (t : ButcherTableau s) :
    t.HasGaussLegendreNodes ↔
      ∀ i : Fin s,
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).eval (t.c i) = 0 := by
  sorry

end OpenMathAristotleCycle165
