import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

open Polynomial

namespace ButcherTableau

theorem cycle167_hasGaussLegendreNodes_iff_eval_map_shiftedLegendre_zero {s : ℕ}
    (t : ButcherTableau s)
    (hbridge :
      ∀ x : ℝ,
        shiftedLegendreP s x =
          (-1 : ℝ) ^ s *
            (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).eval x) :
    t.HasGaussLegendreNodes ↔
      ∀ i : Fin s,
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).eval (t.c i) = 0 := by
  sorry

end ButcherTableau
