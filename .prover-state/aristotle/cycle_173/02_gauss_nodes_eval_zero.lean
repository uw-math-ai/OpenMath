import OpenMath.Legendre
import OpenMath.ShiftedLegendreDivision
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

namespace OpenMath
namespace ButcherTableau

variable {s : ℕ} (t : ButcherTableau s)

/-- Convert the Gauss-Legendre node hypothesis into vanishing of Mathlib's
shifted Legendre polynomial at each node. -/
theorem cycle173_gauss_nodes_eval_zero
    (hGL : t.HasGaussLegendreNodes)
    (hbridge : ∀ x : ℝ,
      shiftedLegendreP s x =
        (-1 : ℝ) ^ s *
          (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).eval x) :
    ∀ i : Fin s,
      (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).eval (t.c i) = 0 := by
  sorry

end ButcherTableau
end OpenMath
