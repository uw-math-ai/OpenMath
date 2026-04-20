import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.FieldDivision

open Polynomial

namespace OpenMathAristotleCycle163

/-- The mapped shifted Legendre polynomial over `ℝ` has degree `s` and hence at most `s` roots. -/
theorem shiftedLegendre_map_card_roots_le (s : ℕ) :
    ((Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).roots.card : ℕ) ≤ s := by
  sorry

/-- The leading coefficient of the mapped shifted Legendre polynomial is nonzero. -/
theorem shiftedLegendre_map_coeff_self_ne_zero (s : ℕ) :
    (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff s ≠ 0 := by
  sorry

end OpenMathAristotleCycle163
