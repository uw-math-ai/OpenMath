import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.FieldDivision

open Polynomial

namespace OpenMathAristotleCycle165

/-- For the Gaussian-quadrature range `s < k ≤ 2s`, the monomial `X^(k-1)`
admits Euclidean division by the shifted Legendre polynomial of degree `s`,
with a remainder of degree `< s`. -/
theorem monomial_div_mod_shiftedLegendre {s k : ℕ}
    (hsk : s < k) (hk : k ≤ 2 * s) :
    ∃ q r : ℝ[X],
      X ^ (k - 1) =
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q + r ∧
      r.natDegree < s := by
  sorry

end OpenMathAristotleCycle165
