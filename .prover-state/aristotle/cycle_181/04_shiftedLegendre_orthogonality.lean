import OpenMath.Legendre
import OpenMath.LegendreHelpers

/-- Cycle 181 Aristotle target: produce a reusable orthogonality statement for
the sign-correct mapped shifted Legendre polynomial on `[0,1]`. -/
theorem cycle181_shiftedLegendre_orthogonality (s j : ℕ) (hj : j < s) :
    ∑ l ∈ Finset.range (s + 1),
      ((-1 : ℝ) ^ s *
          (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff l) /
        ((l : ℝ) + j + 1) = 0 := by
  sorry
