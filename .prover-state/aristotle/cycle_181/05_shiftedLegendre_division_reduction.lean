import OpenMath.Legendre
import OpenMath.ShiftedLegendreDivision

/-- Cycle 181 Aristotle target: package the monomial-division remainder step in
the form needed by `gaussLegendre_B_double`. -/
theorem cycle181_shiftedLegendre_division_reduction {s j : ℕ}
    (hj : j < s) :
    ∃ q r : Polynomial ℝ,
      Polynomial.X ^ (s + j) =
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q + r ∧
      r.natDegree < s := by
  sorry
