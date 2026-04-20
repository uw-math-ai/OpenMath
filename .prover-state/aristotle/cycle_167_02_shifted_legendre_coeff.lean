import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

open Polynomial

theorem cycle167_shiftedLegendre_coeff_nonzero (s : ℕ) :
    (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff s ≠ 0 := by
  sorry
