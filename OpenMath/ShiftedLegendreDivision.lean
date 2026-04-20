import OpenMath.Legendre
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

open Polynomial

namespace OpenMath

/-- For `s < k ≤ 2s`, Euclidean division of `X^(k-1)` by the mapped shifted
Legendre polynomial yields a remainder of degree `< s`. Harvested from
Aristotle project `679726ac-461a-49a9-be03-3a6f13dbb5fe` and adjusted to the
OpenMath environment. -/
theorem monomial_div_mod_shiftedLegendre {s k : ℕ}
    (hsk : s < k) (hk : k ≤ 2 * s) :
    ∃ q r : ℝ[X],
      X ^ (k - 1) =
        (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)) * q + r ∧
      r.natDegree < s := by
  set P : Polynomial ℝ := Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)
  have hP_nonzero : P ≠ 0 := by
    have hs : P.coeff s ≠ 0 := by
      rw [show P = Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s) by rfl]
      rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
      simp [Nat.choose_self]
      exact_mod_cast (Nat.choose_pos (Nat.le_add_left s s)).ne'
    intro hP0
    apply hs
    simp [hP0]
  refine ⟨X ^ (k - 1) / P, X ^ (k - 1) % P, ?_, ?_⟩
  · simpa [add_comm] using (EuclideanDomain.div_add_mod (X ^ (k - 1)) P).symm
  · have hdeg : (X ^ (k - 1) % P).degree < P.degree := EuclideanDomain.mod_lt _ hP_nonzero
    by_cases hr : X ^ (k - 1) % P = 0
    · simp [hr]
      omega
    · have hP_degree : P.degree = s := by
        refine le_antisymm ?_ ?_
        · rw [Polynomial.degree_le_iff_coeff_zero]
          intro m hm
          norm_cast at hm
          rw [show P = Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s) by rfl]
          rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
          simp [Nat.choose_eq_zero_of_lt hm]
        · have hs : P.coeff s ≠ 0 := by
            rw [show P = Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s) by rfl]
            rw [Polynomial.coeff_map, Polynomial.coeff_shiftedLegendre]
            simp [Nat.choose_self]
            exact_mod_cast (Nat.choose_pos (Nat.le_add_left s s)).ne'
          exact Polynomial.le_degree_of_ne_zero hs
      have hP_natdeg : P.natDegree = s := Polynomial.natDegree_eq_of_degree_eq_some hP_degree
      rw [← hP_natdeg]
      exact Polynomial.natDegree_lt_natDegree hr hdeg

end OpenMath
