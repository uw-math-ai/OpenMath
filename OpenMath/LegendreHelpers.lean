import Mathlib

open Finset Real Polynomial
open scoped BigOperators

/-- The coefficient of `x^l` in the explicit shifted Legendre expansion. -/
noncomputable def shiftedLegCoeff (s l : ℕ) : ℝ :=
  (-1 : ℝ) ^ (s + l) * (s.choose l : ℝ) * ((s + l).choose s : ℝ)

@[simp] lemma shiftedLegCoeff_gt (s l : ℕ) (h : s < l) : shiftedLegCoeff s l = 0 := by
  simp [shiftedLegCoeff, Nat.choose_eq_zero_of_lt h]

/-- The leading coefficient is `choose (2s) s`. -/
lemma shiftedLegCoeff_diag (s : ℕ) :
    shiftedLegCoeff s s = (Nat.choose (2 * s) s : ℝ) := by
  unfold shiftedLegCoeff
  have h1 : (-1 : ℝ) ^ (s + s) = 1 := by
    rw [show s + s = 2 * s by ring, pow_mul]
    simp
  rw [h1, one_mul, Nat.choose_self]
  simp
  congr 1
  omega

lemma shiftedLegCoeff_diag_pos (s : ℕ) : 0 < shiftedLegCoeff s s := by
  rw [shiftedLegCoeff_diag]
  exact_mod_cast Nat.choose_pos (by omega)

lemma shiftedLegCoeff_diag_ne_zero (s : ℕ) : shiftedLegCoeff s s ≠ 0 :=
  ne_of_gt (shiftedLegCoeff_diag_pos s)

/-- The polynomial `Q_j(X) = ∏_{m ∈ range s \ {j}} (X + (m+1))`. -/
noncomputable def Q_poly (s j : ℕ) : Polynomial ℝ :=
  ∏ m ∈ (Finset.range s).erase j, (X + C (↑(m + 1) : ℝ))

lemma Q_poly_natDegree_lt (s j : ℕ) (hj : j < s) : (Q_poly s j).natDegree < s := by
  have : (Q_poly s j).natDegree = s - 1 := by
    unfold Q_poly
    rw [natDegree_prod_of_monic _ _ (fun m _ => monic_X_add_C _)]
    simp only [natDegree_X_add_C, sum_const, card_erase_of_mem (mem_range.mpr hj), card_range]
    simp
  omega

lemma Q_poly_eval (s j : ℕ) (l : ℝ) :
    (Q_poly s j).eval l = ∏ m ∈ (Finset.range s).erase j, (l + ↑(m + 1)) := by
  simp [Q_poly, eval_prod]

/-- The `s`-th forward difference of `Q_j` vanishes at `0`. -/
lemma fwdDiff_Q_vanishes (s j : ℕ) (hj : j < s) :
    ∑ k ∈ Finset.range (s + 1),
      (-1 : ℝ) ^ (s - k) * ↑(s.choose k) *
        ∏ m ∈ (Finset.range s).erase j, ((k : ℝ) + ↑(m + 1)) = 0 := by
  have hdeg := Q_poly_natDegree_lt s j hj
  have h := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg
  have h2 := fwdDiff_iter_eq_sum_shift (1 : ℝ) (fun x => (Q_poly s j).eval x) s (0 : ℝ)
  rw [h] at h2
  simp only [Pi.zero_apply, Nat.smul_one_eq_cast, zero_add, Q_poly_eval] at h2
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] at h2
  linarith

lemma prod_range_eq_factorial_mul_choose (s l : ℕ) :
    (∏ m ∈ Finset.range s, ((l : ℝ) + ↑(m + 1))) = (s.factorial : ℝ) * ((s + l).choose s : ℝ) := by
  rw_mod_cast [← Nat.descFactorial_eq_factorial_mul_choose]
  rw [Nat.descFactorial_eq_prod_range]
  rw [← Finset.prod_range_reflect]
  exact Finset.prod_congr rfl fun x hx => by
    cases s <;> norm_num at *
    omega

/-- The core finite-sum orthogonality identity for shifted Legendre coefficients. -/
theorem orthogonality_sum_zero (s j : ℕ) (hj : j < s) :
    ∑ l ∈ Finset.range (s + 1),
      shiftedLegCoeff s l / ((l : ℝ) + ↑j + 1) = 0 := by
  have hForwardDiffVanishes :
      ∑ k ∈ Finset.range (s + 1),
        (-1 : ℝ) ^ (s - k) * Nat.choose s k *
          ∏ m ∈ ((Finset.range s).erase j), ((k : ℝ) + (m + 1)) = 0 := by
    convert fwdDiff_Q_vanishes s j hj using 1
    grind +splitImp
  have hTermRewrite :
      ∀ k ∈ Finset.range (s + 1),
        (-1 : ℝ) ^ (s - k) * Nat.choose s k *
            (∏ m ∈ ((Finset.range s).erase j), ((k : ℝ) + (m + 1))) =
          (Nat.factorial s : ℝ) * shiftedLegCoeff s k / ((k : ℝ) + (j + 1)) := by
    intro k hk
    have hProdDelete :
        (∏ m ∈ ((Finset.range s).erase j), ((k : ℝ) + (m + 1))) =
          (∏ m ∈ Finset.range s, ((k : ℝ) + (m + 1))) / ((k : ℝ) + (j + 1)) := by
      rw [eq_div_iff (by positivity), Finset.prod_erase_mul _ _ (Finset.mem_range.mpr hj)]
    have hProdFull :
        ∏ m ∈ Finset.range s, ((k : ℝ) + (m + 1)) =
          (Nat.factorial s : ℝ) * Nat.choose (s + k) s := by
      convert prod_range_eq_factorial_mul_choose s k using 1
      norm_cast
    simp_all +decide [mul_div_assoc, shiftedLegCoeff]
    rw [show s + k = s - k + (2 * k) by linarith [Nat.sub_add_cancel hk]]
    norm_num [pow_add, pow_mul]
    ring
  have hrewritten :
      ∑ k ∈ Finset.range (s + 1),
        (Nat.factorial s : ℝ) * shiftedLegCoeff s k / ((k : ℝ) + (j + 1)) = 0 := by
    have hsumEq :
        (∑ k ∈ Finset.range (s + 1),
          (-1 : ℝ) ^ (s - k) * Nat.choose s k *
            ∏ m ∈ ((Finset.range s).erase j), ((k : ℝ) + (m + 1))) =
        ∑ k ∈ Finset.range (s + 1),
          (Nat.factorial s : ℝ) * shiftedLegCoeff s k / ((k : ℝ) + (j + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hTermRewrite k hk]
    rw [← hsumEq]
    exact hForwardDiffVanishes
  have hfactorial_ne : (Nat.factorial s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero s)
  have hmul :
      (Nat.factorial s : ℝ) *
        (∑ l ∈ Finset.range (s + 1), shiftedLegCoeff s l / ((l : ℝ) + ↑j + 1)) = 0 := by
    simpa [Finset.mul_sum, mul_assoc, add_assoc, div_eq_mul_inv] using hrewritten
  exact (mul_eq_zero.mp hmul).resolve_left hfactorial_ne
