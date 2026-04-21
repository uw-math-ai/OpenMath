import OpenMath.Pade

open Finset Complex Polynomial
open scoped BigOperators

/-!
# Padé Asymptotics Near the Origin

This helper layer isolates the polynomial coefficient/divisibility facts needed
to control the first neglected term of

`padeP n d z - padeQ n d z * expTaylor (n + d) z`.

The live order-star seam only needs the exact degree-`n + d + 1` coefficient and
the resulting `X^(n+d+2)` divisibility after subtracting that leading monomial.
-/

namespace PadeAsymptotics

/-- The truncated exponential as a polynomial in `ℂ[X]`. -/
noncomputable def expTaylor_poly (n : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (1 / (i.factorial : ℂ)) * Polynomial.X ^ i

/-- The Padé numerator polynomial in `ℂ[X]`. -/
noncomputable def padeP_poly (p q : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (p + 1),
    Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (p.factorial : ℂ) /
      (((p + q).factorial : ℂ) * ((p - j).factorial : ℂ) * (j.factorial : ℂ))) *
    Polynomial.X ^ j

/-- The Padé denominator polynomial in `ℂ[X]`. -/
noncomputable def padeQ_poly (p q : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (q + 1),
    Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (q.factorial : ℂ) /
      (((p + q).factorial : ℂ) * ((q - j).factorial : ℂ) * (j.factorial : ℂ)) *
      (-1) ^ j) *
    Polynomial.X ^ j

/-- The formal Padé defect against the order-`p+q` exponential truncation. -/
noncomputable def padeDefect_poly (p q : ℕ) : Polynomial ℂ :=
  padeP_poly p q - padeQ_poly p q * expTaylor_poly (p + q)

/-- Evaluation bridge for the polynomial Taylor truncation. -/
theorem expTaylor_poly_eval (n : ℕ) (z : ℂ) :
    (expTaylor_poly n).eval z = expTaylor n z := by
  unfold expTaylor_poly expTaylor
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp [div_eq_mul_inv, mul_comm]

/-- Evaluation bridge for the Padé numerator polynomial. -/
theorem padeP_poly_eval (p q : ℕ) (z : ℂ) :
    (padeP_poly p q).eval z = padeP p q z := by
  unfold padeP_poly padeP
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Evaluation bridge for the Padé denominator polynomial. -/
theorem padeQ_poly_eval (p q : ℕ) (z : ℂ) :
    (padeQ_poly p q).eval z = padeQ p q z := by
  unfold padeQ_poly padeQ
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [show (-z) ^ j = (-1 : ℂ) ^ j * z ^ j by
    rw [neg_eq_neg_one_mul, mul_pow]]
  ring

/-- Exact coefficients of the polynomial Taylor truncation. -/
theorem expTaylor_poly_coeff (m k : ℕ) :
    (expTaylor_poly m).coeff k =
      if k ≤ m then 1 / ((k.factorial : ℕ) : ℂ) else 0 := by
  unfold expTaylor_poly
  have hsum :
      (∑ i ∈ Finset.range (m + 1),
          (Polynomial.C (1 / (i.factorial : ℂ)) * Polynomial.X ^ i : Polynomial ℂ)).coeff k =
        ∑ i ∈ Finset.range (m + 1),
          ((Polynomial.C (1 / (i.factorial : ℂ)) * Polynomial.X ^ i : Polynomial ℂ)).coeff k := by
    simpa using (Finset.sum_apply k (Finset.range (m + 1)) fun i =>
      (Polynomial.C (1 / (i.factorial : ℂ)) * Polynomial.X ^ i : Polynomial ℂ))
  rw [hsum]
  by_cases hk : k ≤ m
  · rw [Finset.sum_eq_single k]
    · rw [if_pos hk, Polynomial.coeff_C_mul_X_pow]
      simp
    · intro j hj hne
      have hne' : k ≠ j := by
        intro h
        exact hne h.symm
      rw [Polynomial.coeff_C_mul_X_pow]
      simp [hne']
    · intro hk_mem
      exact False.elim <| hk_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [if_neg hk]
    have hzero : ∀ i ∈ Finset.range (m + 1),
        ((Polynomial.C (1 / (i.factorial : ℂ)) * Polynomial.X ^ i : Polynomial ℂ)).coeff k = 0 := by
      intro i hi
      have hik : k ≠ i := by
        intro h
        subst h
        exact hk (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      rw [Polynomial.coeff_C_mul_X_pow]
      simp [hik]
    exact Finset.sum_eq_zero hzero

/-- Exact coefficients of the Padé numerator polynomial. -/
theorem padeP_poly_coeff (p q k : ℕ) :
    (padeP_poly p q).coeff k =
      ((((p + q - k).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
        (p.choose k : ℂ) := by
  unfold padeP_poly
  have hsum :
      (∑ j ∈ Finset.range (p + 1),
          (Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (p.factorial : ℂ) /
            (((p + q).factorial : ℂ) * ((p - j).factorial : ℂ) * (j.factorial : ℂ))) *
            Polynomial.X ^ j : Polynomial ℂ)).coeff k =
        ∑ j ∈ Finset.range (p + 1),
          ((Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (p.factorial : ℂ) /
            (((p + q).factorial : ℂ) * ((p - j).factorial : ℂ) * (j.factorial : ℂ))) *
            Polynomial.X ^ j : Polynomial ℂ)).coeff k := by
    simpa using (Finset.sum_apply k (Finset.range (p + 1)) fun j =>
      (Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (p.factorial : ℂ) /
        (((p + q).factorial : ℂ) * ((p - j).factorial : ℂ) * (j.factorial : ℂ))) *
        Polynomial.X ^ j : Polynomial ℂ))
  rw [hsum]
  by_cases hk : k ≤ p
  · rw [Finset.sum_eq_single k]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl, Nat.cast_choose ℂ hk]
      ring_nf
    · intro j hj hne
      have hne' : k ≠ j := by
        intro h
        exact hne h.symm
      rw [Polynomial.coeff_C_mul_X_pow, if_neg hne']
    · intro hk_mem
      exact False.elim <| hk_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]
    have hzero : ∀ j ∈ Finset.range (p + 1),
        ((Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (p.factorial : ℂ) /
          (((p + q).factorial : ℂ) * ((p - j).factorial : ℂ) * (j.factorial : ℂ))) *
          Polynomial.X ^ j : Polynomial ℂ)).coeff k = 0 := by
      intro j hj
      have hkj : k ≠ j := by
        intro h
        subst h
        exact hk (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      rw [Polynomial.coeff_C_mul_X_pow, if_neg hkj]
    simpa using Finset.sum_eq_zero hzero

/-- Exact coefficients of the Padé denominator polynomial. -/
theorem padeQ_poly_coeff (p q k : ℕ) :
    (padeQ_poly p q).coeff k =
      ((((p + q - k).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
        (q.choose k : ℂ) * (-1 : ℂ) ^ k := by
  unfold padeQ_poly
  have hsum :
      (∑ j ∈ Finset.range (q + 1),
          (Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (q.factorial : ℂ) /
            (((p + q).factorial : ℂ) * ((q - j).factorial : ℂ) * (j.factorial : ℂ)) *
            (-1) ^ j) * Polynomial.X ^ j : Polynomial ℂ)).coeff k =
        ∑ j ∈ Finset.range (q + 1),
          ((Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (q.factorial : ℂ) /
            (((p + q).factorial : ℂ) * ((q - j).factorial : ℂ) * (j.factorial : ℂ)) *
            (-1) ^ j) * Polynomial.X ^ j : Polynomial ℂ)).coeff k := by
    simpa using (Finset.sum_apply k (Finset.range (q + 1)) fun j =>
      (Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (q.factorial : ℂ) /
        (((p + q).factorial : ℂ) * ((q - j).factorial : ℂ) * (j.factorial : ℂ)) *
        (-1) ^ j) * Polynomial.X ^ j : Polynomial ℂ))
  rw [hsum]
  by_cases hk : k ≤ q
  · rw [Finset.sum_eq_single k]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl, Nat.cast_choose ℂ hk]
      ring_nf
    · intro j hj hne
      have hne' : k ≠ j := by
        intro h
        exact hne h.symm
      rw [Polynomial.coeff_C_mul_X_pow, if_neg hne']
    · intro hk_mem
      exact False.elim <| hk_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]
    have hzero : ∀ j ∈ Finset.range (q + 1),
        ((Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (q.factorial : ℂ) /
          (((p + q).factorial : ℂ) * ((q - j).factorial : ℂ) * (j.factorial : ℂ)) *
          (-1) ^ j) * Polynomial.X ^ j : Polynomial ℂ)).coeff k = 0 := by
      intro j hj
      have hkj : k ≠ j := by
        intro h
        subst h
        exact hk (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      rw [Polynomial.coeff_C_mul_X_pow, if_neg hkj]
    simpa using Finset.sum_eq_zero hzero

/-- A Beta-function style alternating-binomial reciprocal sum used in the
degree-`p+q+1` coefficient computation. -/
theorem alternating_choose_reciprocal (p q : ℕ) :
    ∑ i ∈ Finset.range (q + 1),
      ((-1 : ℂ) ^ i) * (q.choose i : ℂ) / (p + 1 + i : ℂ) =
        ((p.factorial : ℂ) * (q.factorial : ℂ)) /
          (((p + q + 1).factorial : ℂ)) := by
  have hstep :
      ∀ p q : ℕ,
        (∑ i ∈ Finset.range (q + 2), ((-1 : ℂ) ^ i) * (q + 1).choose i / (p + 1 + i : ℂ)) =
          (∑ i ∈ Finset.range (q + 1), ((-1 : ℂ) ^ i) * (q.choose i : ℂ) / (p + 1 + i : ℂ)) -
            (∑ i ∈ Finset.range (q + 1), ((-1 : ℂ) ^ i) * (q.choose i : ℂ) / (p + 2 + i : ℂ)) := by
    intro p q
    have h := Finset.sum_choose_succ_mul (R := ℂ)
        (f := fun i _ => ((-1 : ℂ) ^ i) / (p + 1 + i : ℂ)) q
    have h' :
        (∑ i ∈ Finset.range (q + 2), ((-1 : ℂ) ^ i) * (q + 1).choose i / (p + 1 + i : ℂ)) =
          (∑ i ∈ Finset.range (q + 1), ((-1 : ℂ) ^ i) * (q.choose i : ℂ) / (p + 1 + i : ℂ)) +
            (∑ i ∈ Finset.range (q + 1),
              (q.choose i : ℂ) * (((-1 : ℂ) ^ (i + 1)) / (p + (i + (1 + 1)) : ℂ))) := by
      simpa [div_eq_mul_inv, Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm] using h
    have hneg :
        (∑ i ∈ Finset.range (q + 1),
          (q.choose i : ℂ) * (((-1 : ℂ) ^ (i + 1)) / (p + (i + (1 + 1)) : ℂ))) =
            -(∑ i ∈ Finset.range (q + 1),
              ((-1 : ℂ) ^ i) * (q.choose i : ℂ) / (p + 2 + i : ℂ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    rw [h', hneg, sub_eq_add_neg]
  induction q generalizing p with
  | zero =>
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
      have hp1 : (((p + 1).factorial : ℕ) : ℂ) = (p + 1 : ℂ) * (p.factorial : ℂ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hp1]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne',
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero p)]
  | succ q ih =>
      rw [hstep p q, ih p]
      have ih' := ih (p + 1)
      norm_num [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] at ih' ⊢
      rw [ih']
      have hp1 : (((p + 1).factorial : ℕ) : ℂ) = (p + 1 : ℂ) * (p.factorial : ℂ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hq1 : (((q + 1).factorial : ℕ) : ℂ) = (q + 1 : ℂ) * (q.factorial : ℂ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hp1, hq1]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne',
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)]
      have hpq2 : (((q + (p + 2)).factorial : ℕ) : ℂ) =
          (q + p + 2 : ℂ) * (((q + (p + 1)).factorial : ℕ) : ℂ) := by
        rw [show q + (p + 2) = (q + (p + 1)) + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      rw [hpq2]
      ring

/-- The Padé defect vanishes below degree `p + q + 1`. -/
theorem padeDefect_poly_coeff_lt (p q k : ℕ) (hk : k < p + q + 1) :
    (padeDefect_poly p q).coeff k = 0 := by
  sorry

/-- The exact degree-`p+q+1` coefficient of the Padé defect. -/
theorem padeDefect_poly_coeff_succ (p q : ℕ) :
    (padeDefect_poly p q).coeff (p + q + 1) =
      (1 / (((p + q + 1).factorial : ℂ))) - (padePhiErrorConst p q : ℂ) := by
  sorry

/-- After removing the explicit leading monomial, the Padé defect is divisible by
`X^(p+q+2)`. -/
theorem padeDefect_poly_sub_leading_X_pow_dvd (p q : ℕ) :
    Polynomial.X ^ (p + q + 2) ∣
      (padeDefect_poly p q -
        Polynomial.C
            ((1 / (((p + q + 1).factorial : ℂ))) - (padePhiErrorConst p q : ℂ)) *
          Polynomial.X ^ (p + q + 1)) := by
  sorry

/-- Function-level factorization of the Padé defect after removing the leading
degree-`p+q+1` term. -/
theorem padeDefect_sub_leading_factorization (p q : ℕ) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      padeP p q z - padeQ p q z * expTaylor (p + q) z -
        ((1 / (((p + q + 1).factorial : ℂ))) - (padePhiErrorConst p q : ℂ)) *
          z ^ (p + q + 1) =
      z ^ (p + q + 2) * h z := by
  sorry

end PadeAsymptotics

/-- Honest leading-term expansion of `padeR n d z * exp (-z)` at the origin. -/
theorem padeR_exp_neg_leading_term
    (n d : ℕ) :
    ∃ g : ℂ → ℂ, ∀ z : ℂ,
      padeR n d z * exp (-z) -
        (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) =
      z ^ (n + d + 2) * g z := by
  sorry
