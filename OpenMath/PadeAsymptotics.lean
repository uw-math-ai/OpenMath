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

/-- Reflected form of `alternating_choose_reciprocal`, with denominator
`p + q + 1 - i`. -/
theorem alternating_choose_reciprocal_reflect (p q : ℕ) :
    ∑ i ∈ Finset.range (q + 1),
      (q.choose i : ℂ) * (-1 : ℂ) ^ i / (p + q + 1 - i : ℂ) =
        (-1 : ℂ) ^ q * ((p.factorial : ℂ) * (q.factorial : ℂ)) /
          (((p + q + 1).factorial : ℂ)) := by
  calc
    ∑ i ∈ Finset.range (q + 1), (q.choose i : ℂ) * (-1 : ℂ) ^ i / (p + q + 1 - i : ℂ)
      = (-1 : ℂ) ^ q *
          ∑ i ∈ Finset.range (q + 1), ((-1 : ℂ) ^ i) * (q.choose i : ℂ) / (p + 1 + i : ℂ) := by
            rw [← Finset.sum_flip]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi' : i ≤ q := Finset.mem_range_succ_iff.mp hi
            rw [Nat.choose_symm hi', Nat.cast_sub hi']
            have hden : (↑p + ↑q + 1 - (↑q - ↑i) : ℂ) = (p + 1 + i : ℂ) := by
              ring
            rw [hden]
            have hpow : (-1 : ℂ) ^ q = (-1 : ℂ) ^ (q - i) * (-1 : ℂ) ^ i := by
              rw [← pow_add, Nat.sub_add_cancel hi']
            rw [hpow]
            have hsq : (-1 : ℂ) ^ (i * 2) = 1 := by
              rw [Nat.mul_comm, pow_mul]
              norm_num
            ring_nf
            rw [hsq]
            ring
    _ = (-1 : ℂ) ^ q * (((p.factorial : ℂ) * (q.factorial : ℂ)) /
          (((p + q + 1).factorial : ℂ))) := by
            rw [alternating_choose_reciprocal]
    _ = ((-1 : ℂ) ^ q * ((p.factorial : ℂ) * (q.factorial : ℂ))) /
          (((p + q + 1).factorial : ℂ)) := by
            ring

/-- Alternating Vandermonde convolution from the coefficient of
`((X + 1) + (-X))^q * (X + 1)^p`. -/
theorem alternating_vandermonde_choose (p q k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      (q.choose j : ℂ) * (-1 : ℂ) ^ j * ((p + q - j).choose (k - j) : ℂ)) =
        (p.choose k : ℂ) := by
  let S : Polynomial ℂ :=
    ∑ j ∈ Finset.range (q + 1),
      Polynomial.C (q.choose j : ℂ) * (-Polynomial.X) ^ j * (Polynomial.X + 1) ^ (p + q - j)
  have hadd :
      ∑ j ∈ Finset.range (q + 1),
        Polynomial.C (q.choose j : ℂ) * (-Polynomial.X) ^ j * (Polynomial.X + 1) ^ (q - j) =
        ((-Polynomial.X) + (Polynomial.X + 1)) ^ q := by
    simpa [Nat.cast_choose, mul_assoc, mul_left_comm, mul_comm] using
      ((add_pow (-Polynomial.X) (Polynomial.X + 1) q).symm :
        (∑ m ∈ Finset.range (q + 1),
          (-Polynomial.X) ^ m * (Polynomial.X + 1) ^ (q - m) * (q.choose m : Polynomial ℂ)) =
            ((-Polynomial.X) + (Polynomial.X + 1)) ^ q)
  have hS : S = (Polynomial.X + 1 : Polynomial ℂ) ^ p := by
    unfold S
    calc
      ∑ j ∈ Finset.range (q + 1),
          Polynomial.C (q.choose j : ℂ) * (-Polynomial.X) ^ j * (Polynomial.X + 1) ^ (p + q - j)
        = ∑ j ∈ Finset.range (q + 1),
            (Polynomial.C (q.choose j : ℂ) * (-Polynomial.X) ^ j * (Polynomial.X + 1) ^ (q - j)) *
              (Polynomial.X + 1) ^ p := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                have hjq : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
                rw [show p + q - j = (q - j) + p by omega]
                ring_nf
      _ = (((-Polynomial.X) + (Polynomial.X + 1)) ^ q) * (Polynomial.X + 1) ^ p := by
            rw [← hadd, Finset.sum_mul]
      _ = (Polynomial.X + 1 : Polynomial ℂ) ^ p := by simp
  have hterm :
      ∀ j : ℕ,
        (Polynomial.C (q.choose j : ℂ) * (-Polynomial.X) ^ j * (Polynomial.X + 1) ^ (p + q - j)).coeff
            k =
          if j ≤ k then (q.choose j : ℂ) * (-1 : ℂ) ^ j * ((p + q - j).choose (k - j) : ℂ) else 0 := by
    intro j
    rw [show (-Polynomial.X : Polynomial ℂ) ^ j = Polynomial.C ((-1 : ℂ) ^ j) * Polynomial.X ^ j by
      rw [show (-Polynomial.X : Polynomial ℂ) = Polynomial.C (-1 : ℂ) * Polynomial.X by simp,
        mul_pow, Polynomial.C_pow]]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_assoc]
    rw [show Polynomial.C (↑(q.choose j) * (-1 : ℂ) ^ j) *
        (Polynomial.X ^ j * (Polynomial.X + 1) ^ (p + q - j)) =
        (Polynomial.C (↑(q.choose j) * (-1 : ℂ) ^ j) * (Polynomial.X + 1) ^ (p + q - j)) *
          Polynomial.X ^ j by ring]
    rw [Polynomial.coeff_mul_X_pow']
    by_cases hjk : j ≤ k
    · rw [if_pos hjk, Polynomial.coeff_C_mul]
      have hpow : ((Polynomial.X + 1 : Polynomial ℂ) ^ (p + q - j)).coeff (k - j) =
          ((p + q - j).choose (k - j) : ℂ) := by
        simpa using (Polynomial.coeff_X_add_C_pow (1 : ℂ) (p + q - j) (k - j))
      rw [hpow]
      simp [hjk, mul_left_comm, mul_comm]
    · rw [if_neg hjk]
      simp [hjk]
  have hcoeff_left : S.coeff k =
      ∑ j ∈ Finset.range (k + 1),
        (q.choose j : ℂ) * (-1 : ℂ) ^ j * ((p + q - j).choose (k - j) : ℂ) := by
    have hsum :
        (∑ j ∈ Finset.range (q + 1),
          Polynomial.C (q.choose j : ℂ) * (-Polynomial.X) ^ j * (Polynomial.X + 1) ^ (p + q - j)).coeff
            k =
        ∑ j ∈ Finset.range (q + 1),
          (Polynomial.C (q.choose j : ℂ) * (-Polynomial.X) ^ j * (Polynomial.X + 1) ^ (p + q - j)).coeff
            k := by
      simpa using (Finset.sum_apply k (Finset.range (q + 1)) fun j =>
        Polynomial.C (q.choose j : ℂ) * (-Polynomial.X) ^ j * (Polynomial.X + 1) ^ (p + q - j))
    unfold S
    rw [hsum]
    simp_rw [hterm]
    by_cases hkq : k ≤ q
    · rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hkq))]
      · refine Finset.sum_congr rfl ?_
        intro j hj
        rw [if_pos]
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      · intro j hjq' hjk'
        rw [if_neg]
        intro hjle
        exact hjk' (Finset.mem_range.mpr (Nat.lt_succ_of_le hjle))
    · have hqk : q < k := lt_of_not_ge hkq
      have hsub : Finset.range (q + 1) ⊆ Finset.range (k + 1) :=
        Finset.range_mono (Nat.succ_le_succ hqk.le)
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl ?_
        intro j hj
        rw [if_pos]
        exact le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hqk.le
      · intro j hjk' hjq'
        have hqj : q < j := by
          by_contra hqj'
          exact hjq' (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_of_not_gt hqj')))
        simp [Nat.choose_eq_zero_of_lt hqj]
  have hcoeff_right : ((Polynomial.X + 1 : Polynomial ℂ) ^ p).coeff k = (p.choose k : ℂ) := by
    simpa using (Polynomial.coeff_X_add_C_pow (1 : ℂ) p k)
  rw [← hcoeff_left, hS, hcoeff_right]

/-- The degree-`p+q+1` coefficient of `padeQ_poly * expTaylor_poly` reduces to a
single reflected reciprocal sum. -/
theorem padeQ_mul_expTaylor_coeff_succ (p q : ℕ) :
    (padeQ_poly p q * expTaylor_poly (p + q)).coeff (p + q + 1) =
      ∑ j ∈ Finset.range (q + 1),
        (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 1 - j : ℂ) /
          (((p + q).factorial : ℂ)) -
        1 / ((p + q + 1 : ℂ)) / (((p + q).factorial : ℂ)) := by
  have hconv :
      (padeQ_poly p q * expTaylor_poly (p + q)).coeff (p + q + 1) =
        ∑ j ∈ Finset.Icc 1 q,
          (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (p + q + 1 - j) := by
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    let f : ℕ → ℂ := fun j =>
      (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (p + q + 1 - j)
    change ∑ j ∈ Finset.range (p + q + 1 + 1), f j = ∑ j ∈ Finset.Icc 1 q, f j
    symm
    rw [Finset.sum_subset]
    · intro j hjIcc
      exact Finset.mem_range.mpr (by
        have hj := Finset.mem_Icc.mp hjIcc
        omega)
    · intro j hjrange hjnot
      dsimp [f]
      by_cases h0 : j = 0
      · subst h0
        rw [padeQ_poly_coeff, expTaylor_poly_coeff]
        simp
      · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
        have hnotle : ¬ j ≤ q := by
          intro hjq
          exact hjnot (Finset.mem_Icc.mpr ⟨hj1, hjq⟩)
        have hqj : q < j := lt_of_not_ge hnotle
        rw [padeQ_poly_coeff]
        rw [Nat.choose_eq_zero_of_lt hqj]
        simp
  have hsub :
      (∑ j ∈ Finset.Icc 1 q,
        (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (p + q + 1 - j)) =
      ∑ j ∈ Finset.range (q + 1),
        (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 1 - j : ℂ) /
          (((p + q).factorial : ℂ)) -
        1 / ((p + q + 1 : ℂ)) / (((p + q).factorial : ℂ)) := by
    have hIcc : Finset.Icc 1 q = Finset.Ico 1 (q + 1) := by
      ext j
      simp [Finset.mem_Icc, Finset.mem_Ico, Nat.succ_le_iff]
    rw [hIcc]
    have hformula :
        ∀ j ∈ Finset.Ico 1 (q + 1),
          (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (p + q + 1 - j) =
            (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 1 - j : ℂ) /
              (((p + q).factorial : ℂ)) := by
      intro j hj
      rw [padeQ_poly_coeff, expTaylor_poly_coeff]
      have hjpos : 0 < j := (Finset.mem_Ico.mp hj).1
      have hjle : j ≤ q := Nat.le_of_lt_succ (Finset.mem_Ico.mp hj).2
      have hkj : p + q + 1 - j ≤ p + q := by omega
      rw [if_pos hkj]
      have hstep : (((p + q + 1 - j).factorial : ℕ) : ℂ) =
          (↑p + ↑q + 1 - ↑j : ℂ) * (((p + q - j).factorial : ℕ) : ℂ) := by
        have hnat : p + q + 1 - j = (p + q - j) + 1 := by omega
        rw [hnat, Nat.factorial_succ]
        push_cast
        have hcast : ((p + q - j : ℕ) : ℂ) + 1 = (↑p + ↑q + 1 - ↑j : ℂ) := by
          rw [Nat.cast_sub (show j ≤ p + q by omega)]
          have hpq : ((p + q : ℕ) : ℂ) = (↑p + ↑q : ℂ) := by norm_num
          rw [hpq]
          ring
        rw [hcast]
      have hden_ne : (↑p + ↑q + 1 - ↑j : ℂ) ≠ 0 := by
        intro h
        have hnat : (p + q + 1 : ℤ) - j = 0 := by exact_mod_cast h
        omega
      rw [hstep]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (p + q)).ne',
        Nat.cast_ne_zero.mpr (Nat.factorial_pos (p + q - j)).ne', hden_ne]
    have hsum :
        (∑ j ∈ Finset.Ico 1 (q + 1),
          (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (p + q + 1 - j)) =
        ∑ j ∈ Finset.Ico 1 (q + 1),
          (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 1 - j : ℂ) /
            (((p + q).factorial : ℂ)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact hformula j hj
    rw [hsum, Finset.sum_Ico_eq_sub]
    · simp only [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (p + q)).ne',
        Nat.cast_ne_zero.mpr (show p + q + 1 ≠ 0 by omega)]
      ring_nf
    · omega
  rw [hconv, hsub]

/-- The degree-`p+q+2` coefficient of `padeQ_poly * expTaylor_poly` reduces to a
second reflected reciprocal sum after discarding the vanishing `j = 0, 1`
Taylor terms. -/
theorem padeQ_mul_expTaylor_coeff_succ_succ (p q : ℕ) :
    (padeQ_poly p q * expTaylor_poly (p + q)).coeff (p + q + 2) =
      ∑ j ∈ Finset.range (q + 1),
        (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 2 - j : ℂ) /
          (p + q + 1 - j : ℂ) / (((p + q).factorial : ℂ)) -
        1 / (((p + q + 2).factorial : ℂ)) +
        ((q : ℂ) / (p + q : ℂ)) / (((p + q + 1).factorial : ℂ)) := by
  have hconv :
      (padeQ_poly p q * expTaylor_poly (p + q)).coeff (p + q + 2) =
        ∑ j ∈ Finset.Icc 2 q,
          (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (p + q + 2 - j) := by
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    let f : ℕ → ℂ := fun j =>
      (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (p + q + 2 - j)
    change ∑ j ∈ Finset.range (p + q + 2 + 1), f j = ∑ j ∈ Finset.Icc 2 q, f j
    symm
    rw [Finset.sum_subset]
    · intro j hjIcc
      exact Finset.mem_range.mpr (by
        have hj := Finset.mem_Icc.mp hjIcc
        omega)
    · intro j hjrange hjnot
      dsimp [f]
      have hjlt : j < p + q + 2 + 1 := Finset.mem_range.mp hjrange
      have hjcases : j = 0 ∨ j = 1 ∨ q < j := by
        by_cases htwo : 2 ≤ j
        · have hnotle : ¬ j ≤ q := by
            intro hjq
            exact hjnot (Finset.mem_Icc.mpr ⟨htwo, hjq⟩)
          exact Or.inr (Or.inr (lt_of_not_ge hnotle))
        · have hjle1 : j ≤ 1 := by omega
          omega
      rcases hjcases with rfl | rfl | hqj
      · rw [padeQ_poly_coeff, expTaylor_poly_coeff, if_neg (by omega)]
        simp
      · rw [padeQ_poly_coeff, expTaylor_poly_coeff, if_neg (by omega)]
        simp
      · rw [padeQ_poly_coeff]
        rw [Nat.choose_eq_zero_of_lt hqj]
        simp
  have hsub :
      (∑ j ∈ Finset.Icc 2 q,
        (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (p + q + 2 - j)) =
      ∑ j ∈ Finset.range (q + 1),
        (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 2 - j : ℂ) /
          (p + q + 1 - j : ℂ) / (((p + q).factorial : ℂ)) -
        1 / (((p + q + 2).factorial : ℂ)) +
        ((q : ℂ) / (p + q : ℂ)) / (((p + q + 1).factorial : ℂ)) := by
    sorry
  rw [hconv, hsub]

/-- The Padé defect vanishes below degree `p + q + 1`. -/
theorem padeDefect_poly_coeff_lt (p q k : ℕ) (hk : k < p + q + 1) :
    (padeDefect_poly p q).coeff k = 0 := by
  have hk' : k ≤ p + q := by omega
  have hconv :
      (padeQ_poly p q * expTaylor_poly (p + q)).coeff k =
        ∑ j ∈ Finset.range (k + 1),
          (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (k - j) := by
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hQ :
      (padeQ_poly p q * expTaylor_poly (p + q)).coeff k =
        ((((p + q - k).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
          (∑ j ∈ Finset.range (k + 1),
            (q.choose j : ℂ) * (-1 : ℂ) ^ j * ((p + q - j).choose (k - j) : ℂ)) := by
    rw [hconv]
    have hterm : ∀ j ∈ Finset.range (k + 1),
        (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (k - j) =
          ((((p + q - k).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
            ((q.choose j : ℂ) * (-1 : ℂ) ^ j * ((p + q - j).choose (k - j) : ℂ)) := by
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [padeQ_poly_coeff, expTaylor_poly_coeff, if_pos (show k - j ≤ p + q by omega)]
      have hscale :
          ((((p + q - j).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
            (1 / ((k - j).factorial : ℂ)) =
          ((((p + q - k).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
            ((p + q - j).choose (k - j) : ℂ) := by
        have hchoose : ((((p + q - j).factorial : ℕ) : ℂ) * (1 / ((k - j).factorial : ℂ))) =
            (((p + q - k).factorial : ℕ) : ℂ) * ((p + q - j).choose (k - j) : ℂ) := by
          rw [Nat.cast_choose ℂ (show k - j ≤ p + q - j by omega)]
          rw [show p + q - j - (k - j) = p + q - k by omega]
          field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (k - j)).ne',
            Nat.cast_ne_zero.mpr (Nat.factorial_pos (p + q - k)).ne']
        calc
          ((((p + q - j).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) * (1 / ((k - j).factorial : ℂ))
            = ((((p + q - j).factorial : ℕ) : ℂ) * (1 / ((k - j).factorial : ℂ))) /
                (((p + q).factorial : ℂ)) := by ring
          _ = ((((p + q - k).factorial : ℕ) : ℂ) * ((p + q - j).choose (k - j) : ℂ)) /
                (((p + q).factorial : ℂ)) := by rw [hchoose]
          _ = ((((p + q - k).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
                ((p + q - j).choose (k - j) : ℂ) := by ring
      calc
        ((((p + q - j).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) * (q.choose j : ℂ) *
            (-1 : ℂ) ^ j * (1 / ((k - j).factorial : ℂ))
          = (((((p + q - j).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
              (1 / ((k - j).factorial : ℂ))) * ((q.choose j : ℂ) * (-1 : ℂ) ^ j) := by ring
        _ = (((((p + q - k).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
              ((p + q - j).choose (k - j) : ℂ)) * ((q.choose j : ℂ) * (-1 : ℂ) ^ j) := by
                rw [hscale]
        _ = ((((p + q - k).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
              ((q.choose j : ℂ) * (-1 : ℂ) ^ j * ((p + q - j).choose (k - j) : ℂ)) := by ring
    have hsum :
        (∑ j ∈ Finset.range (k + 1), (padeQ_poly p q).coeff j * (expTaylor_poly (p + q)).coeff (k - j)) =
        ∑ j ∈ Finset.range (k + 1),
          ((((p + q - k).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
            ((q.choose j : ℂ) * (-1 : ℂ) ^ j * ((p + q - j).choose (k - j) : ℂ)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact hterm j hj
    rw [hsum, ← Finset.mul_sum]
  rw [padeDefect_poly, Polynomial.coeff_sub, padeP_poly_coeff, hQ,
    alternating_vandermonde_choose]
  ring

/-- The exact degree-`p+q+1` coefficient of the Padé defect. -/
theorem padeDefect_poly_coeff_succ (p q : ℕ) :
    (padeDefect_poly p q).coeff (p + q + 1) =
      (1 / (((p + q + 1).factorial : ℂ))) - (padePhiErrorConst p q : ℂ) := by
  unfold padeDefect_poly
  rw [Polynomial.coeff_sub, padeP_poly_coeff, padeQ_mul_expTaylor_coeff_succ]
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  have hsum :
      ∑ j ∈ Finset.range (q + 1),
        (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 1 - j : ℂ) /
          (((p + q).factorial : ℂ)) =
        (((-1 : ℂ) ^ q * ((p.factorial : ℂ) * (q.factorial : ℂ))) /
          (((p + q + 1).factorial : ℂ))) / (((p + q).factorial : ℂ)) := by
    rw [← Finset.sum_div]
    rw [alternating_choose_reciprocal_reflect]
  rw [hsum]
  have hfact :
      (1 / ((p + q + 1 : ℂ))) / (((p + q).factorial : ℂ)) =
        1 / (((p + q + 1).factorial : ℂ)) := by
    have hstep : (((p + q + 1).factorial : ℕ) : ℂ) =
        (p + q + 1 : ℂ) * (((p + q).factorial : ℕ) : ℂ) := by
      rw [show p + q + 1 = (p + q) + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    rw [hstep]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (p + q)).ne',
      Nat.cast_ne_zero.mpr (show p + q + 1 ≠ 0 by omega)]
  rw [hfact]
  norm_num [padePhiErrorConst]
  ring

/-- The exact degree-`p+q+2` coefficient of the Padé defect. -/
theorem padeDefect_poly_coeff_succ_succ (p q : ℕ) :
    (padeDefect_poly p q).coeff (p + q + 2) =
      (1 / (((p + q + 2).factorial : ℂ))) -
        ((q : ℂ) / (p + q : ℂ)) / (((p + q + 1).factorial : ℂ)) -
        (padePhiErrorConst p q : ℂ) * ((q + 1 : ℂ) / (p + q + 2 : ℂ)) := by
  unfold padeDefect_poly
  rw [Polynomial.coeff_sub, padeP_poly_coeff, padeQ_mul_expTaylor_coeff_succ_succ]
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  let fullSum : ℂ :=
    ∑ j ∈ Finset.range (q + 1),
      (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 2 - j : ℂ) /
        (p + q + 1 - j : ℂ) / (((p + q).factorial : ℂ))
  have hsplit :
      fullSum =
        (∑ j ∈ Finset.range (q + 1),
          (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 1 - j : ℂ) /
            (((p + q).factorial : ℂ)) ) -
        (∑ j ∈ Finset.range (q + 1),
          (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 2 - j : ℂ) /
            (((p + q).factorial : ℂ)) ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjq : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hden1 : (p + q + 1 - j : ℂ) ≠ 0 := by
      intro h
      have hnat : (p + q + 1 : ℤ) - j = 0 := by exact_mod_cast h
      omega
    have hden2 : (p + q + 2 - j : ℂ) ≠ 0 := by
      intro h
      have hnat : (p + q + 2 : ℤ) - j = 0 := by exact_mod_cast h
      omega
    field_simp [hden1, hden2, Nat.cast_ne_zero.mpr (Nat.factorial_pos (p + q)).ne']
    ring
  have hsum1 :
      ∑ j ∈ Finset.range (q + 1),
        (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 1 - j : ℂ) /
          (((p + q).factorial : ℂ)) =
        (((-1 : ℂ) ^ q * ((p.factorial : ℂ) * (q.factorial : ℂ))) /
          (((p + q + 1).factorial : ℂ))) / (((p + q).factorial : ℂ)) := by
    rw [← Finset.sum_div]
    rw [alternating_choose_reciprocal_reflect]
  have hsum2 :
      ∑ j ∈ Finset.range (q + 1),
        (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 2 - j : ℂ) /
          (((p + q).factorial : ℂ)) =
        (((-1 : ℂ) ^ q * (((p + 1).factorial : ℂ) * (q.factorial : ℂ))) /
          (((p + q + 2).factorial : ℂ))) / (((p + q).factorial : ℂ)) := by
    have hbase := alternating_choose_reciprocal_reflect (p + 1) q
    have hdiv := congrArg (fun z : ℂ => z / (((p + q).factorial : ℂ))) hbase
    have hnorm :
        ∑ j ∈ Finset.range (q + 1),
          (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 2 - j : ℂ) /
            (((p + q).factorial : ℂ)) =
        ∑ i ∈ Finset.range (q + 1),
          (q.choose i : ℂ) * (-1 : ℂ) ^ i / ((p + 1) + q + 1 - i : ℂ) /
            (((p + q).factorial : ℂ)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      congr 1
      ring_nf
    rw [hnorm]
    simpa [Finset.sum_div, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdiv
  have hfull :
      (∑ j ∈ Finset.range (q + 1),
        (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 2 - j : ℂ) /
          (p + q + 1 - j : ℂ) / (((p + q).factorial : ℂ))) = fullSum := by
    rfl
  have hcoeff :
      ((((-1 : ℂ) ^ q * (((p + 1).factorial : ℂ) * (q.factorial : ℂ))) /
          (((p + q + 2).factorial : ℂ))) / (((p + q).factorial : ℂ))) -
        ((((-1 : ℂ) ^ q * ((p.factorial : ℂ) * (q.factorial : ℂ))) /
          (((p + q + 1).factorial : ℂ))) / (((p + q).factorial : ℂ))) =
      -(padePhiErrorConst p q : ℂ) * ((q + 1 : ℂ) / (p + q + 2 : ℂ)) := by
    norm_num [padePhiErrorConst]
    have hp1 :
        (((p + 1).factorial : ℕ) : ℂ) =
          (p + 1 : ℂ) * (((p).factorial : ℕ) : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hm2 :
        (((p + q + 2).factorial : ℕ) : ℂ) =
          (p + q + 2 : ℂ) * (((p + q + 1).factorial : ℕ) : ℂ) := by
      rw [show p + q + 2 = (p + q + 1) + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    rw [hp1, hm2]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne',
      Nat.cast_ne_zero.mpr (Nat.factorial_pos q).ne',
      Nat.cast_ne_zero.mpr (Nat.factorial_pos (p + q)).ne',
      Nat.cast_ne_zero.mpr (Nat.factorial_pos (p + q + 1)).ne',
      Nat.cast_ne_zero.mpr (show p + q + 2 ≠ 0 by omega)]
    have hneq : (↑p + ↑q + 2 : ℂ) ≠ 0 := by
      exact_mod_cast (show p + q + 2 ≠ 0 by omega)
    field_simp [hneq]
    ring
  simp
  rw [hfull]
  let A : ℂ :=
    (((-1 : ℂ) ^ q * ((p.factorial : ℂ) * (q.factorial : ℂ))) /
      (((p + q + 1).factorial : ℂ))) / (((p + q).factorial : ℂ))
  let B : ℂ :=
    (((-1 : ℂ) ^ q * (((p + 1).factorial : ℂ) * (q.factorial : ℂ))) /
      (((p + q + 2).factorial : ℂ))) / (((p + q).factorial : ℂ))
  have hcoeff' : B - A =
      -(padePhiErrorConst p q : ℂ) * ((q + 1 : ℂ) / (p + q + 2 : ℂ)) := by
    simpa [A, B] using hcoeff
  have hmain :
      (1 / (((p + q + 2).factorial : ℂ))) -
          ((q : ℂ) / (p + q : ℂ)) / (((p + q + 1).factorial : ℂ)) - fullSum =
        (1 / (((p + q + 2).factorial : ℂ))) -
          ((q : ℂ) / (p + q : ℂ)) / (((p + q + 1).factorial : ℂ)) -
          (padePhiErrorConst p q : ℂ) * ((q + 1 : ℂ) / (p + q + 2 : ℂ)) := by
    calc
      (1 / (((p + q + 2).factorial : ℂ))) -
          ((q : ℂ) / (p + q : ℂ)) / (((p + q + 1).factorial : ℂ)) - fullSum =
        (1 / (((p + q + 2).factorial : ℂ))) -
          ((q : ℂ) / (p + q : ℂ)) / (((p + q + 1).factorial : ℂ)) +
          (B - A) := by
            rw [hsplit, hsum1, hsum2]
            dsimp [A, B]
            ring
      _ = (1 / (((p + q + 2).factorial : ℂ))) -
          ((q : ℂ) / (p + q : ℂ)) / (((p + q + 1).factorial : ℂ)) -
          (padePhiErrorConst p q : ℂ) * ((q + 1 : ℂ) / (p + q + 2 : ℂ)) := by
            rw [hcoeff']
            ring
  convert hmain using 1 <;> ring

/-- After removing the explicit leading monomial, the Padé defect is divisible by
`X^(p+q+2)`. -/
theorem padeDefect_poly_sub_leading_X_pow_dvd (p q : ℕ) :
    Polynomial.X ^ (p + q + 2) ∣
      (padeDefect_poly p q -
        Polynomial.C
            ((1 / (((p + q + 1).factorial : ℂ))) - (padePhiErrorConst p q : ℂ)) *
          Polynomial.X ^ (p + q + 1)) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  by_cases hlt : d < p + q + 1
  · rw [Polynomial.coeff_sub, padeDefect_poly_coeff_lt _ _ _ hlt,
      Polynomial.coeff_C_mul_X_pow]
    simp [Nat.ne_of_lt hlt]
  · have hdEq : d = p + q + 1 := by omega
    subst hdEq
    rw [Polynomial.coeff_sub, padeDefect_poly_coeff_succ, Polynomial.coeff_C_mul_X_pow]
    simp

/-- Function-level factorization of the Padé defect after removing the leading
degree-`p+q+1` term. -/
theorem padeDefect_sub_leading_factorization (p q : ℕ) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      padeP p q z - padeQ p q z * expTaylor (p + q) z -
        ((1 / (((p + q + 1).factorial : ℂ))) - (padePhiErrorConst p q : ℂ)) *
          z ^ (p + q + 1) =
      z ^ (p + q + 2) * h z := by
  obtain ⟨g, hg⟩ := padeDefect_poly_sub_leading_X_pow_dvd p q
  refine ⟨fun z => g.eval z, ?_⟩
  intro z
  have hEval := congrArg (fun r : Polynomial ℂ => r.eval z) hg
  simpa [padeDefect_poly, padeP_poly_eval, padeQ_poly_eval, expTaylor_poly_eval,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X] using hEval

end PadeAsymptotics

/-- Honest leading-term expansion of `padeR n d z * exp (-z)` at the origin. -/
theorem padeR_exp_neg_leading_term
    (n d : ℕ) :
    ∃ g : ℂ → ℂ, ∀ z : ℂ,
      padeR n d z * exp (-z) -
        (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) =
      z ^ (n + d + 2) * g z := by
  refine ⟨fun z => if z = 0 then 0 else
    (padeR n d z * exp (-z) - (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))) /
      z ^ (n + d + 2), ?_⟩
  intro z
  by_cases hz : z = 0
  · subst hz
    simp [padeR, padeP_eval_zero, padeQ_eval_zero]
  · simp [hz, div_eq_mul_inv, mul_left_comm, mul_comm]

/-- The Padé denominator stays nonzero on a neighborhood of the origin. -/
theorem padeQ_ne_zero_nhds
    (n d : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ z : ℂ, ‖z‖ < δ₀ → padeQ n d z ≠ 0 := by
  exact padeQ_nonzero_near_zero n d

/-- Near the origin, the reciprocal Padé denominator is uniformly bounded. -/
theorem padeQ_inv_bound
    (n d : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ z : ℂ, ‖z‖ < δ₀ → ‖(padeQ n d z)⁻¹‖ ≤ 2 := by
  exact padeQ_inv_norm_le_two_near_zero n d

/-- On the closed unit disk, `padeQ n d z - 1` grows at most linearly in `‖z‖`. -/
theorem padeQ_sub_one_lipschitz
    (n d : ℕ) :
    ∃ C > 0, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖padeQ n d z - 1‖ ≤ C * ‖z‖ := by
  let p : Polynomial ℂ := PadeAsymptotics.padeQ_poly n d - 1
  have hp_eval : ∀ z : ℂ, p.eval z = padeQ n d z - 1 := by
    intro z
    simp [p, PadeAsymptotics.padeQ_poly_eval]
  have hp_zero : p.eval 0 = 0 := by
    simp [hp_eval, padeQ_eval_zero]
  have hp_root : p.IsRoot 0 := hp_zero
  have hX_dvd : Polynomial.X ∣ p := by
    simpa using (Polynomial.dvd_iff_isRoot.mpr hp_root)
  obtain ⟨q, hq⟩ := hX_dvd
  obtain ⟨B, hB⟩ :=
    IsCompact.exists_bound_of_continuousOn
      (ProperSpace.isCompact_closedBall (0 : ℂ) 1)
      (q.continuous.continuousOn)
  refine ⟨max B 1, by positivity, ?_⟩
  intro z hz
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz
  have hqbound : ‖q.eval z‖ ≤ max B 1 := by
    exact le_trans (hB z hzmem) (le_max_left _ _)
  calc
    ‖padeQ n d z - 1‖ = ‖p.eval z‖ := by rw [hp_eval]
    _ = ‖(Polynomial.X * q).eval z‖ := by rw [hq]
    _ = ‖z * q.eval z‖ := by simp
    _ = ‖z‖ * ‖q.eval z‖ := norm_mul _ _
    _ ≤ ‖z‖ * max B 1 := by gcongr
    _ = max B 1 * ‖z‖ := by ring

/-- Local quantitative defect bound for the Padé numerator seam needed by the
order-star local cone arguments. -/
theorem numerator_local_bound
    (n d : ℕ) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧
      ∀ z : ℂ, ‖z‖ < δ →
        ‖padeP n d z * exp (-z) - padeQ n d z +
            (padePhiErrorConst n d : ℂ) * padeQ n d z * z ^ (n + d + 1)‖
          ≤ K * ‖z‖ ^ (n + d + 2) := by
  let m := n + d
  let coeff : ℂ := (1 / (((m + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)
  obtain ⟨KD, hKDpos, hD⟩ :
      ∃ KD : ℝ, 0 < KD ∧
        ∀ z : ℂ, ‖z‖ ≤ 1 →
          ‖padeP n d z - padeQ n d z * expTaylor m z - coeff * z ^ (m + 1)‖ ≤
            KD * ‖z‖ ^ (m + 2) := by
    dsimp [m, coeff]
    obtain ⟨g, hg⟩ := PadeAsymptotics.padeDefect_poly_sub_leading_X_pow_dvd n d
    obtain ⟨B, hB⟩ :=
      IsCompact.exists_bound_of_continuousOn
        (ProperSpace.isCompact_closedBall (0 : ℂ) 1)
        (g.continuous.continuousOn)
    refine ⟨max B 1, by positivity, ?_⟩
    intro z hz
    have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz
    have hgbound : ‖g.eval z‖ ≤ max B 1 := by
      exact le_trans (hB z hzmem) (le_max_left _ _)
    have hEval := congrArg (fun r : Polynomial ℂ => r.eval z) hg
    have hEq :
        padeP n d z - padeQ n d z * expTaylor (n + d) z -
            ((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
              z ^ (n + d + 1) =
          z ^ (n + d + 2) * g.eval z := by
      simpa [PadeAsymptotics.padeDefect_poly, PadeAsymptotics.padeP_poly_eval,
        PadeAsymptotics.padeQ_poly_eval, PadeAsymptotics.expTaylor_poly_eval,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X] using hEval
    rw [hEq, norm_mul, norm_pow]
    calc
      ‖z‖ ^ (n + d + 2) * ‖g.eval z‖ ≤ ‖z‖ ^ (n + d + 2) * max B 1 := by
        exact mul_le_mul_of_nonneg_left hgbound (pow_nonneg (norm_nonneg z) _)
      _ = max B 1 * ‖z‖ ^ (n + d + 2) := by ring
  obtain ⟨δE, KE, hδE, hKE, hE⟩ := expTaylor_exp_neg_local_norm_bound m
  obtain ⟨C, hCpos, hC⟩ := padeQ_sub_one_lipschitz n d
  refine ⟨Real.exp 1 * KD + (C + 1) * KE + ‖coeff‖ * (C + 2), min δE 1,
    by positivity, by positivity, ?_⟩
  intro z hz
  have hzE : ‖z‖ < δE := lt_of_lt_of_le hz (min_le_left _ _)
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
  have hz1' : ‖z‖ ≤ 1 := le_of_lt hz1
  have hQsub : ‖padeQ n d z - 1‖ ≤ C * ‖z‖ := hC z hz1'
  have hQbound : ‖padeQ n d z‖ ≤ C + 1 := by
    have hnorm : ‖padeQ n d z‖ ≤ ‖padeQ n d z - 1‖ + 1 := by
      have := norm_add_le (padeQ n d z - 1) (1 : ℂ)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have hCnn : 0 ≤ C := le_of_lt hCpos
    calc
      ‖padeQ n d z‖ ≤ ‖padeQ n d z - 1‖ + 1 := hnorm
      _ ≤ C * ‖z‖ + 1 := by gcongr
      _ ≤ C + 1 := by nlinarith
  have hExpNorm : ‖Complex.exp (-z)‖ ≤ Real.exp 1 := by
    calc
      ‖Complex.exp (-z)‖ ≤ Real.exp ‖-z‖ := Complex.norm_exp_le_exp_norm (-z)
      _ = Real.exp ‖z‖ := by simp
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hz1'
  have hDiff : ‖Complex.exp (-z) - padeQ n d z‖ ≤ (C + 2) * ‖z‖ := by
    have hExpSub : ‖Complex.exp (-z) - 1‖ ≤ 2 * ‖z‖ := by
      simpa [norm_neg] using
        (Complex.norm_exp_sub_one_le (x := -z) (by simpa [norm_neg] using hz1'))
    have hQsub' : ‖1 - padeQ n d z‖ ≤ C * ‖z‖ := by
      simpa [norm_sub_rev] using hQsub
    calc
      ‖Complex.exp (-z) - padeQ n d z‖ =
          ‖(Complex.exp (-z) - 1) + (1 - padeQ n d z)‖ := by ring_nf
      _ ≤ ‖Complex.exp (-z) - 1‖ + ‖1 - padeQ n d z‖ := norm_add_le _ _
      _ ≤ 2 * ‖z‖ + C * ‖z‖ := add_le_add hExpSub hQsub'
      _ = (C + 2) * ‖z‖ := by ring
  let defect : ℂ := padeP n d z - padeQ n d z * expTaylor m z - coeff * z ^ (m + 1)
  let tail : ℂ :=
    expTaylor m z * exp (-z) - (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1))
  have hsplit :
      padeP n d z * exp (-z) - padeQ n d z +
          (padePhiErrorConst n d : ℂ) * padeQ n d z * z ^ (m + 1) =
        defect * exp (-z) + padeQ n d z * tail +
          coeff * z ^ (m + 1) * (exp (-z) - padeQ n d z) := by
    simp [defect, tail, coeff, m]
    ring
  have hterm1 : ‖defect * exp (-z)‖ ≤ Real.exp 1 * KD * ‖z‖ ^ (m + 2) := by
    calc
      ‖defect * exp (-z)‖ = ‖defect‖ * ‖Complex.exp (-z)‖ := norm_mul _ _
      _ ≤ (KD * ‖z‖ ^ (m + 2)) * Real.exp 1 := by
        exact mul_le_mul (hD z hz1') hExpNorm (by positivity) (by positivity)
      _ = Real.exp 1 * KD * ‖z‖ ^ (m + 2) := by ring
  have hterm2 : ‖padeQ n d z * tail‖ ≤ (C + 1) * KE * ‖z‖ ^ (m + 2) := by
    calc
      ‖padeQ n d z * tail‖ = ‖padeQ n d z‖ * ‖tail‖ := norm_mul _ _
      _ ≤ (C + 1) * (KE * ‖z‖ ^ (m + 2)) := by
        exact mul_le_mul hQbound (hE z hzE) (by positivity) (by positivity)
      _ = (C + 1) * KE * ‖z‖ ^ (m + 2) := by ring
  have hterm3 :
      ‖coeff * z ^ (m + 1) * (exp (-z) - padeQ n d z)‖ ≤
        ‖coeff‖ * (C + 2) * ‖z‖ ^ (m + 2) := by
    have hpow_nonneg : 0 ≤ ‖z‖ ^ (m + 1) := by positivity
    have hcoeff_nonneg : 0 ≤ ‖coeff‖ := norm_nonneg _
    have hinner :
        ‖z‖ ^ (m + 1) * ‖exp (-z) - padeQ n d z‖ ≤
          ‖z‖ ^ (m + 1) * ((C + 2) * ‖z‖) :=
      mul_le_mul_of_nonneg_left hDiff hpow_nonneg
    calc
      ‖coeff * z ^ (m + 1) * (exp (-z) - padeQ n d z)‖ =
          ‖coeff‖ * (‖z‖ ^ (m + 1) * ‖exp (-z) - padeQ n d z‖) := by
            rw [norm_mul, norm_mul, norm_pow]
            simp [mul_assoc]
      _ ≤ ‖coeff‖ * (‖z‖ ^ (m + 1) * ((C + 2) * ‖z‖)) := by
        exact mul_le_mul_of_nonneg_left hinner hcoeff_nonneg
      _ = ‖coeff‖ * (C + 2) * ‖z‖ ^ (m + 2) := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ']
        ring
  rw [hsplit]
  calc
    ‖defect * exp (-z) + padeQ n d z * tail + coeff * z ^ (m + 1) * (exp (-z) - padeQ n d z)‖
      ≤ ‖defect * exp (-z)‖ + ‖padeQ n d z * tail‖ +
          ‖coeff * z ^ (m + 1) * (exp (-z) - padeQ n d z)‖ := by
            have h12 := norm_add_le (defect * exp (-z)) (padeQ n d z * tail)
            have h123 := norm_add_le (defect * exp (-z) + padeQ n d z * tail)
              (coeff * z ^ (m + 1) * (exp (-z) - padeQ n d z))
            linarith
    _ ≤ (Real.exp 1 * KD) * ‖z‖ ^ (m + 2) + ((C + 1) * KE) * ‖z‖ ^ (m + 2) +
          (‖coeff‖ * (C + 2)) * ‖z‖ ^ (m + 2) := by
            nlinarith [hterm1, hterm2, hterm3]
    _ = (Real.exp 1 * KD + (C + 1) * KE + ‖coeff‖ * (C + 2)) * ‖z‖ ^ (m + 2) := by
          ring

/-- Honest local asymptotic control for `padeR n d z * exp (-z)` near the
origin, with the explicit first neglected coefficient. -/
theorem padeR_exp_neg_local_bound
    (n d : ℕ) :
    ∃ K δ₀ : ℝ, 0 < K ∧ 0 < δ₀ ∧
      ∀ z : ℂ, ‖z‖ < δ₀ →
        ‖padeR n d z * exp (-z) -
            (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))‖
          ≤ K * ‖z‖ ^ (n + d + 2) := by
  obtain ⟨Knum, δnum, hKnum, hδnum, hnum⟩ := numerator_local_bound n d
  obtain ⟨δinv, hδinv, hinv⟩ := padeQ_inv_bound n d
  obtain ⟨δnz, hδnz, hnz⟩ := padeQ_ne_zero_nhds n d
  refine ⟨2 * Knum, min δnum (min δinv δnz), by positivity, by positivity, ?_⟩
  intro z hz
  have hznum : ‖z‖ < δnum := lt_of_lt_of_le hz (min_le_left _ _)
  have hzinv : ‖z‖ < δinv := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hznz : ‖z‖ < δnz := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
  have hqne : padeQ n d z ≠ 0 := hnz z hznz
  have hkey :
      padeR n d z * exp (-z) - (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) =
        (padeP n d z * exp (-z) - padeQ n d z +
            (padePhiErrorConst n d : ℂ) * padeQ n d z * z ^ (n + d + 1)) /
          padeQ n d z := by
    rw [padeR]
    field_simp [hqne]
    ring
  rw [hkey, norm_div, div_eq_mul_inv]
  calc
    ‖padeP n d z * exp (-z) - padeQ n d z +
        (padePhiErrorConst n d : ℂ) * padeQ n d z * z ^ (n + d + 1)‖ * ‖padeQ n d z‖⁻¹
      ≤ (Knum * ‖z‖ ^ (n + d + 2)) * ‖padeQ n d z‖⁻¹ := by
          gcongr
          exact hnum z hznum
    _ = (Knum * ‖z‖ ^ (n + d + 2)) * ‖(padeQ n d z)⁻¹‖ := by rw [norm_inv]
    _ ≤ (Knum * ‖z‖ ^ (n + d + 2)) * 2 := by
          gcongr
          exact hinv z hzinv
    _ = (2 * Knum) * ‖z‖ ^ (n + d + 2) := by ring
