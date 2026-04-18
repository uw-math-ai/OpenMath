import OpenMath.Pade

/-!
# Padé Uniqueness (Theorem 352B)

The (l,m)-Padé approximant to exp is **unique**: if P̃/Q̃ also satisfies the
Padé approximation condition to order l+m, then P̃ · Q_{l,m} = P_{l,m} · Q̃
as polynomials.

## Structure

1. `Polynomial ℂ` versions of `expTaylor`, `padeP`, `padeQ`
2. Vanishing lemma: degree ≤ n ∧ X^{n+1} ∣ p ⟹ p = 0
3. Padé approximation order in polynomial divisibility form
4. Uniqueness theorem (352B)

Reference: Iserles, *A First Course in the Numerical Analysis of Differential
Equations*, Theorem 352B (p. 258).
-/

open Finset Complex Polynomial
open scoped BigOperators

/-! ## Polynomial Versions of Padé Functions -/

/-- The n-th Taylor polynomial of exp as a formal polynomial. -/
noncomputable def expTaylor_poly (n : ℕ) : Polynomial ℂ :=
  ∑ i in Finset.range (n + 1),
    Polynomial.C (1 / (i.factorial : ℂ)) * Polynomial.X ^ i

/-- The Padé numerator P_{p,q} as a formal polynomial. -/
noncomputable def padeP_poly (p q : ℕ) : Polynomial ℂ :=
  ∑ j in Finset.range (p + 1),
    Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (p.factorial : ℂ) /
      (((p + q).factorial : ℂ) * ((p - j).factorial : ℂ) * (j.factorial : ℂ))) *
    Polynomial.X ^ j

/-- The Padé denominator Q_{p,q} as a formal polynomial. The (-1)^j factor
    absorbs the `(-z)^j` from the function-level definition. -/
noncomputable def padeQ_poly (p q : ℕ) : Polynomial ℂ :=
  ∑ j in Finset.range (q + 1),
    Polynomial.C ((((p + q - j).factorial : ℕ) : ℂ) * (q.factorial : ℂ) /
      (((p + q).factorial : ℂ) * ((q - j).factorial : ℂ) * (j.factorial : ℂ)) *
      (-1) ^ j) *
    Polynomial.X ^ j

/-! ## Evaluation Lemmas -/

/-- The polynomial `expTaylor_poly` evaluates to the function `expTaylor`. -/
theorem expTaylor_poly_eval (n : ℕ) (z : ℂ) :
    (expTaylor_poly n).eval z = expTaylor n z := by
  simp only [expTaylor_poly, expTaylor, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  congr 1; ext i; ring

/-- The polynomial `padeP_poly` evaluates to the function `padeP`. -/
theorem padeP_poly_eval (p q : ℕ) (z : ℂ) :
    (padeP_poly p q).eval z = padeP p q z := by
  simp only [padeP_poly, padeP, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  congr 1; ext j; ring

/-- The polynomial `padeQ_poly` evaluates to the function `padeQ`. -/
theorem padeQ_poly_eval (p q : ℕ) (z : ℂ) :
    (padeQ_poly p q).eval z = padeQ p q z := by
  simp only [padeQ_poly, padeQ, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  congr 1; ext j
  simp only [neg_mul, one_mul, mul_comm ((-1 : ℂ) ^ j) (z ^ j), ← mul_pow]
  ring

/-! ## Degree Bounds -/

private theorem natDegree_C_mul_X_pow_le' (c : ℂ) (j : ℕ) :
    (Polynomial.C c * Polynomial.X ^ j).natDegree ≤ j := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [Polynomial.natDegree_C_mul_X_pow _ _ hc]

/-- The Taylor polynomial has formal degree ≤ n. -/
theorem expTaylor_poly_natDegree_le (n : ℕ) :
    (expTaylor_poly n).natDegree ≤ n := by
  unfold expTaylor_poly
  calc (∑ i in Finset.range (n + 1), _).natDegree
      ≤ (Finset.range (n + 1)).sup (fun i => (Polynomial.C _ * Polynomial.X ^ i).natDegree) :=
          Polynomial.natDegree_sum_le _ _
    _ ≤ n := Finset.sup_le (fun i hi =>
        le_trans (natDegree_C_mul_X_pow_le' _ _) (by omega))

/-- The Padé numerator polynomial has formal degree ≤ p. -/
theorem padeP_poly_natDegree_le (p q : ℕ) :
    (padeP_poly p q).natDegree ≤ p := by
  unfold padeP_poly
  calc (∑ j in Finset.range (p + 1), _).natDegree
      ≤ (Finset.range (p + 1)).sup (fun j => (Polynomial.C _ * Polynomial.X ^ j).natDegree) :=
          Polynomial.natDegree_sum_le _ _
    _ ≤ p := Finset.sup_le (fun j hj =>
        le_trans (natDegree_C_mul_X_pow_le' _ _) (by omega))

/-- The Padé denominator polynomial has formal degree ≤ q. -/
theorem padeQ_poly_natDegree_le (p q : ℕ) :
    (padeQ_poly p q).natDegree ≤ q := by
  unfold padeQ_poly
  calc (∑ j in Finset.range (q + 1), _).natDegree
      ≤ (Finset.range (q + 1)).sup (fun j => (Polynomial.C _ * Polynomial.X ^ j).natDegree) :=
          Polynomial.natDegree_sum_le _ _
    _ ≤ q := Finset.sup_le (fun j hj =>
        le_trans (natDegree_C_mul_X_pow_le' _ _) (by omega))

/-! ## Vanishing Lemma -/

/-- A polynomial of degree ≤ n that is divisible by X^{n+1} must be zero.
This is the key algebraic fact for the uniqueness proof. -/
theorem poly_eq_zero_of_X_pow_dvd (p : Polynomial ℂ) (n : ℕ)
    (hdeg : p.natDegree ≤ n)
    (hdvd : Polynomial.X ^ (n + 1) ∣ p) : p = 0 := by
  by_contra hp
  have h1 : (Polynomial.X ^ (n + 1) : Polynomial ℂ).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hp
  rw [Polynomial.natDegree_X_pow] at h1
  omega

/-! ## Padé Approximation Order (Polynomial Divisibility Form)

This is the polynomial-level strengthening of `pade_approximation_order`.
It says X^{p+q+1} divides the defect polynomial P_{p,q} - Q_{p,q} · T_{p+q}
in the polynomial ring ℂ[X].

The proof requires showing that each coefficient of the defect below degree p+q+1
vanishes. This follows from the combinatorial Vandermonde-type identity:
  C(p, i) = ∑_{j=0}^{min(i,q)} (-1)^j · C(q, j) · C(p+q-j, i-j)
for all i ≤ p+q, which is provable by induction on q. -/

theorem pade_approximation_order_poly (p q : ℕ) :
    Polynomial.X ^ (p + q + 1) ∣
      (padeP_poly p q - padeQ_poly p q * expTaylor_poly (p + q)) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have hcoeff :
      (padeP_poly p q).coeff d =
        (padeQ_poly p q * expTaylor_poly (p + q)).coeff d := by
    let S : Polynomial ℂ :=
      ∑ j in Finset.range (q + 1),
        Polynomial.C (q.choose j : ℂ) * (-Polynomial.X) ^ j * (Polynomial.X + 1) ^ (p + q - j)
    have hP :
        (padeP_poly p q).coeff d =
          ((((p + q - d).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) *
            (((Polynomial.X + 1 : Polynomial ℂ) ^ p).coeff d) := by
      by_cases hd' : d ≤ p
      · simp [padeP_poly, Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow, hd',
          show d < p + 1 by omega, add_pow]
        field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne',
          Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne']
        ring
      · have hdp : ¬ d < p + 1 := by omega
        have hchoose : (((Polynomial.X + 1 : Polynomial ℂ) ^ p).coeff d) = 0 := by
          simp [hd']
        simp [padeP_poly, Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow, hd', hdp, hchoose]
    have hQ :
        (padeQ_poly p q * expTaylor_poly (p + q)).coeff d =
          ((((p + q - d).factorial : ℕ) : ℂ) / (((p + q).factorial : ℂ))) * S.coeff d := by
      simp [S, padeQ_poly, expTaylor_poly, Polynomial.coeff_mul,
        Nat.sum_antidiagonal_eq_sum_range_succ, Polynomial.coeff_sum,
        Polynomial.coeff_C_mul_X_pow, add_pow, Finset.mul_sum]
    have hS : S = (Polynomial.X + 1 : Polynomial ℂ) ^ p := by
      unfold S
      rw [← Finset.sum_mul]
      conv_lhs =>
        congr
        skip
        ext j
        rw [← mul_assoc, ← pow_add, add_tsub_cancel_left]
      rw [← add_pow]
      simp
    rw [hP, hQ, hS]
  rw [Polynomial.coeff_sub]
  exact sub_eq_zero.mpr hcoeff

/-! ## Uniqueness Theorem (352B) -/

/-- **Theorem 352B**: Uniqueness of the (l,m) Padé approximation.

If P and Q are polynomials of degrees ≤ l and ≤ m respectively, with Q(0) = 1,
and the defect P - Q · T_{l+m} vanishes to polynomial order l+m+1 (i.e.,
X^{l+m+1} divides it), then P · Q_{l,m} = P_{l,m} · Q.

Equivalently, the rational function P/Q equals P_{l,m}/Q_{l,m} (as functions
wherever both denominators are nonzero). -/
theorem pade_uniqueness (l m : ℕ)
    (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ l) (hQ : Q.natDegree ≤ m)
    (hQ0 : Q.eval 0 = 1)
    (happrox : Polynomial.X ^ (l + m + 1) ∣ (P - Q * expTaylor_poly (l + m))) :
    P * padeQ_poly l m = padeP_poly l m * Q := by
  set N := l + m + 1
  set T := expTaylor_poly (l + m)
  set D₁ := P - Q * T
  set D₂ := padeP_poly l m - padeQ_poly l m * T
  -- H = P * padeQ_poly - padeP_poly * Q = D₁ * padeQ_poly - D₂ * Q
  have hH : P * padeQ_poly l m - padeP_poly l m * Q =
      D₁ * padeQ_poly l m - D₂ * Q := by ring
  -- Degree bound: natDegree H ≤ l + m
  have hdeg_H : (P * padeQ_poly l m - padeP_poly l m * Q).natDegree ≤ l + m :=
    calc (P * padeQ_poly l m - padeP_poly l m * Q).natDegree
        ≤ max (P * padeQ_poly l m).natDegree (padeP_poly l m * Q).natDegree :=
            Polynomial.natDegree_sub_le _ _
      _ ≤ max (P.natDegree + (padeQ_poly l m).natDegree)
              ((padeP_poly l m).natDegree + Q.natDegree) :=
            max_le_max Polynomial.natDegree_mul_le Polynomial.natDegree_mul_le
      _ ≤ max (l + m) (l + m) :=
            max_le_max (Nat.add_le_add hP (padeQ_poly_natDegree_le l m))
              (Nat.add_le_add (padeP_poly_natDegree_le l m) hQ)
      _ = l + m := max_self _
  -- Divisibility: X^N | H
  have hdvd_H : Polynomial.X ^ N ∣ (P * padeQ_poly l m - padeP_poly l m * Q) := by
    rw [hH]
    exact dvd_sub (dvd_mul_of_dvd_left happrox _)
      (dvd_mul_of_dvd_left (pade_approximation_order_poly l m) _)
  -- Apply vanishing lemma
  exact sub_eq_zero.mp (poly_eq_zero_of_X_pow_dvd _ (l + m) hdeg_H hdvd_H)

/-- **Corollary**: Uniqueness at the function level. If P̃ and Q̃ are polynomials
satisfying the Padé condition, then P̃ · Q_{l,m} = P_{l,m} · Q̃ pointwise. -/
theorem pade_uniqueness_fun (l m : ℕ)
    (P Q : Polynomial ℂ)
    (hP : P.natDegree ≤ l) (hQ : Q.natDegree ≤ m)
    (hQ0 : Q.eval 0 = 1)
    (happrox : Polynomial.X ^ (l + m + 1) ∣ (P - Q * expTaylor_poly (l + m))) :
    ∀ z, P.eval z * padeQ l m z = padeP l m z * Q.eval z := by
  intro z
  have h := congr_arg (Polynomial.eval z) (pade_uniqueness l m P Q hP hQ hQ0 happrox)
  simp only [Polynomial.eval_mul, padeP_poly_eval, padeQ_poly_eval] at h
  exact h
