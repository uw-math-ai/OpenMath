import OpenMath.PadeUniqueness

open Polynomial

theorem cycle109_pade_order_coeff (p q d : ℕ) (hd : d < p + q + 1) :
    (padeP_poly p q).coeff d =
      (padeQ_poly p q * expTaylor_poly (p + q)).coeff d := by
  have hdiv := pade_approximation_order_poly p q
  rw [Polynomial.X_pow_dvd_iff] at hdiv
  exact by
    have := hdiv d hd
    rw [Polynomial.coeff_sub] at this
    exact sub_eq_zero.mp this
