import OpenMath.PadeUniqueness

open Polynomial

theorem cycle109_pade_order_poly (p q : ℕ) :
    Polynomial.X ^ (p + q + 1) ∣
      (padeP_poly p q - padeQ_poly p q * expTaylor_poly (p + q)) := by
  simpa using pade_approximation_order_poly p q
