import OpenMath.Pade
import OpenMath.OrderStars

open Complex Set Real

theorem cycle286_padeR_no_nonzero_eq_exp_on_orderWeb
    (n d : ℕ) :
    ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
      padeR n d z = exp z → False := by
  sorry
