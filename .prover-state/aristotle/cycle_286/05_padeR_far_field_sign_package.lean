import OpenMath.Pade
import OpenMath.OrderStars

open Complex Set Real

theorem cycle286_padeR_far_field_sign_package
    (n d : ℕ) :
    (∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
      1 < ‖padeR n d z * exp (-z)‖) ∧
    (∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
      ‖padeR n d z * exp (-z)‖ < 1) := by
  sorry
