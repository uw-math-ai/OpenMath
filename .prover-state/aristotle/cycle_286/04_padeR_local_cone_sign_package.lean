import OpenMath.Pade
import OpenMath.OrderStars

open Complex Set Real

theorem cycle286_padeR_local_cone_sign_package
    (n d : ℕ) :
    (∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
      ∃ aperture > 0, ∃ radius > 0,
        ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
          ‖padeR n d z * exp (-z)‖ < 1) ∧
    (∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
      ∃ aperture > 0, ∃ radius > 0,
        ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
          1 < ‖padeR n d z * exp (-z)‖) := by
  sorry
