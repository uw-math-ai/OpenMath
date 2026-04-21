import OpenMath.PadeOrderStars

open Complex

noncomputable section

theorem padeQ_nonzero_near_zero
    (n d : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ z : ℂ, ‖z‖ < δ₀ → padeQ n d z ≠ 0 := by
  sorry

theorem padeQ_inv_norm_le_two_near_zero
    (n d : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ z : ℂ, ‖z‖ < δ₀ → ‖(padeQ n d z)⁻¹‖ ≤ 2 := by
  sorry
