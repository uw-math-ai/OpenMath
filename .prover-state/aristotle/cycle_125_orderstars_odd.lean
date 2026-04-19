import OpenMath.OrderStars

open Complex Set Real

namespace OpenMath
namespace AristotleScratch

theorem pow_ray_odd_angle_scratch (t : ℝ) (p k : ℕ) :
    ((↑t : ℂ) * exp (↑((2 * ↑k + 1) * π / (↑p + 1)) * I)) ^ (p + 1) =
      ↑(-(t ^ (p + 1))) := by
  sorry

theorem arrow_down_of_neg_errorConst_odd_scratch (R : ℂ → ℂ) (p : ℕ) (C K δ₀ : ℝ)
    (hC : C < 0) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2))
    (k : ℕ) :
    IsDownArrowDir R ((2 * ↑k + 1) * π / (↑p + 1)) := by
  sorry

theorem arrow_up_of_pos_errorConst_odd_scratch (R : ℂ → ℂ) (p : ℕ) (C K δ₀ : ℝ)
    (hC : 0 < C) (hK : 0 < K) (hδ : 0 < δ₀)
    (hφ : ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖R z * exp (-z) - (1 - ↑C * z ^ (p + 1))‖ ≤ K * ‖z‖ ^ (p + 2))
    (k : ℕ) :
    IsUpArrowDir R ((2 * ↑k + 1) * π / (↑p + 1)) := by
  sorry

end AristotleScratch
end OpenMath
