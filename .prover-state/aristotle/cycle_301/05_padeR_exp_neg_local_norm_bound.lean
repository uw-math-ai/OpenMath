import OpenMath.Pade

namespace Cycle301Aristotle05

open Complex

theorem padeR_exp_neg_local_norm_bound
    (n d : ℕ) :
    ∃ δ₀ K : ℝ, 0 < δ₀ ∧ 0 < K ∧
      ∀ z : ℂ, ‖z‖ < δ₀ →
        ‖padeR n d z * exp (-z) -
            (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))‖ ≤
          K * ‖z‖ ^ (n + d + 2) := by
  sorry

end Cycle301Aristotle05
