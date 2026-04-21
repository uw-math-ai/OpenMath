import OpenMath.Pade

namespace Cycle301Aristotle03

open Complex

theorem expTaylor_exp_neg_local_norm_bound
    (m : ℕ) :
    ∃ δ₀ K : ℝ, 0 < δ₀ ∧ 0 < K ∧
      ∀ z : ℂ, ‖z‖ < δ₀ →
        ‖expTaylor m z * exp (-z) -
            (1 - (1 : ℂ) / (((m + 1).factorial : ℂ)) * z ^ (m + 1))‖ ≤
          K * ‖z‖ ^ (m + 2) := by
  sorry

end Cycle301Aristotle03
