import OpenMath.LMMAB3Convergence

namespace LMM

theorem cycle419_ab3Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max
          ‖ab3IterVec h f t₀ y₀ y₁ y₂ (n + 1)
              - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖ab3IterVec h f t₀ y₀ y₁ y₂ (n + 2)
              - y (t₀ + ((n : ℝ) + 2) * h)‖)
        ‖ab3IterVec h f t₀ y₀ y₁ y₂ (n + 3)
            - y (t₀ + ((n : ℝ) + 3) * h)‖
      ≤ (1 + h * ((11 / 3) * L))
            * max (max
                  ‖ab3IterVec h f t₀ y₀ y₁ y₂ n
                      - y (t₀ + (n : ℝ) * h)‖
                  ‖ab3IterVec h f t₀ y₀ y₁ y₂ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖ab3IterVec h f t₀ y₀ y₁ y₂ (n + 2)
                    - y (t₀ + ((n : ℝ) + 2) * h)‖
        + ‖ab3VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  sorry

end LMM
