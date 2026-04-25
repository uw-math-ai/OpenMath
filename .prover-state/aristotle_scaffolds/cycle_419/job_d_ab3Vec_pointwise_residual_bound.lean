import OpenMath.LMMAB3Convergence

namespace LMM

theorem cycle419_ab3Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 4 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 3 * h) - y (t + 2 * h)
        - h • ((23 / 12 : ℝ) • deriv y (t + 2 * h)
              - (16 / 12 : ℝ) • deriv y (t + h)
              + (5 / 12 : ℝ) • deriv y t)‖
      ≤ (7 : ℝ) * M * h ^ 4 := by
  sorry

end LMM
