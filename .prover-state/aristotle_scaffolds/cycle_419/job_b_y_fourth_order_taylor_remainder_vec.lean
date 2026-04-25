import OpenMath.LMMAB3Convergence

namespace LMM

theorem cycle419_y_fourth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 4 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖y (t + r) - y t - r • deriv y t
        - (r ^ 2 / 2) • iteratedDeriv 2 y t
        - (r ^ 3 / 6) • iteratedDeriv 3 y t‖
      ≤ M / 24 * r ^ 4 := by
  sorry

end LMM
