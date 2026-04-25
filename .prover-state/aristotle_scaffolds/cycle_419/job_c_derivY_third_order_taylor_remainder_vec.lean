import OpenMath.LMMAB3Convergence

namespace LMM

theorem cycle419_derivY_third_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 4 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖deriv y (t + r) - deriv y t - r • iteratedDeriv 2 y t
        - (r ^ 2 / 2) • iteratedDeriv 3 y t‖
      ≤ M / 6 * r ^ 3 := by
  sorry

end LMM
