import OpenMath.PadeOrderStars

open Complex

theorem cycle338_oddDownArrowSameComponentRadiusPhaseBound_atZero
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δ > 0,
      ∀ r ∈ Set.Ioo (0 : ℝ) δ,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) (0 : ℂ) ∧
            ∃ s ∈ Set.Icc (-r) r,
              z =
                (↑r : ℂ) *
                  exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + s) * I) := by
  sorry
