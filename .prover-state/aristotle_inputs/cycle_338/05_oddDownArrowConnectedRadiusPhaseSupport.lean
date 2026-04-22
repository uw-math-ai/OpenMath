import OpenMath.PadeOrderStars

open Complex

theorem cycle338_oddDownArrowConnectedRadiusPhaseSupport
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δ > 0, ∃ support : Set ℂ,
      IsConnected support ∧
        support ⊆ orderWeb (padeR n d) ∧
        (0 : ℂ) ∈ support ∧
        ∀ r ∈ Set.Ioo (0 : ℝ) δ,
          ∃ z ∈ support, ∃ s ∈ Set.Icc (-r) r,
            z =
              (↑r : ℂ) *
                exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + s) * I) := by
  sorry
