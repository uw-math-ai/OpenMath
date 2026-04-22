import OpenMath.PadeOrderStars

open Complex

theorem cycle336_uniformRadiusPhaseStrip_oddDownArrow
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δ η : ℝ,
      0 < δ ∧
      0 < η ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) δ, ∀ s ∈ Set.Icc (-η) η,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + s) * I)
        0 < Complex.re (padeR n d w * exp (-w))) ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) δ,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) - η) * I)
        0 < Complex.im (padeR n d w * exp (-w))) ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) δ,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + η) * I)
        Complex.im (padeR n d w * exp (-w)) < 0) := by
  sorry
