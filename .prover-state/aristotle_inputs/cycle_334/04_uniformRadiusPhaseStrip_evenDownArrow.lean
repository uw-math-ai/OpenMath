import OpenMath.PadeOrderStars

open Complex

theorem cycle334_uniformRadiusPhaseStrip_evenDownArrow
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ δ η : ℝ,
      0 < δ ∧
      0 < η ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) δ, ∀ s ∈ Set.Icc (-η) η,
        let w : ℂ := (↑r : ℂ) * exp (↑s * I)
        0 < Complex.re (padeR n d w * exp (-w))) ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) δ,
        let w : ℂ := (↑r : ℂ) * exp (↑(-η) * I)
        0 < Complex.im (padeR n d w * exp (-w))) ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) δ,
        let w : ℂ := (↑r : ℂ) * exp (↑η * I)
        Complex.im (padeR n d w * exp (-w)) < 0) := by
  sorry
