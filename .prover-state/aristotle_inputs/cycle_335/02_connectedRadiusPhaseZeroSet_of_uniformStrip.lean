import OpenMath.PadeOrderStars

open Complex

theorem cycle335_connectedRadiusPhaseZeroSet_of_uniformStrip
    {n d : ℕ} {θ a b η : ℝ}
    (hab : a ≤ b)
    (hη : 0 < η)
    (hstrip_re :
      ∀ r ∈ Set.Icc a b, ∀ s ∈ Set.Icc (-η) η,
        let w : ℂ := (↑r : ℂ) * exp (↑(θ + s) * I)
        0 < Complex.re (padeR n d w * exp (-w)))
    (hleft_im :
      ∀ r ∈ Set.Icc a b,
        let w : ℂ := (↑r : ℂ) * exp (↑(θ - η) * I)
        0 < Complex.im (padeR n d w * exp (-w)))
    (hright_im :
      ∀ r ∈ Set.Icc a b,
        let w : ℂ := (↑r : ℂ) * exp (↑(θ + η) * I)
        Complex.im (padeR n d w * exp (-w)) < 0) :
    ∃ Z : Set (ℝ × ℝ),
      IsConnected Z ∧
      Z ⊆ {p : ℝ × ℝ |
        p.1 ∈ Set.Icc a b ∧
        p.2 ∈ Set.Icc (-η) η ∧
        let w : ℂ := (↑p.1 : ℂ) * exp (↑(θ + p.2) * I)
        Complex.im (padeR n d w * exp (-w)) = 0 ∧
        0 < Complex.re (padeR n d w * exp (-w))} ∧
      Set.Icc a b ⊆ Prod.fst '' Z := by
  sorry
