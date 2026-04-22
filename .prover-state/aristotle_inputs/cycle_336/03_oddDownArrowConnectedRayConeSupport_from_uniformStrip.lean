import OpenMath.PadeOrderStars

open Complex

theorem cycle336_oddDownArrowConnectedRayConeSupport_from_uniformStrip
    {n d : ℕ} {δ η : ℝ}
    (hδ : 0 < δ)
    (hη : 0 < η)
    (hstrip_re :
      ∀ r ∈ Set.Ioo (0 : ℝ) δ, ∀ s ∈ Set.Icc (-η) η,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + s) * I)
        0 < Complex.re (padeR n d w * exp (-w)))
    (hleft_im :
      ∀ r ∈ Set.Ioo (0 : ℝ) δ,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) - η) * I)
        0 < Complex.im (padeR n d w * exp (-w)))
    (hright_im :
      ∀ r ∈ Set.Ioo (0 : ℝ) δ,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + η) * I)
        Complex.im (padeR n d w * exp (-w)) < 0) :
    Nonempty
      (PadeRConnectedRayConeOrderWebSupport n d
        (Real.pi / ((↑(n + d) + 1) : ℝ))) := by
  sorry
