import OpenMath.PadeOrderStars

open Complex

theorem cycle336_oddDownArrowConnectedRadiusPhaseZeroSet
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δ η : ℝ,
      0 < δ ∧
      0 < η ∧
      ∃ Z : Set (ℝ × ℝ),
        IsConnected Z ∧
        Z ⊆ {p : ℝ × ℝ |
          p.1 ∈ Set.Icc (0 : ℝ) δ ∧
          p.2 ∈ Set.Icc (-η) η ∧
          let w : ℂ :=
            (↑p.1 : ℂ) *
              exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + p.2) * I)
          Complex.im (padeR n d w * exp (-w)) = 0 ∧
          0 < Complex.re (padeR n d w * exp (-w))} ∧
        Set.Icc (0 : ℝ) δ ⊆ Prod.fst '' Z := by
  sorry
