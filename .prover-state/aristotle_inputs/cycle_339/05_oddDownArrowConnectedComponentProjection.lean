import OpenMath.PadeOrderStars

open Complex

theorem cycle339_oddDownArrowConnectedComponentProjection
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δ > 0,
      let θ0 : ℝ := Real.pi / ((↑(n + d) + 1) : ℝ)
      let F : ℝ × ℝ → ℝ := fun p =>
        let w : ℂ := (↑p.1 : ℂ) * exp (↑(θ0 + p.2) * I)
        Complex.im (padeR n d w * exp (-w))
      let K : Set (ℝ × ℝ) :=
        {p : ℝ × ℝ |
          p.1 ∈ Set.Icc (0 : ℝ) δ ∧
            p.2 ∈ Set.Icc (-p.1) p.1 ∧
            F p = 0}
      Set.Icc (0 : ℝ) δ ⊆ Prod.fst '' connectedComponentIn K (0, 0) := by
  sorry
