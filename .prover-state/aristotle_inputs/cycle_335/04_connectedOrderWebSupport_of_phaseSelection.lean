import OpenMath.PadeOrderStars

open Complex

theorem cycle335_connectedOrderWebSupport_of_phaseSelection
    {n d : ℕ} {θ a b η : ℝ}
    (hab : a ≤ b)
    (σ : ℝ → ℝ)
    (hσcont : ContinuousOn σ (Set.Icc a b))
    (hσmem : ∀ r ∈ Set.Icc a b, σ r ∈ Set.Icc (-η) η)
    (hσzero :
      ∀ r ∈ Set.Icc a b,
        let w : ℂ := (↑r : ℂ) * exp (↑(θ + σ r) * I)
        Complex.im (padeR n d w * exp (-w)) = 0)
    (hσre :
      ∀ r ∈ Set.Icc a b,
        let w : ℂ := (↑r : ℂ) * exp (↑(θ + σ r) * I)
        0 < Complex.re (padeR n d w * exp (-w))) :
    ∃ support : Set ℂ,
      IsConnected support ∧
      support ⊆ orderWeb (padeR n d) ∧
      (((↑a : ℂ) * exp (↑(θ + σ a) * I)) ∈ support) ∧
      (((↑b : ℂ) * exp (↑(θ + σ b) * I)) ∈ support) := by
  sorry
