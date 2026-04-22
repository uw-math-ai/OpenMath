import OpenMath.PadeOrderStars

open Complex

theorem cycle335_phaseSelection_of_connectedRadiusPhaseZeroSet
    {n d : ℕ} {θ a b η s0 s1 : ℝ} {z0 z : ℂ} {Z : Set (ℝ × ℝ)}
    (hab : a ≤ b)
    (hη : 0 < η)
    (hs0 : s0 ∈ Set.Icc (-η) η)
    (hs1 : s1 ∈ Set.Icc (-η) η)
    (hz0 : z0 = ((↑a : ℂ) * exp (↑(θ + s0) * I)))
    (hz : z = ((↑b : ℂ) * exp (↑(θ + s1) * I)))
    (hZconn : IsConnected Z)
    (hZsubset :
      Z ⊆ {p : ℝ × ℝ |
        p.1 ∈ Set.Icc a b ∧
        p.2 ∈ Set.Icc (-η) η ∧
        let w : ℂ := (↑p.1 : ℂ) * exp (↑(θ + p.2) * I)
        Complex.im (padeR n d w * exp (-w)) = 0 ∧
        0 < Complex.re (padeR n d w * exp (-w))})
    (hZ0 : (a, s0) ∈ Z)
    (hZ1 : (b, s1) ∈ Z)
    (hproj : Set.Icc a b ⊆ Prod.fst '' Z) :
    ∃ σ : ℝ → ℝ,
      ContinuousOn σ (Set.Icc a b) ∧
      (∀ r ∈ Set.Icc a b, σ r ∈ Set.Icc (-η) η) ∧
      (∀ r ∈ Set.Icc a b,
        let w : ℂ := (↑r : ℂ) * exp (↑(θ + σ r) * I)
        Complex.im (padeR n d w * exp (-w)) = 0) ∧
      (∀ r ∈ Set.Icc a b,
        let w : ℂ := (↑r : ℂ) * exp (↑(θ + σ r) * I)
        0 < Complex.re (padeR n d w * exp (-w))) ∧
      z0 = ((↑a : ℂ) * exp (↑(θ + σ a) * I)) ∧
      z = ((↑b : ℂ) * exp (↑(θ + σ b) * I)) := by
  sorry
