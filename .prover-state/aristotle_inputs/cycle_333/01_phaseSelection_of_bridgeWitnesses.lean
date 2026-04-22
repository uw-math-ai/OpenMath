import OpenMath.PadeOrderStars

open Complex

theorem cycle333_phaseSelection_of_bridgeWitnesses
    {n d : ℕ} {θ : ℝ}
    (hbridge : PadeROrderWebArcPhaseBridgeNearOrigin n d θ)
    {z0 z : ℂ}
    (hz0web : z0 ∈ orderWeb (padeR n d))
    (hz0cone : z0 ∈ rayConeNearOrigin θ (1 : ℝ) 1)
    (aperture radius : ℝ)
    (hzweb : z ∈ orderWeb (padeR n d))
    (hzcone : z ∈ rayConeNearOrigin θ aperture radius) :
    ∃ a b η : ℝ, ∃ σ : ℝ → ℝ,
      a ≤ b ∧
      0 < η ∧
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
