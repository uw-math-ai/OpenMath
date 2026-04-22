import OpenMath.PadeOrderStars

open Complex

theorem cycle334_connectedRadiusPhaseZeroSet_of_bridgeWitnesses
    {n d : ℕ} {θ : ℝ}
    (hbridge : PadeROrderWebArcPhaseBridgeNearOrigin n d θ)
    {z0 z : ℂ}
    (hz0web : z0 ∈ orderWeb (padeR n d))
    (hz0cone : z0 ∈ rayConeNearOrigin θ (1 : ℝ) 1)
    (aperture radius : ℝ)
    (hzweb : z ∈ orderWeb (padeR n d))
    (hzcone : z ∈ rayConeNearOrigin θ aperture radius) :
    ∃ a b η s0 s1 : ℝ, ∃ Z : Set (ℝ × ℝ),
      a ≤ b ∧
      0 < η ∧
      s0 ∈ Set.Icc (-η) η ∧
      s1 ∈ Set.Icc (-η) η ∧
      z0 = ((↑a : ℂ) * exp (↑(θ + s0) * I)) ∧
      z = ((↑b : ℂ) * exp (↑(θ + s1) * I)) ∧
      IsConnected Z ∧
      Z ⊆ {p : ℝ × ℝ |
        p.1 ∈ Set.Icc a b ∧
        p.2 ∈ Set.Icc (-η) η ∧
        let w : ℂ := (↑p.1 : ℂ) * exp (↑(θ + p.2) * I)
        Complex.im (padeR n d w * exp (-w)) = 0 ∧
        0 < Complex.re (padeR n d w * exp (-w))} ∧
      (a, s0) ∈ Z ∧
      (b, s1) ∈ Z ∧
      Set.Icc a b ⊆ Prod.fst '' Z := by
  sorry
