import OpenMath.PadeOrderStars

open Complex

theorem cycle335_oddDownArrowSameComponentContinuation
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ z0 ∈ orderWeb (padeR n d),
      ∀ aperture > 0, ∀ radius > 0,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) z0 ∧
            z ∈ rayConeNearOrigin
              (Real.pi / ((↑(n + d) + 1) : ℝ)) aperture radius := by
  sorry
