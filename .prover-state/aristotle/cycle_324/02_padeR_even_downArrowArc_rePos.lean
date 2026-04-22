import OpenMath.PadeOrderStars

open Complex

namespace Cycle324Aristotle

theorem padeR_even_downArrowArc_rePos
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∀ aperture > 0, ∀ radius > 0,
      ∃ t ∈ Set.Ioo (0 : ℝ) radius, ∃ η > 0,
        ∀ s ∈ Set.Icc (-η) η,
          0 < Complex.re
            (padeR n d (((↑t : ℂ) * exp (↑s * I))) *
              exp (-(((↑t : ℂ) * exp (↑s * I))))) := by
  sorry

end Cycle324Aristotle
