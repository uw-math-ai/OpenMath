import OpenMath.PadeOrderStars

open Complex

namespace Cycle324Aristotle

theorem padeR_even_downArrowArc_endpointSigns
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∀ radius > 0,
      ∃ t ∈ Set.Ioo (0 : ℝ) radius, ∃ η > 0,
        0 < Complex.im
          (padeR n d (((↑t : ℂ) * exp (↑(-η) * I))) *
            exp (-(((↑t : ℂ) * exp (↑(-η) * I))))) ∧
        Complex.im
          (padeR n d (((↑t : ℂ) * exp (↑η * I))) *
            exp (-(((↑t : ℂ) * exp (↑η * I))))) < 0 := by
  sorry

end Cycle324Aristotle
