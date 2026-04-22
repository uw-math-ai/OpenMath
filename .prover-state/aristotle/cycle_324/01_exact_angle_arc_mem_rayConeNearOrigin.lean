import OpenMath.PadeOrderStars

open Complex

namespace Cycle324Aristotle

theorem exact_angle_arc_mem_rayConeNearOrigin
    (θ aperture radius : ℝ)
    (haperture : 0 < aperture) (hradius : 0 < radius) :
    ∃ t ∈ Set.Ioo (0 : ℝ) radius, ∃ η > 0,
      ∀ s ∈ Set.Icc (-η) η,
        ((↑t : ℂ) * exp (↑(θ + s) * I)) ∈ rayConeNearOrigin θ aperture radius := by
  sorry

end Cycle324Aristotle
