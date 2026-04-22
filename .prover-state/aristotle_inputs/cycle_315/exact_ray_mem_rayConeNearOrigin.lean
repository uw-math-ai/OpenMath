import OpenMath.PadeOrderStars

open Complex

namespace Cycle315Aristotle

theorem exact_ray_mem_rayConeNearOrigin (θ aperture radius t : ℝ)
    (haperture : 0 < aperture) (ht : t ∈ Set.Ioo (0 : ℝ) radius) :
    ((↑t : ℂ) * exp (↑θ * I)) ∈ rayConeNearOrigin θ aperture radius := by
  sorry

end Cycle315Aristotle
