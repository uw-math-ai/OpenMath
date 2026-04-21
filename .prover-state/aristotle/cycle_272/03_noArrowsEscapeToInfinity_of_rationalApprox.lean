import OpenMath.OrderStars

namespace OpenMath

theorem cycle272_noArrowsEscapeToInfinity_of_rationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (h_approx : IsRationalApproxToExp data)
    (hreal : RealizesInfinityCounts R data) :
    NoArrowsEscapeToInfinity data := by
  sorry

end OpenMath
