import OpenMath.OrderStars

namespace OpenMath

theorem cycle272_noDownArrowEscapesToInfinity_of_rationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (h_approx : IsRationalApproxToExp data)
    (hreal : RealizesInfinityCounts R data) :
    data.downArrowsAtInfinity = 0 := by
  sorry

end OpenMath
