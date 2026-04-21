import OpenMath.OrderStars

namespace OpenMath

theorem cycle272_noUpArrowEscapesToInfinity_of_rationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (h_approx : IsRationalApproxToExp data)
    (hreal : RealizesInfinityCounts R data) :
    data.upArrowsAtInfinity = 0 := by
  sorry

end OpenMath
