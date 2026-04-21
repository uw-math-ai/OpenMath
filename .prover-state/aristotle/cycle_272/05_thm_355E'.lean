import OpenMath.OrderStars

namespace OpenMath

theorem cycle272_thm_355E'
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (h_pade : IsPadeApproxToExp data)
    (hreal : RealizesInfinityCounts R data) :
    data.downArrowsAtZeros = data.numeratorDegree ∧
    data.upArrowsAtPoles = data.denominatorDegree := by
  sorry

end OpenMath
