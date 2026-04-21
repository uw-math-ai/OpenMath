import OpenMath.OrderStars

namespace OpenMath

theorem cycle271_noArrowsEscapeToInfinity_of_rationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (h_approx : IsRationalApproxToExp data)
    (hdown : DownArrowInfinityWitnesses R data)
    (hup : UpArrowInfinityWitnesses R data) :
    NoArrowsEscapeToInfinity data := by
  sorry

end OpenMath
