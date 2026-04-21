import OpenMath.PadeOrderStars

open Complex

theorem cycle298_padeREhleBarrierNatInput_of_padeR_aStable
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hA : IsAStablePadeApprox data) :
    PadeREhleBarrierNatInput n d data := by
  sorry
