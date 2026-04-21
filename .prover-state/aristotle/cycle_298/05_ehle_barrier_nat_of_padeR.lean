import OpenMath.PadeOrderStars

open Complex

theorem cycle298_ehle_barrier_nat_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hA : IsAStablePadeApprox data) :
    InEhleWedge n d := by
  sorry
