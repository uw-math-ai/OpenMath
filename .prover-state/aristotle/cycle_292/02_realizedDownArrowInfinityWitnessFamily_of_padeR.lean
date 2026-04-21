import OpenMath.Pade
import OpenMath.OrderStars

open Complex

abbrev Cycle292PadeRRealizedDownArrowInfinityWitnessFamily
    (n d : ℕ) (data : OrderArrowTerminationData) :=
  ∀ _ : Fin data.downArrowsAtInfinity,
    RealizedDownArrowInfinityBranch (padeR n d)

def cycle292_realizedDownArrowInfinityWitnessFamily_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hpade : IsPadeApproxToExp data) :
    Cycle292PadeRRealizedDownArrowInfinityWitnessFamily n d data := by
  sorry
