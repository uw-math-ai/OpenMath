import OpenMath.Pade
import OpenMath.OrderStars

open Complex

abbrev Cycle292PadeRRealizedUpArrowInfinityWitnessFamily
    (n d : ℕ) (data : OrderArrowTerminationData) :=
  ∀ _ : Fin data.upArrowsAtInfinity,
    RealizedUpArrowInfinityBranch (padeR n d)

def cycle292_realizedUpArrowInfinityWitnessFamily_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hpade : IsPadeApproxToExp data) :
    Cycle292PadeRRealizedUpArrowInfinityWitnessFamily n d data := by
  sorry
