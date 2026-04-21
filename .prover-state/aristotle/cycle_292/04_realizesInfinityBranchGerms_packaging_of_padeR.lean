import OpenMath.Pade
import OpenMath.OrderStars

open Complex

abbrev Cycle292PadeRRealizedDownArrowInfinityWitnessFamily
    (n d : ℕ) (data : OrderArrowTerminationData) :=
  ∀ _ : Fin data.downArrowsAtInfinity,
    RealizedDownArrowInfinityBranch (padeR n d)

abbrev Cycle292PadeRRealizedUpArrowInfinityWitnessFamily
    (n d : ℕ) (data : OrderArrowTerminationData) :=
  ∀ _ : Fin data.upArrowsAtInfinity,
    RealizedUpArrowInfinityBranch (padeR n d)

def cycle292_realizesInfinityBranchGerms_packaging_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hdown : Cycle292PadeRRealizedDownArrowInfinityWitnessFamily n d data)
    (hup : Cycle292PadeRRealizedUpArrowInfinityWitnessFamily n d data) :
    RealizesInfinityBranchGerms (padeR n d) data := by
  exact ⟨hdown, hup⟩
