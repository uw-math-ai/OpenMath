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

def cycle292_realizesInfinityBranchGerms_equiv_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData} :
    RealizesInfinityBranchGerms (padeR n d) data ≃
      (Cycle292PadeRRealizedDownArrowInfinityWitnessFamily n d data ×
        Cycle292PadeRRealizedUpArrowInfinityWitnessFamily n d data) where
  toFun hreal := ⟨hreal.downArrowInfinityWitnesses, hreal.upArrowInfinityWitnesses⟩
  invFun hreal := ⟨hreal.1, hreal.2⟩
  left_inv hreal := by cases hreal <;> rfl
  right_inv hreal := by cases hreal <;> rfl
