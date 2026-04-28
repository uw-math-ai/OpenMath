import OpenMath.ButcherGroup

namespace ButcherTableau

/-- The elementary weight of `ButcherProduct t₁ t₂` at an upper-left block
row index `Fin.castAdd t i` reduces to the elementary weight of `t₁` alone.
This is the next-layer reduction for the §384 convolution: it lets us
identify the "cuts" factor in cycle 518's powerset identity with
`t₁.bSeries`. -/
theorem cycle518_butcherProduct_elementaryWeight_castAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin s) :
    (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i)
      = t₁.elementaryWeight τ i := by
  sorry

end ButcherTableau
