import OpenMath.ButcherGroup

namespace ButcherTableau

/-- Full upper-left block elementary-weight reduction, using nested
`BTree.rec` over the tree and child list. -/
theorem cycle519_elementaryWeight_castAdd_full
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin s) :
    (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i)
      = t₁.elementaryWeight τ i := by
  sorry

end ButcherTableau
