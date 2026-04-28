import OpenMath.ButcherGroup

namespace ButcherTableau

/-- Leaf case for the upper-left block elementary-weight reduction. -/
theorem cycle519_elementaryWeight_castAdd_leaf
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (i : Fin s) :
    (ButcherProduct t₁ t₂).elementaryWeight BTree.leaf (Fin.castAdd t i)
      = t₁.elementaryWeight BTree.leaf i := by
  sorry

end ButcherTableau
