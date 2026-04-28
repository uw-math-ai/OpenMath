import OpenMath.ButcherGroup

namespace ButcherTableau

/-- Node/foldr step for the upper-left block elementary-weight reduction,
assuming the child-level reduction hypotheses. -/
theorem cycle519_elementaryWeight_castAdd_node
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree)
    (ih : ∀ c ∈ children, ∀ i : Fin s,
      (ButcherProduct t₁ t₂).elementaryWeight c (Fin.castAdd t i)
        = t₁.elementaryWeight c i)
    (i : Fin s) :
    (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.castAdd t i)
      = t₁.elementaryWeight (BTree.node children) i := by
  sorry

end ButcherTableau
