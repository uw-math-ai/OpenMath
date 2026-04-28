import OpenMath.ButcherGroup

namespace ButcherTableau

/-- Sanity base case for the §384 convolution: the elementary weight of
`ButcherProduct t₁ t₂` at a `leaf` and any second-method row equals 1
(the trivial "no children to split" case). -/
theorem cycle518_butcherProduct_elementaryWeight_natAdd_leaf
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight BTree.leaf (Fin.natAdd s i) = 1 := by
  sorry

end ButcherTableau
