import OpenMath.ButcherGroup

open BigOperators

theorem cycle521_rightAuxAt_node_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j) := by
  sorry
