import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau

/-- bSeries-form corollary of the cycle 548 mixed leaf/singleton-leaf
root-children parametric closed form, modulo the `bConv` headline. -/
theorem ButcherProduct.bSeries_node_mixed_leaf_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (a b : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf])))
        + ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
              (t₁.bSeries BTree.leaf) ^ S_leaf.card *
                (t₁.bSeries (BTree.node [BTree.leaf])) ^ S_sl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  (t₁.bSeries BTree.leaf) ^ T.card *
                  t₂.bSeries
                    (BTree.node
                      (List.replicate (a - S_leaf.card + T.card) BTree.leaf ++
                        List.replicate ((S_slᶜ : Finset (Fin b)).card - T.card)
                          (BTree.node [BTree.leaf])))) := by
  -- Hint: by `ButcherProduct.bSeries_eq_bConv` and the `bConv` headline
  -- `ButcherProduct.bConv_node_mixed_leaf_singleton_leaf_eq`.
  sorry

end ButcherTableau
