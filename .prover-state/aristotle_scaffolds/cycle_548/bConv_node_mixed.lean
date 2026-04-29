import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau

/-- §384 honest convolution closed form on the mixed root family
`BTree.node (List.replicate a BTree.leaf ++ List.replicate b (BTree.node [BTree.leaf]))`.

Three combinatorial choices: (1) `S_leaf ⊆ Fin a` of root leaves to cut,
(2) `S_sl ⊆ Fin b` of root singleton-leaf children to cut, (3)
`T ⊆ S_slᶜ` of kept singleton-leaf children whose internal leaf is
internally cut. The kept-side `t₂.bSeries` summand is a node with
`(a - S_leaf.card) + T.card` plain leaves followed by
`(b - S_sl.card) - T.card` singleton-leaf children.

Cycle 547 lemma `bConv_node_replicate_singleton_leaf_eq` is the
`a = 0` slice. Cycle 542 lemma `bConv_node_replicate_leaf_eq` is the
`b = 0` slice. -/
theorem ButcherProduct.bConv_node_mixed_leaf_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (a b : ℕ) :
    ButcherProduct.bConv (t₁.bSeries) t₂
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
  sorry

end ButcherTableau
