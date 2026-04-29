import OpenMath.ButcherGroup.Section384SlicesMixed

open Finset

namespace ButcherTableau

theorem cycle563_bConv_node_replicate_triple_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    ButcherProduct.bConv (t₁.bSeries) t₂
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef (t₁.bSeries BTree.leaf) χ *
                t₂.bSeries (tripleLeafChoiceTree χ)) := by
  sorry

end ButcherTableau
