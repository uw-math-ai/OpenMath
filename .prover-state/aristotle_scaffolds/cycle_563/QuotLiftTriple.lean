import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau
namespace QuotEquiv

theorem cycle563_bSeriesHom_product_node_replicate_triple_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (n : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = q.bSeriesHom
          (BTree.node
            (List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (q.bSeriesHom
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef (q.bSeriesHom BTree.leaf) χ *
                r.bSeriesHom (tripleLeafChoiceTree χ)) := by
  sorry

end QuotEquiv
end ButcherTableau
