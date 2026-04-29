import OpenMath.ButcherGroup

namespace ButcherTableau
namespace IsG1Equiv

theorem cycle563_product_congr_node_replicate_triple_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (n : ℕ) (hn : 1 + 4 * n ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) := by
  sorry

end IsG1Equiv
end ButcherTableau
