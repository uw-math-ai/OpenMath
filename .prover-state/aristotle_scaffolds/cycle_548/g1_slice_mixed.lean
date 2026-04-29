import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau

/-- Cycle 548 sixth tracked `G1.mul`-direction well-definedness
deliverable: product preserves `G₁` equivalence on every node whose root
children are `a` plain leaves followed by `b` singleton-leaf nodes, with
the order bound `1 + a + 2 * b ≤ p`.

Hint: rewrite both sides with
`QuotEquiv.bSeriesHom_product_node_mixed_leaf_singleton_leaf` and follow
the cycle 547 `product_congr_node_replicate_singleton_leaf` pattern,
applying `hq` to `t₁.bSeries`-image trees of small order
(BTree.leaf, BTree.node [BTree.leaf], the full mixed root, and the
kept-side mixed bodies at strictly smaller order). -/
theorem product_congr_node_mixed_leaf_singleton_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (a b : ℕ) (hab : 1 + a + 2 * b ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]))) := by
  sorry

end ButcherTableau
