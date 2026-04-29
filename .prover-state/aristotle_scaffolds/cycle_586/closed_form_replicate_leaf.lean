import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-- Closed form for `bSeriesConvAug` on a node with `n` leaf children. -/
theorem bSeriesConvAug_node_replicate_leaf (α β : AugSeries) (n : ℕ) :
    bSeriesConvAug α β (BTree.node (List.replicate n BTree.leaf))
      = α.toFun (BTree.node (List.replicate n BTree.leaf)) * β.emptyVal
        + ∑ S : Finset (Fin n), α.toFun BTree.leaf ^ S.card *
            β.toFun (BTree.node (List.replicate (n - S.card) BTree.leaf)) := by
  sorry

end ButcherTableau
