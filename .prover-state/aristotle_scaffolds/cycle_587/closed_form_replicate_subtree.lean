import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-- Cycle 587 Aristotle payload: the naive replicate-subtree closed form.

This is expected to expose the partial-inner-cut obstruction when
`τ.innerCut` has branches other than `some τ` and `none`. -/
theorem bSeriesConvAug_node_replicate_cycle587
    (α β : AugSeries) (τ : BTree) (n : ℕ) :
    bSeriesConvAug α β (BTree.node (List.replicate n τ))
      = α.toFun (BTree.node (List.replicate n τ)) * β.emptyVal
        + ∑ S : Finset (Fin n), α.toFun τ ^ S.card *
            β.toFun (BTree.node (List.replicate (n - S.card) τ)) := by
  sorry

end ButcherTableau
