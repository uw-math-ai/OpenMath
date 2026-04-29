import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-- Closed form for `bSeriesConvAug` on a two-leaf node. -/
theorem bSeriesConvAug_node_two_leaves (α β : AugSeries) :
    bSeriesConvAug α β (BTree.node [BTree.leaf, BTree.leaf])
      = α.toFun (BTree.node [BTree.leaf, BTree.leaf]) * β.emptyVal
        + β.toFun (BTree.node [BTree.leaf, BTree.leaf])
        + 2 * α.toFun BTree.leaf * β.toFun (BTree.node [BTree.leaf])
        + α.toFun BTree.leaf * α.toFun BTree.leaf * β.toFun (BTree.node []) := by
  sorry

/-- `n=2` instance of unital associativity at `BTree.node [leaf, leaf]`. -/
theorem mul_assoc_at_node_two_leaves
    (α β γ : AugSeries)
    (hα : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node [BTree.leaf, BTree.leaf])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node [BTree.leaf, BTree.leaf]) := by
  sorry

end ButcherTableau
