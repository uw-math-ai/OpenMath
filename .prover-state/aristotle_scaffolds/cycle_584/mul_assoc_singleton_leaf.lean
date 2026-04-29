import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv

open Finset

namespace ButcherTableau

structure AugSeries where
  emptyVal : ℝ
  toFun    : BTree → ℝ

def AugSeries.IsUnital (α : AugSeries) : Prop := α.emptyVal = 1

noncomputable def bSeriesConvAug (α β : AugSeries) (τ : BTree) : ℝ :=
  ((τ.innerCut α.toFun).map fun c =>
      match c.1 with
      | some trunk => c.2 * β.toFun trunk
      | none       => c.2 * β.emptyVal).sum

theorem bSeriesConvAug_leaf (α β : AugSeries) :
    bSeriesConvAug α β BTree.leaf
      = β.toFun BTree.leaf + α.toFun BTree.leaf * β.emptyVal := by
  sorry

theorem bSeriesConvAug_node_nil (α β : AugSeries) :
    bSeriesConvAug α β (BTree.node [])
      = α.toFun (BTree.node []) * β.emptyVal + β.toFun (BTree.node []) := by
  sorry

theorem bSeriesConvAug_node_singleton_leaf (α β : AugSeries) :
    bSeriesConvAug α β (BTree.node [BTree.leaf])
      = α.toFun (BTree.node [BTree.leaf]) * β.emptyVal
        + β.toFun (BTree.node [BTree.leaf])
        + α.toFun BTree.leaf * β.toFun (BTree.node []) := by
  sorry

theorem bSeriesConv_eq_bSeriesConvAug (α β : BTree → ℝ) (τ : BTree) :
    bSeriesConv α β τ = bSeriesConvAug ⟨1, α⟩ ⟨0, β⟩ τ := by
  sorry

theorem mul_assoc_at_node_singleton_leaf
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node [BTree.leaf])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node [BTree.leaf]) := by
  sorry

end ButcherTableau
