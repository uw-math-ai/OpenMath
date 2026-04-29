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

noncomputable def bSeriesConvAug (α β : AugSeries) (τ : BTree) : ℝ :=
  ((τ.innerCut α.toFun).map fun c =>
      match c.1 with
      | some trunk => c.2 * β.toFun trunk
      | none       => c.2 * β.emptyVal).sum

theorem bSeriesConvAug_node (α β : AugSeries) (children : List BTree) :
    bSeriesConvAug α β (BTree.node children)
      = α.toFun (BTree.node children) * β.emptyVal
        + ((BTree.innerCutForest children α.toFun).map (fun cs =>
            cs.foldr (fun c acc => c.2 * acc) (1 : ℝ)
              * β.toFun (BTree.node (cs.filterMap (fun c => c.1))))).sum := by
  unfold bSeriesConvAug
  rw [BTree.innerCut]
  simp [List.map_cons, List.map_map, Function.comp_def]

end ButcherTableau
