import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-- Cycle 587 Aristotle payload: arbitrary children-list associativity. -/
theorem mul_assoc_at_node_cycle587
    (α β γ : AugSeries)
    (hα : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital)
    (children : List BTree) :
    bSeriesConvAug ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ
        (BTree.node children)
      = bSeriesConvAug α ⟨1, fun σ => bSeriesConvAug β γ σ⟩
          (BTree.node children) := by
  sorry

end ButcherTableau
