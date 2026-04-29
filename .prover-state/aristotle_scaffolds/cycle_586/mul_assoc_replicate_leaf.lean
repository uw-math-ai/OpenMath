import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-- Parametric depth-2 unital associativity sanity check at
`BTree.node (List.replicate n BTree.leaf)`. -/
theorem mul_assoc_at_node_replicate_leaf
    (α β γ : AugSeries)
    (hα : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) (n : ℕ) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node (List.replicate n BTree.leaf))
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node (List.replicate n BTree.leaf)) := by
  sorry

end ButcherTableau
