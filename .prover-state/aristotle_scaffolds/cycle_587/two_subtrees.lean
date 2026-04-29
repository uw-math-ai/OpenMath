import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-- Cycle 587 Aristotle payload: the `n = 2` replicate-subtree corollary. -/
theorem mul_assoc_at_node_two_subtrees_cycle587
    (α β γ : AugSeries)
    (hα : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) (τ : BTree) :
    bSeriesConvAug ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ
        (BTree.node [τ, τ])
      = bSeriesConvAug α ⟨1, fun σ => bSeriesConvAug β γ σ⟩
          (BTree.node [τ, τ]) := by
  sorry

end ButcherTableau
