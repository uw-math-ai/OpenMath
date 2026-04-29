import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-- Cycle 587 Aristotle payload: replicate of an arbitrary fixed subtree. -/
theorem mul_assoc_at_node_replicate_cycle587
    (α β γ : AugSeries)
    (hα : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital)
    (τ : BTree) (n : ℕ) :
    bSeriesConvAug ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ
        (BTree.node (List.replicate n τ))
      = bSeriesConvAug α ⟨1, fun σ => bSeriesConvAug β γ σ⟩
          (BTree.node (List.replicate n τ)) := by
  sorry

end ButcherTableau
