import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau

theorem ButcherProduct.elementaryWeight_natAdd_node
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.natAdd s i)
      = children.foldr
          (fun c acc => acc * (t₁.bSeries c +
            ∑ j : Fin t, t₂.A i j *
              (ButcherProduct t₁ t₂).elementaryWeight c (Fin.natAdd s j))) 1 := by
  sorry

end ButcherTableau
