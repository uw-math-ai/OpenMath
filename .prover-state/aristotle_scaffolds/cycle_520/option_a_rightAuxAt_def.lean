import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau

/-- §384 right-block auxiliary `ψ`: the recursive contribution attached
to a second-method stage `i : Fin t` after the upper-left block has been
collapsed via `t₁.bSeries`. The closed form is the structural witness for
the §384 convolution recursion. -/
noncomputable def ButcherProduct.rightAuxAt
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    BTree → Fin t → ℝ
  | .leaf, _ => 1
  | .node children, i =>
      children.foldr
        (fun c acc => acc * (t₁.bSeries c +
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAt t₁ t₂ c j)) 1
termination_by t => sizeOf t
decreasing_by
  have hmem : sizeOf c < sizeOf children :=
    List.sizeOf_lt_of_mem (by assumption)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by simp
  exact Nat.lt_trans hmem hnode

@[simp] theorem ButcherProduct.rightAuxAt_leaf
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ BTree.leaf i = 1 := by
  sorry

theorem ButcherProduct.rightAuxAt_node
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
      = children.foldr
          (fun c acc => acc * (t₁.bSeries c +
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ c j)) 1 := by
  sorry

end ButcherTableau
