import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup

open Finset

namespace ButcherTableau

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

/-- §384 right-block recursive reduction: the elementary weight of
`ButcherProduct t₁ t₂` at a second-method stage `Fin.natAdd s i` is the
recursive auxiliary `rightAuxAt t₁ t₂ τ i`. The `t₁` data only enters
through `bSeries`, which makes the closed-form `(trunk, cuts)`
decomposition viable on the next layer. -/
theorem ButcherProduct.elementaryWeight_natAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
      = ButcherProduct.rightAuxAt t₁ t₂ τ i := by
  sorry

end ButcherTableau
