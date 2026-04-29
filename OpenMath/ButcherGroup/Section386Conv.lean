import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section384
import OpenMath.ButcherGroup.Section384Slices

/-!
# Butcher §386 honest bSeries-only convolution

Defines `bSeriesConv α β τ` recursively on `BTree`, depending on the
two coefficient maps `α, β : BTree → ℝ` only -- **not** on the
underlying `ButcherTableau`. This is the Connes-Kreimer pruning
convolution: a sum over admissible cuts of `τ` of
`(∏ pruned subtree p, α p) · β trunk`.

This module is the structural prerequisite for `IsG1Equiv.product_congr`
(see `.prover-state/issues/butcher_g1_mul_section384_blocker.md`)
and for `QuotEquiv.bSeriesHom_product` in unrestricted form (see
`.prover-state/issues/butcher_section384_convolution.md`).

Cycle 567 lands the definition and small-case unfolding lemmas.
The headline equality
`(t₁.product t₂).bSeries τ = t₁.bSeries τ + bSeriesConv (t₁.bSeries) (t₂.bSeries) τ`
is left for a follow-up cycle.
-/

open Finset

namespace ButcherTableau

/-
Enumerate admissible inner cuts of a rooted tree.

The result is a list of `(trunk?, weight)` pairs. `some trunk` means the
root remains in the trunk after cutting descendants; `none` means this
whole tree has been pruned away, contributing `α τ` to the cut weight.

The child-choice product is implemented by the mutually recursive
`BTree.innerCutForest`: for a list of children it returns all lists of one
cut choice per child. -/
mutual
  noncomputable def _root_.BTree.innerCut (τ : BTree) (α : BTree → ℝ) :
      List (Option BTree × ℝ) :=
    match τ with
    | BTree.leaf => [(some BTree.leaf, (1 : ℝ)), (none, α BTree.leaf)]
    | BTree.node children =>
        (none, α (BTree.node children)) ::
          (BTree.innerCutForest children α).map (fun cs =>
            (some (BTree.node (cs.filterMap (fun c => c.1))),
              cs.foldr (fun c acc => c.2 * acc) (1 : ℝ)))
  termination_by sizeOf τ
  decreasing_by
    all_goals simp_wf

  /-- List-level child-choice product induced by `BTree.innerCut`. For a
  list of children, it returns all lists of one cut choice per child. -/
  noncomputable def _root_.BTree.innerCutForest (children : List BTree)
      (α : BTree → ℝ) : List (List (Option BTree × ℝ)) :=
    match children with
    | [] => [[]]
    | head :: tail =>
        List.flatMap
          (fun c => (BTree.innerCutForest tail α).map (fun cs => c :: cs))
          (head.innerCut α)
  termination_by sizeOf children
  decreasing_by
    all_goals
      simp_wf
      try omega
end

/-- The bSeries-only admissible-cut convolution: keep only cuts whose root
survives in the trunk, multiplying the cut weight by the second coefficient
map evaluated on that trunk. -/
noncomputable def bSeriesConv (α β : BTree → ℝ) (τ : BTree) : ℝ :=
  ((τ.innerCut α).filterMap fun c => c.1.map (fun t => c.2 * β t)).sum

theorem innerCut_leaf (α : BTree → ℝ) :
    BTree.leaf.innerCut α = [(some BTree.leaf, 1), (none, α BTree.leaf)] := by
  simp [BTree.innerCut]

theorem innerCut_node_nil (α : BTree → ℝ) :
    (BTree.node []).innerCut α =
      [(none, α (BTree.node [])), (some (BTree.node []), 1)] := by
  simp [BTree.innerCut, BTree.innerCutForest]

theorem innerCut_node (α : BTree → ℝ) (children : List BTree) :
    (BTree.node children).innerCut α =
      (none, α (BTree.node children)) ::
        ((BTree.innerCutForest children α).map (fun cs =>
          (some (BTree.node (cs.filterMap (fun c => c.1))),
            cs.foldr (fun c acc => c.2 * acc) (1 : ℝ)))) := by
  cases children <;> simp [BTree.innerCut, BTree.innerCutForest]

theorem innerCut_node_singleton_leaf (α : BTree → ℝ) :
    (BTree.node [BTree.leaf]).innerCut α =
      [(none, α (BTree.node [BTree.leaf])),
        (some (BTree.node [BTree.leaf]), 1),
        (some (BTree.node []), α BTree.leaf)] := by
  simp [BTree.innerCut, BTree.innerCutForest]

theorem bSeriesConv_leaf (α β : BTree → ℝ) :
    bSeriesConv α β BTree.leaf = β BTree.leaf := by
  simp [bSeriesConv, BTree.innerCut]

theorem bSeriesConv_node_nil (α β : BTree → ℝ) :
    bSeriesConv α β (BTree.node []) = β (BTree.node []) := by
  simp [bSeriesConv, BTree.innerCut, BTree.innerCutForest]

theorem bSeriesConv_node_singleton_leaf (α β : BTree → ℝ) :
    bSeriesConv α β (BTree.node [BTree.leaf])
      = β (BTree.node [BTree.leaf]) + α BTree.leaf * β (BTree.node []) := by
  simp [bSeriesConv, BTree.innerCut, BTree.innerCutForest]

theorem bSeriesConv_singleton_leaf_consistency
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    t₁.bSeries (BTree.node [BTree.leaf])
      + bSeriesConv (t₁.bSeries) (t₂.bSeries) (BTree.node [BTree.leaf])
    = (ButcherProduct t₁ t₂).bSeries (BTree.node [BTree.leaf]) := by
  rw [bSeriesConv_node_singleton_leaf,
      ButcherProduct.bSeries_singleton_leaf_eq]
  rw [bSeries_node_nil]
  ring

end ButcherTableau
