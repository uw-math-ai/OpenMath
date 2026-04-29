import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv

/-!
# Butcher §386 unital augmented convolution

Cycle 580 showed that the asymmetric `bSeriesConv` from
`OpenMath.ButcherGroup.Section386Conv` is not associative even on
`BTree.node [BTree.leaf]`.  The mismatch comes from the trivial no-prune
branch carrying weight `1` rather than `α.emptyVal` while the full-prune
branch is filtered out.

Cycle 583 attempted an augmented convolution
`bSeriesConvAug : AugSeries → AugSeries → BTree → ℝ` that adds the
full-prune branch weighted by `β.emptyVal`.  That definition is also not
associative for arbitrary augmented series, see
`.prover-state/issues/butcher_section386_aug_middle_emptyval.md`.

This module provides the same `bSeriesConvAug` together with an
`IsUnital` predicate and proves depth-2 associativity on the unital
subspace.  The bridge to the asymmetric `bSeriesConv` records the
canonical pair of empty values (`⟨1, _⟩` on the left and `⟨0, _⟩` on
the right) under which the two convolutions agree.

The §388 antipode / `Group (G1 p)` work will use the unital augmented
convolution going forward.
-/

open Finset

namespace ButcherTableau

/-- A real-valued tree series augmented with an empty-forest value.

The `emptyVal` field captures the value that the empty pruned forest
contributes to a convolution; the `toFun` field is the usual coefficient
on rooted trees. -/
structure AugSeries where
  emptyVal : ℝ
  toFun    : BTree → ℝ

/-- A unital augmented series has empty-forest value `1`. -/
def AugSeries.IsUnital (α : AugSeries) : Prop := α.emptyVal = 1

/-- Augmented bSeries-only convolution.  Both branches of the inner cut
contribute: the `some trunk` branch with weight `c.2 * β.toFun trunk`,
and the full-prune `none` branch with weight `c.2 * β.emptyVal`. -/
noncomputable def bSeriesConvAug (α β : AugSeries) (τ : BTree) : ℝ :=
  ((τ.innerCut α.toFun).map fun c =>
      match c.1 with
      | some trunk => c.2 * β.toFun trunk
      | none       => c.2 * β.emptyVal).sum

theorem bSeriesConvAug_leaf (α β : AugSeries) :
    bSeriesConvAug α β BTree.leaf
      = β.toFun BTree.leaf + α.toFun BTree.leaf * β.emptyVal := by
  simp [bSeriesConvAug, BTree.innerCut]

theorem bSeriesConvAug_node_nil (α β : AugSeries) :
    bSeriesConvAug α β (BTree.node [])
      = α.toFun (BTree.node []) * β.emptyVal + β.toFun (BTree.node []) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]

theorem bSeriesConvAug_node_singleton_leaf (α β : AugSeries) :
    bSeriesConvAug α β (BTree.node [BTree.leaf])
      = α.toFun (BTree.node [BTree.leaf]) * β.emptyVal
        + β.toFun (BTree.node [BTree.leaf])
        + α.toFun BTree.leaf * β.toFun (BTree.node []) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest, add_assoc]

/-- Bridge: the asymmetric `bSeriesConv` agrees with `bSeriesConvAug`
when the right argument has `emptyVal = 0` (so the full-prune branch
contributes nothing).  The left argument's `emptyVal` is unused by
`bSeriesConvAug`; we pin it to `1` for the canonical unital embedding. -/
theorem bSeriesConv_eq_bSeriesConvAug (α β : BTree → ℝ) (τ : BTree) :
    bSeriesConv α β τ
      = bSeriesConvAug ⟨1, α⟩ ⟨0, β⟩ τ := by
  unfold bSeriesConv bSeriesConvAug
  show ((τ.innerCut α).filterMap fun c => c.1.map (fun t => c.2 * β t)).sum
      = ((τ.innerCut α).map fun c =>
          match c.1 with
          | some trunk => c.2 * β trunk
          | none       => c.2 * 0).sum
  induction τ.innerCut α with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨h1, h2⟩ := head
    cases h1 with
    | none =>
      simp only [List.filterMap_cons, Option.map_none,
        List.map_cons, List.sum_cons]
      rw [mul_zero, zero_add]
      exact ih
    | some t =>
      simp only [List.filterMap_cons, Option.map_some,
        List.map_cons, List.sum_cons]
      rw [ih]

/-- Depth-2 unital associativity sanity check.

For unital augmented series `α, β, γ`, the augmented convolution is
associative at `BTree.node [BTree.leaf]`.  This is the smallest
non-trivial associativity check for the §388 antipode work and
isolates the `β.emptyVal · α(leaf) · γ(node [])` mismatch documented
in the cycle 583 issue file. -/
theorem mul_assoc_at_node_singleton_leaf
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node [BTree.leaf])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node [BTree.leaf]) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  rw [bSeriesConvAug_node_singleton_leaf, bSeriesConvAug_node_singleton_leaf]
  simp only [bSeriesConvAug_leaf, bSeriesConvAug_node_nil,
    bSeriesConvAug_node_singleton_leaf]
  rw [hβ', hγ']
  ring

/-- One-line corollary at `BTree.leaf` for unital augmented series. -/
theorem mul_assoc_at_leaf
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ BTree.leaf
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩ BTree.leaf := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  simp only [bSeriesConvAug_leaf]
  rw [hβ', hγ']
  ring

/-- One-line corollary at `BTree.node []` for unital augmented series. -/
theorem mul_assoc_at_node_nil
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ (BTree.node [])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩ (BTree.node []) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  simp only [bSeriesConvAug_node_nil]
  rw [hβ', hγ']
  ring

/-- Closed form for the next order-2 tree `BTree.node [BTree.node []]`. -/
theorem bSeriesConvAug_node_node_nil (α β : AugSeries) :
    bSeriesConvAug α β (BTree.node [BTree.node []])
      = α.toFun (BTree.node [BTree.node []]) * β.emptyVal
        + β.toFun (BTree.node [BTree.node []])
        + α.toFun (BTree.node []) * β.toFun (BTree.node []) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest,
    add_comm, add_left_comm]

/-- Depth-2 unital associativity sanity check at
`BTree.node [BTree.node []]`. -/
theorem mul_assoc_at_node_node_nil
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node [BTree.node []])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node [BTree.node []]) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  rw [bSeriesConvAug_node_node_nil, bSeriesConvAug_node_node_nil]
  simp only [bSeriesConvAug_node_nil, bSeriesConvAug_node_node_nil]
  rw [hβ', hγ']
  ring

/-- Symmetric root split for `bSeriesConvAug` at a node: the root-prune
branch is separated from the forest cuts that keep the trunk root. -/
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
