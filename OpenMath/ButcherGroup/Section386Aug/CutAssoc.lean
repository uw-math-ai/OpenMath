import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-! ## Cycle 604: cut-aggregate API for unital `bSeriesConvAug`
associativity

The depth-by-depth `mul_assoc_at_node_depth_<k>_children` ladder
(cycles 598/599/600/602/603) closed depth-1, depth-2, and depth-3, but
each new depth introduces a fresh family of cohort lemmas.  The
strong-induction obstruction issue identifies the single algebraic
identity whose proof would collapse the entire ladder into one
parametric headline: a Hopf-style cut-associativity at the level of
`BTree.innerCut`.

This module begins that infrastructure.  We define the
`cutAggregate` combinator that aggregates the proper-trunk inner-cut
contributions, prove its base reductions on `BTree.leaf` and
`BTree.node []`, give the bridge to `bSeriesConvAug`, and state the
cut-associativity headline together with the three sanity cases that
the eventual inductive proof must specialize to.  The headline itself
is left as the only sorry in this module, awaiting the structural
mutual induction over `BTree.innerCut` / `BTree.innerCutForest`.
-/

/-- Aggregate `Σ_{(some t, w) ∈ τ.innerCut α} w * F t` over the proper
inner cuts of `τ`.  Equivalently, `bSeriesConvAug ⟨_, α⟩ ⟨_, F⟩ τ`
minus the full-prune branch weighted by `β.emptyVal`. -/
noncomputable def cutAggregate (α : BTree → ℝ) (F : BTree → ℝ)
    (τ : BTree) : ℝ :=
  ((τ.innerCut α).filterMap (fun c => c.1.map (fun t => c.2 * F t))).sum

@[simp] theorem cutAggregate_leaf (α F : BTree → ℝ) :
    cutAggregate α F BTree.leaf = F BTree.leaf := by
  simp [cutAggregate, BTree.innerCut]

@[simp] theorem cutAggregate_node_nil (α F : BTree → ℝ) :
    cutAggregate α F (BTree.node []) = F (BTree.node []) := by
  simp [cutAggregate, BTree.innerCut, BTree.innerCutForest]

theorem cutAggregate_node_singleton_leaf (α F : BTree → ℝ) :
    cutAggregate α F (BTree.node [BTree.leaf])
      = F (BTree.node [BTree.leaf]) + α BTree.leaf * F (BTree.node []) := by
  simp [cutAggregate, BTree.innerCut, BTree.innerCutForest, add_comm]

/-- Reduce the `none`-branch sum of `τ.innerCut α` to `α τ`.  The only
`none` entry in `τ.innerCut α` at the root level is the full-prune
`(none, α τ)`; all other entries are tagged with `some trunk`. -/
private lemma sum_none_innerCut (α : BTree → ℝ) (τ : BTree) :
    ((τ.innerCut α).filterMap (fun c => match c.1 with
        | none => some c.2 | some _ => none)).sum = α τ := by
  cases τ with
  | leaf => simp [BTree.innerCut]
  | node children =>
    rw [innerCut_node]
    simp only [List.filterMap_cons, List.sum_cons]
    have htail :
        (((BTree.innerCutForest children α).map (fun cs =>
            (some (BTree.node (cs.filterMap (fun c => c.1))),
              cs.foldr (fun c acc => c.2 * acc) (1 : ℝ)))).filterMap
            (fun c => match c.1 with
              | none => some c.2 | some _ => none)) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro x hx
      rcases List.mem_map.mp hx with ⟨_, _, rfl⟩
      rfl
    rw [htail]
    simp

/-- Generic split: for any list `L` of `(Option BTree × ℝ)` entries,
the augmented sum equals the proper-cut sum plus the `none`-branch sum
weighted by `e`. -/
private lemma list_aug_split
    (L : List (Option BTree × ℝ)) (g : BTree → ℝ) (e : ℝ) :
    (L.map (fun c => match c.1 with
        | some trunk => c.2 * g trunk | none => c.2 * e)).sum
      = (L.filterMap (fun c => c.1.map (fun t => c.2 * g t))).sum
        + e * (L.filterMap (fun c => match c.1 with
            | none => some c.2 | some _ => none)).sum := by
  induction L with
  | nil => simp
  | cons head tail ih =>
    cases h : head.1 with
    | none =>
      simp only [List.map_cons, List.filterMap_cons, h, List.sum_cons,
        Option.map_none]
      rw [ih]
      ring
    | some t =>
      simp only [List.map_cons, List.filterMap_cons, h, List.sum_cons,
        Option.map_some]
      rw [ih]
      ring

/-- Bridge: the augmented convolution `bSeriesConvAug α β` decomposes
as the proper-cut aggregate against `β.toFun` plus the full-prune
contribution `α.toFun τ * β.emptyVal`. -/
theorem bSeriesConvAug_eq_cutAggregate (α β : AugSeries) (τ : BTree) :
    bSeriesConvAug α β τ
      = cutAggregate α.toFun β.toFun τ + α.toFun τ * β.emptyVal := by
  show ((τ.innerCut α.toFun).map (fun c => match c.1 with
        | some trunk => c.2 * β.toFun trunk
        | none => c.2 * β.emptyVal)).sum
      = ((τ.innerCut α.toFun).filterMap
            (fun c => c.1.map (fun t => c.2 * β.toFun t))).sum
        + α.toFun τ * β.emptyVal
  rw [list_aug_split (τ.innerCut α.toFun) β.toFun β.emptyVal,
      sum_none_innerCut]
  ring

/-- Hopf-style cut-associativity for the unital augmented convolution.

For every coefficient function `F : BTree → ℝ` and every tree `c`,
the inner-cut aggregate of the convolved series `bSeriesConvAug α β`
at `c` equals the iterated double aggregate through the outer
`α`-cuts and the inner `β`-cuts on each resulting trunk.  The unital
hypothesis on `β` collapses the full-prune correction in the
intermediate trunk evaluations.

This is the structural identity whose proof collapses the entire
`mul_assoc_at_node_depth_<k>_children` ladder into one parametric
headline; see the `section386aug_strong_induction_obstruction.md`
issue file. -/
theorem cutAggregate_bSeriesConvAug
    (α β : AugSeries) (hβ : β.IsUnital) (F : BTree → ℝ) (c : BTree) :
    cutAggregate (fun t => bSeriesConvAug α β t) F c
      = cutAggregate α.toFun (fun t => cutAggregate β.toFun F t) c := by
  sorry

/-- Sanity case at `c = BTree.leaf`: both sides reduce to `F leaf`. -/
theorem cutAggregate_bSeriesConvAug_leaf
    (α β : AugSeries) (_ : β.IsUnital) (F : BTree → ℝ) :
    cutAggregate (fun t => bSeriesConvAug α β t) F BTree.leaf
      = cutAggregate α.toFun (fun t => cutAggregate β.toFun F t)
          BTree.leaf := by
  simp

/-- Sanity case at `c = BTree.node []`: both sides reduce to
`F (node [])`. -/
theorem cutAggregate_bSeriesConvAug_node_nil
    (α β : AugSeries) (_ : β.IsUnital) (F : BTree → ℝ) :
    cutAggregate (fun t => bSeriesConvAug α β t) F (BTree.node [])
      = cutAggregate α.toFun (fun t => cutAggregate β.toFun F t)
          (BTree.node []) := by
  simp

/-- Sanity case at `c = BTree.node [BTree.leaf]`: the smallest case
where the unitality of `β` is load-bearing.  Both sides reduce, via
`bSeriesConvAug_node_singleton_leaf` and
`cutAggregate_node_singleton_leaf`, to
`F (node [leaf]) + (β leaf + α leaf) * F (node [])`. -/
theorem cutAggregate_bSeriesConvAug_node_singleton_leaf
    (α β : AugSeries) (hβ : β.IsUnital) (F : BTree → ℝ) :
    cutAggregate (fun t => bSeriesConvAug α β t) F
        (BTree.node [BTree.leaf])
      = cutAggregate α.toFun (fun t => cutAggregate β.toFun F t)
          (BTree.node [BTree.leaf]) := by
  have hβ' : β.emptyVal = 1 := hβ
  rw [cutAggregate_node_singleton_leaf, cutAggregate_node_singleton_leaf]
  simp only [bSeriesConvAug_leaf, cutAggregate_node_singleton_leaf,
    cutAggregate_node_nil]
  rw [hβ']
  ring

end ButcherTableau
