import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.Section386Aug

open Finset

namespace ButcherTableau

/-! ## Cycle 600: depth-3 mixed-children associativity scaffold

Extends the depth-1 (cycle 598) and depth-2 (cycle 599) cons recurrences
to head children of order at most 3.  The two new shape families are the
two-children-of-order-one node `BTree.node [a, b]` (each `a, b` either
`BTree.leaf` or `BTree.node []`) and the singleton-with-singleton head
`BTree.node [BTree.node [e]]` (with `e` of order ≤ 1).  See the
`section386aug_strong_induction_obstruction.md` issue for why the
parametric form is blocked. -/

/-- Cons recurrence for the inner-forest sum when the head child is the
depth-3 shape `BTree.node [a, b]` with `a, b` of order ≤ 1.  The keep-root
branch enumerates four trunks: `node [a, b]`, `node [a]`, `node [b]`, and
`node []`. -/
private theorem forestSum_cons_node_pair_depth_one
    (α β : AugSeries) (a b : BTree) (ha : a.order ≤ 1) (hb : b.order ≤ 1)
    (cs : List BTree) :
    ((BTree.innerCutForest (BTree.node [a, b] :: cs) α.toFun).map (fun forest =>
        forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
          * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
      = α.toFun (BTree.node [a, b])
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + α.toFun a * α.toFun b
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * (β.shiftBy (BTree.node [])).toFun
                    (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + α.toFun b
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * (β.shiftBy (BTree.node [a])).toFun
                    (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + α.toFun a
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * (β.shiftBy (BTree.node [b])).toFun
                    (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + ((BTree.innerCutForest cs α.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * (β.shiftBy (BTree.node [a, b])).toFun
                  (BTree.node (forest.filterMap (fun e => e.1))))).sum := by
  -- Helper: factor a scalar `k` out of a forest-sum-style map over the
  -- residual cuts.
  have hscale : ∀ (k : ℝ) (T : BTree),
      (List.map
          (fun forest =>
            k * forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node (T :: forest.filterMap (fun e => e.1))))
          (BTree.innerCutForest cs α.toFun)).sum
        = k * (List.map
            (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun
                    (BTree.node (T :: forest.filterMap (fun e => e.1))))
            (BTree.innerCutForest cs α.toFun)).sum := by
    intro k T
    induction BTree.innerCutForest cs α.toFun with
    | nil => simp
    | cons forest tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [bSeriesConvAug_innerForest_cons]
  rcases (order_le_one_iff a).mp ha with rfl | rfl <;>
    rcases (order_le_one_iff b).mp hb with rfl | rfl
  all_goals
    rw [innerCut_node]
    simp only [BTree.innerCutForest, innerCut_leaf, innerCut_node_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.flatMap_append,
      List.map_cons, List.map_nil, List.map_append,
      List.foldr_cons, List.foldr_nil,
      List.filterMap_cons, List.filterMap_nil, mul_one, one_mul,
      List.sum_cons, List.sum_nil, List.sum_append,
      add_zero, zero_add, AugSeries.shiftBy_node]
  -- Case 1: a = leaf, b = leaf
  · rw [hscale (α.toFun BTree.leaf * α.toFun BTree.leaf) (BTree.node []),
        hscale (α.toFun BTree.leaf) (BTree.node [BTree.leaf])]
    linarith
  -- Case 2: a = leaf, b = node []
  · rw [hscale (α.toFun BTree.leaf * α.toFun (BTree.node [])) (BTree.node []),
        hscale (α.toFun BTree.leaf) (BTree.node [BTree.node []]),
        hscale (α.toFun (BTree.node [])) (BTree.node [BTree.leaf])]
    linarith
  -- Case 3: a = node [], b = leaf
  · rw [hscale (α.toFun (BTree.node []) * α.toFun BTree.leaf) (BTree.node []),
        hscale (α.toFun (BTree.node [])) (BTree.node [BTree.leaf]),
        hscale (α.toFun BTree.leaf) (BTree.node [BTree.node []])]
    linarith
  -- Case 4: a = node [], b = node []
  · rw [hscale (α.toFun (BTree.node []) * α.toFun (BTree.node []))
          (BTree.node []),
        hscale (α.toFun (BTree.node [])) (BTree.node [BTree.node []])]
    linarith

/-- Cons recurrence for the inner-forest sum when the head child is the
depth-3 singleton shape `BTree.node [BTree.node [e]]` with `e.order ≤ 1`.
The keep-root branch enumerates three trunks: `node [node [e]]`,
`node [node []]`, and `node []`. -/
private theorem forestSum_cons_node_singleton_node_singleton_depth_one
    (α β : AugSeries) (e : BTree) (he : e.order ≤ 1) (cs : List BTree) :
    ((BTree.innerCutForest (BTree.node [BTree.node [e]] :: cs) α.toFun).map
        (fun forest =>
          forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
            * β.toFun (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
      = α.toFun (BTree.node [BTree.node [e]])
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                * β.toFun (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
        + α.toFun (BTree.node [e])
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                * (β.shiftBy (BTree.node [])).toFun
                    (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
        + α.toFun e
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                * (β.shiftBy (BTree.node [BTree.node []])).toFun
                    (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
        + ((BTree.innerCutForest cs α.toFun).map (fun forest =>
            forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
              * (β.shiftBy (BTree.node [BTree.node [e]])).toFun
                  (BTree.node (forest.filterMap (fun ec => ec.1))))).sum := by
  have hscale : ∀ (k : ℝ) (T : BTree),
      (List.map
          (fun forest =>
            k * forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node (T :: forest.filterMap (fun ec => ec.1))))
          (BTree.innerCutForest cs α.toFun)).sum
        = k * (List.map
            (fun forest =>
              forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                * β.toFun
                    (BTree.node (T :: forest.filterMap (fun ec => ec.1))))
            (BTree.innerCutForest cs α.toFun)).sum := by
    intro k T
    induction BTree.innerCutForest cs α.toFun with
    | nil => simp
    | cons forest tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [bSeriesConvAug_innerForest_cons]
  rcases (order_le_one_iff e).mp he with rfl | rfl
  · -- e = leaf
    have hcut : (BTree.node [BTree.node [BTree.leaf]]).innerCut α.toFun =
        [(none, α.toFun (BTree.node [BTree.node [BTree.leaf]])),
         (some (BTree.node []), α.toFun (BTree.node [BTree.leaf])),
         (some (BTree.node [BTree.node [BTree.leaf]]), 1),
         (some (BTree.node [BTree.node []]), α.toFun BTree.leaf)] := by
      simp [BTree.innerCut, BTree.innerCutForest]
    rw [hcut]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.nil_append, List.sum_append, one_mul, AugSeries.shiftBy_node]
    rw [hscale (α.toFun (BTree.node [BTree.leaf])) (BTree.node []),
        hscale (α.toFun BTree.leaf) (BTree.node [BTree.node []])]
    linarith
  · -- e = node []
    have hcut : (BTree.node [BTree.node [BTree.node []]]).innerCut α.toFun =
        [(none, α.toFun (BTree.node [BTree.node [BTree.node []]])),
         (some (BTree.node []), α.toFun (BTree.node [BTree.node []])),
         (some (BTree.node [BTree.node []]), α.toFun (BTree.node [])),
         (some (BTree.node [BTree.node [BTree.node []]]), 1)] := by
      simp [BTree.innerCut, BTree.innerCutForest]
    rw [hcut]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.nil_append, List.sum_append, one_mul, AugSeries.shiftBy_node]
    rw [hscale (α.toFun (BTree.node [BTree.node []])) (BTree.node []),
        hscale (α.toFun (BTree.node [])) (BTree.node [BTree.node []])]
    linarith

private theorem forestSum_cons_node_pair_depth_one_compact
    (α β : AugSeries) (a b : BTree) (ha : a.order ≤ 1) (hb : b.order ≤ 1)
    (cs : List BTree) :
    forestSum α.toFun β (BTree.node [a, b] :: cs)
      = α.toFun (BTree.node [a, b]) * forestSum α.toFun β cs
        + α.toFun a * α.toFun b
            * forestSum α.toFun (β.shiftBy (BTree.node [])) cs
        + α.toFun b * forestSum α.toFun (β.shiftBy (BTree.node [a])) cs
        + α.toFun a * forestSum α.toFun (β.shiftBy (BTree.node [b])) cs
        + forestSum α.toFun (β.shiftBy (BTree.node [a, b])) cs := by
  simpa [forestSum] using
    forestSum_cons_node_pair_depth_one α β a b ha hb cs

private theorem
    forestSum_cons_node_singleton_node_singleton_depth_one_compact
    (α β : AugSeries) (e : BTree) (he : e.order ≤ 1) (cs : List BTree) :
    forestSum α.toFun β (BTree.node [BTree.node [e]] :: cs)
      = α.toFun (BTree.node [BTree.node [e]]) * forestSum α.toFun β cs
        + α.toFun (BTree.node [e])
            * forestSum α.toFun (β.shiftBy (BTree.node [])) cs
        + α.toFun e
            * forestSum α.toFun (β.shiftBy (BTree.node [BTree.node []])) cs
        + forestSum α.toFun (β.shiftBy (BTree.node [BTree.node [e]])) cs := by
  simpa [forestSum] using
    forestSum_cons_node_singleton_node_singleton_depth_one α β e he cs

/-- Pointwise expansion of `bSeriesConvAug β γ` at a cons whose head is the
depth-3 pair shape `BTree.node [a, b]` with `a, b` of order ≤ 1. -/
private lemma bSeriesConvAug_node_cons_node_pair_depth_one_expand_compact
    (β γ : AugSeries) (a b : BTree) (ha : a.order ≤ 1) (hb : b.order ≤ 1)
    (xs : List BTree) :
    bSeriesConvAug β γ (BTree.node (BTree.node [a, b] :: xs))
      = β.toFun (BTree.node (BTree.node [a, b] :: xs)) * γ.emptyVal
        + β.toFun (BTree.node [a, b]) * forestSum β.toFun γ xs
        + β.toFun a * β.toFun b
            * forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
        + β.toFun b * forestSum β.toFun (γ.shiftBy (BTree.node [a])) xs
        + β.toFun a * forestSum β.toFun (γ.shiftBy (BTree.node [b])) xs
        + forestSum β.toFun (γ.shiftBy (BTree.node [a, b])) xs := by
  rw [bSeriesConvAug_node β γ (BTree.node [a, b] :: xs),
      forestSum_cons_node_pair_depth_one β γ a b ha hb xs]
  simp only [forestSum, AugSeries.shiftBy_node]
  ring

/-- Pointwise expansion of `bSeriesConvAug β γ` at a cons whose head is the
depth-3 singleton-of-singleton shape `BTree.node [BTree.node [e]]` with
`e.order ≤ 1`. -/
private lemma
    bSeriesConvAug_node_cons_node_singleton_node_singleton_depth_one_expand_compact
    (β γ : AugSeries) (e : BTree) (he : e.order ≤ 1) (xs : List BTree) :
    bSeriesConvAug β γ (BTree.node (BTree.node [BTree.node [e]] :: xs))
      = β.toFun (BTree.node (BTree.node [BTree.node [e]] :: xs))
            * γ.emptyVal
        + β.toFun (BTree.node [BTree.node [e]]) * forestSum β.toFun γ xs
        + β.toFun (BTree.node [e])
            * forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
        + β.toFun e
            * forestSum β.toFun (γ.shiftBy (BTree.node [BTree.node []])) xs
        + forestSum β.toFun
            (γ.shiftBy (BTree.node [BTree.node [e]])) xs := by
  rw [bSeriesConvAug_node β γ (BTree.node [BTree.node [e]] :: xs),
      forestSum_cons_node_singleton_node_singleton_depth_one β γ e he xs]
  simp only [forestSum, AugSeries.shiftBy_node]
  ring

/-- Cons recurrence for the next order-4 head shape
`BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]`.  The keep-root cuts
collapse to four trunk shapes with binomial multiplicities. -/
private theorem forestSum_cons_node_triple_leaf_compact
    (α β : AugSeries) (cs : List BTree) :
    forestSum α.toFun β
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: cs)
      = α.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
          * forestSum α.toFun β cs
        + α.toFun BTree.leaf ^ 3
          * forestSum α.toFun (β.shiftBy (BTree.node [])) cs
        + 3 * α.toFun BTree.leaf ^ 2
          * forestSum α.toFun (β.shiftBy (BTree.node [BTree.leaf])) cs
        + 3 * α.toFun BTree.leaf
          * forestSum α.toFun
              (β.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) cs
        + forestSum α.toFun
            (β.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) cs := by
  simp only [forestSum]
  have hscale : ∀ (k : ℝ) (T : BTree),
      (List.map
          (fun forest =>
            k * forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node (T :: forest.filterMap (fun e => e.1))))
          (BTree.innerCutForest cs α.toFun)).sum
        = k * (List.map
            (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun
                    (BTree.node (T :: forest.filterMap (fun e => e.1))))
            (BTree.innerCutForest cs α.toFun)).sum := by
    intro k T
    induction BTree.innerCutForest cs α.toFun with
    | nil => simp
    | cons forest tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  rw [bSeriesConvAug_innerForest_cons]
  have hcut :
      (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]).innerCut α.toFun =
        [(none, α.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])),
         (some (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]), 1),
         (some (BTree.node [BTree.leaf, BTree.leaf]), α.toFun BTree.leaf),
         (some (BTree.node [BTree.leaf, BTree.leaf]), α.toFun BTree.leaf),
         (some (BTree.node [BTree.leaf]), α.toFun BTree.leaf * α.toFun BTree.leaf),
         (some (BTree.node [BTree.leaf, BTree.leaf]), α.toFun BTree.leaf),
         (some (BTree.node [BTree.leaf]), α.toFun BTree.leaf * α.toFun BTree.leaf),
         (some (BTree.node [BTree.leaf]), α.toFun BTree.leaf * α.toFun BTree.leaf),
         (some (BTree.node []),
            α.toFun BTree.leaf
              * (α.toFun BTree.leaf * α.toFun BTree.leaf))] := by
    simp [BTree.innerCut, BTree.innerCutForest]
  rw [hcut]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, List.sum_append, one_mul, AugSeries.shiftBy_node]
  rw [hscale
        (α.toFun BTree.leaf
          * (α.toFun BTree.leaf * α.toFun BTree.leaf)) (BTree.node []),
      hscale (α.toFun BTree.leaf * α.toFun BTree.leaf)
        (BTree.node [BTree.leaf]),
      hscale (α.toFun BTree.leaf)
        (BTree.node [BTree.leaf, BTree.leaf])]
  ring

/-- Pointwise expansion of `bSeriesConvAug β γ` at a cons whose head is the
order-4 triple-leaf shape `BTree.node [leaf, leaf, leaf]`. -/
private lemma bSeriesConvAug_node_cons_node_triple_leaf_expand_compact
    (β γ : AugSeries) (xs : List BTree) :
    bSeriesConvAug β γ
        (BTree.node (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: xs))
      = β.toFun
            (BTree.node
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: xs))
          * γ.emptyVal
        + β.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
          * forestSum β.toFun γ xs
        + β.toFun BTree.leaf ^ 3
          * forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
        + 3 * β.toFun BTree.leaf ^ 2
          * forestSum β.toFun (γ.shiftBy (BTree.node [BTree.leaf])) xs
        + 3 * β.toFun BTree.leaf
          * forestSum β.toFun
              (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) xs
        + forestSum β.toFun
            (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) xs := by
  rw [bSeriesConvAug_node β γ
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: xs)]
  change β.toFun
          (BTree.node
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: xs))
        * γ.emptyVal
      + forestSum β.toFun γ
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: xs)
      = β.toFun
            (BTree.node
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: xs))
          * γ.emptyVal
        + β.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
          * forestSum β.toFun γ xs
        + β.toFun BTree.leaf ^ 3
          * forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
        + 3 * β.toFun BTree.leaf ^ 2
          * forestSum β.toFun (γ.shiftBy (BTree.node [BTree.leaf])) xs
        + 3 * β.toFun BTree.leaf
          * forestSum β.toFun
              (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) xs
        + forestSum β.toFun
            (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) xs
  rw [forestSum_cons_node_triple_leaf_compact β γ xs]
  ring

/-- Aggregate shift identity for the depth-3 pair head `node [a, b]`.
This packages the pointwise pair expansion so the future depth-3 forest
induction can treat it as a single head case. -/
private theorem shift_pair_agg
    (α β γ : AugSeries) (a b : BTree) (ha : a.order ≤ 1) (hb : b.order ≤ 1)
    (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum α.toFun
        ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
          (BTree.node [a, b])) cs
      = forestSum α.toFun (β.shiftBy (BTree.node [a, b])) cs * γ.emptyVal
        + β.toFun (BTree.node [a, b])
          * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + β.toFun a * β.toFun b
          * forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [])) cs
        + β.toFun b
          * forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [a])) cs
        + β.toFun a
          * forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [b])) cs
        + forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [a, b])) cs := by
  have hih_γ := hih γ
  have hih_γn := hih (γ.shiftBy (BTree.node []))
  have hih_γa := hih (γ.shiftBy (BTree.node [a]))
  have hih_γb := hih (γ.shiftBy (BTree.node [b]))
  have hih_γab := hih (γ.shiftBy (BTree.node [a, b]))
  have keyPt : ∀ xs : List BTree,
      bSeriesConvAug β γ (BTree.node (BTree.node [a, b] :: xs))
        = β.toFun (BTree.node (BTree.node [a, b] :: xs)) * γ.emptyVal
          + β.toFun (BTree.node [a, b])
            * (bSeriesConvAug β γ (BTree.node xs)
                - β.toFun (BTree.node xs) * γ.emptyVal)
          + β.toFun a * β.toFun b
            * (bSeriesConvAug β (γ.shiftBy (BTree.node [])) (BTree.node xs)
                - β.toFun (BTree.node xs)
                  * (γ.shiftBy (BTree.node [])).emptyVal)
          + β.toFun b
            * (bSeriesConvAug β (γ.shiftBy (BTree.node [a])) (BTree.node xs)
                - β.toFun (BTree.node xs)
                  * (γ.shiftBy (BTree.node [a])).emptyVal)
          + β.toFun a
            * (bSeriesConvAug β (γ.shiftBy (BTree.node [b])) (BTree.node xs)
                - β.toFun (BTree.node xs)
                  * (γ.shiftBy (BTree.node [b])).emptyVal)
          + (bSeriesConvAug β (γ.shiftBy (BTree.node [a, b])) (BTree.node xs)
              - β.toFun (BTree.node xs)
                * (γ.shiftBy (BTree.node [a, b])).emptyVal) := by
    intro xs
    have hS1 : forestSum β.toFun γ xs
        = bSeriesConvAug β γ (BTree.node xs)
            - β.toFun (BTree.node xs) * γ.emptyVal := by
      rw [bSeriesConvAug_node β γ xs]
      change forestSum β.toFun γ xs
          = β.toFun (BTree.node xs) * γ.emptyVal
            + forestSum β.toFun γ xs
            - β.toFun (BTree.node xs) * γ.emptyVal
      ring
    have hS2 : forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
        = bSeriesConvAug β (γ.shiftBy (BTree.node [])) (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
          = β.toFun (BTree.node xs) * (γ.shiftBy (BTree.node [])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [])).emptyVal
      ring
    have hS3 : forestSum β.toFun (γ.shiftBy (BTree.node [a])) xs
        = bSeriesConvAug β (γ.shiftBy (BTree.node [a])) (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [a])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [a])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [a])) xs
          = β.toFun (BTree.node xs) * (γ.shiftBy (BTree.node [a])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [a])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [a])).emptyVal
      ring
    have hS4 : forestSum β.toFun (γ.shiftBy (BTree.node [b])) xs
        = bSeriesConvAug β (γ.shiftBy (BTree.node [b])) (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [b])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [b])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [b])) xs
          = β.toFun (BTree.node xs) * (γ.shiftBy (BTree.node [b])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [b])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [b])).emptyVal
      ring
    have hS5 : forestSum β.toFun (γ.shiftBy (BTree.node [a, b])) xs
        = bSeriesConvAug β (γ.shiftBy (BTree.node [a, b])) (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [a, b])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [a, b])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [a, b])) xs
          = β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [a, b])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [a, b])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [a, b])).emptyVal
      ring
    rw [bSeriesConvAug_node_cons_node_pair_depth_one_expand_compact
      β γ a b ha hb xs, hS1, hS2, hS3, hS4, hS5]
  have aux : ∀ (L : List (List (Option BTree × ℝ))),
      (L.map (fun forest =>
          forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
            * bSeriesConvAug β γ
                (BTree.node
                  (BTree.node [a, b] :: forest.filterMap (fun e => e.1))))).sum
        = (L.map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node
                    (BTree.node [a, b] :: forest.filterMap (fun e => e.1))))).sum
            * γ.emptyVal
          + β.toFun (BTree.node [a, b])
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β γ
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * γ.emptyVal)
          + β.toFun a * β.toFun b
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β (γ.shiftBy (BTree.node []))
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * (γ.shiftBy (BTree.node [])).emptyVal)
          + β.toFun b
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β (γ.shiftBy (BTree.node [a]))
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * (γ.shiftBy (BTree.node [a])).emptyVal)
          + β.toFun a
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β (γ.shiftBy (BTree.node [b]))
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * (γ.shiftBy (BTree.node [b])).emptyVal)
          + ((L.map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * bSeriesConvAug β (γ.shiftBy (BTree.node [a, b]))
                    (BTree.node (forest.filterMap (fun e => e.1))))).sum
            - (L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * β.toFun
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
                * (γ.shiftBy (BTree.node [a, b])).emptyVal) := by
    intro L
    induction L with
    | nil => simp
    | cons fhd ftl ihL =>
      simp only [List.map_cons, List.sum_cons, ihL]
      rw [keyPt (fhd.filterMap (fun e => e.1))]
      ring
  change ((BTree.innerCutForest cs α.toFun).map (fun forest =>
      forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
        * bSeriesConvAug β γ
            (BTree.node
              (BTree.node [a, b] :: forest.filterMap (fun e => e.1))))).sum
    = forestSum α.toFun (β.shiftBy (BTree.node [a, b])) cs * γ.emptyVal
      + β.toFun (BTree.node [a, b])
        * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
      + β.toFun a * β.toFun b
        * forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [])) cs
      + β.toFun b
        * forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [a])) cs
      + β.toFun a
        * forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [b])) cs
      + forestSum (fun σ => bSeriesConvAug α β σ)
        (γ.shiftBy (BTree.node [a, b])) cs
  rw [aux (BTree.innerCutForest cs α.toFun)]
  simp only [forestSum, AugSeries.shiftBy_node] at hih_γ hih_γn hih_γa hih_γb hih_γab ⊢
  linear_combination -β.toFun (BTree.node [a, b]) * hih_γ
    - (β.toFun a * β.toFun b) * hih_γn
    - β.toFun b * hih_γa - β.toFun a * hih_γb - hih_γab

/-- Aggregate shift identity for the depth-3 singleton-of-singleton head
`node [node [e]]`. -/
private theorem shift_singleton_node_singleton_agg
    (α β γ : AugSeries) (e : BTree) (he : e.order ≤ 1)
    (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum α.toFun
        ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
          (BTree.node [BTree.node [e]])) cs
      = forestSum α.toFun (β.shiftBy (BTree.node [BTree.node [e]])) cs
          * γ.emptyVal
        + β.toFun (BTree.node [BTree.node [e]])
          * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + β.toFun (BTree.node [e])
          * forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [])) cs
        + β.toFun e
          * forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [BTree.node []])) cs
        + forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [BTree.node [e]])) cs := by
  have hih_γ := hih γ
  have hih_γn := hih (γ.shiftBy (BTree.node []))
  have hih_γnn := hih (γ.shiftBy (BTree.node [BTree.node []]))
  have hih_γnne := hih (γ.shiftBy (BTree.node [BTree.node [e]]))
  have keyPt : ∀ xs : List BTree,
      bSeriesConvAug β γ (BTree.node (BTree.node [BTree.node [e]] :: xs))
        = β.toFun (BTree.node (BTree.node [BTree.node [e]] :: xs))
            * γ.emptyVal
          + β.toFun (BTree.node [BTree.node [e]])
            * (bSeriesConvAug β γ (BTree.node xs)
                - β.toFun (BTree.node xs) * γ.emptyVal)
          + β.toFun (BTree.node [e])
            * (bSeriesConvAug β (γ.shiftBy (BTree.node [])) (BTree.node xs)
                - β.toFun (BTree.node xs)
                  * (γ.shiftBy (BTree.node [])).emptyVal)
          + β.toFun e
            * (bSeriesConvAug β (γ.shiftBy (BTree.node [BTree.node []]))
                (BTree.node xs)
                - β.toFun (BTree.node xs)
                  * (γ.shiftBy (BTree.node [BTree.node []])).emptyVal)
          + (bSeriesConvAug β (γ.shiftBy (BTree.node [BTree.node [e]]))
              (BTree.node xs)
              - β.toFun (BTree.node xs)
                * (γ.shiftBy (BTree.node [BTree.node [e]])).emptyVal) := by
    intro xs
    have hS1 : forestSum β.toFun γ xs
        = bSeriesConvAug β γ (BTree.node xs)
            - β.toFun (BTree.node xs) * γ.emptyVal := by
      rw [bSeriesConvAug_node β γ xs]
      change forestSum β.toFun γ xs
          = β.toFun (BTree.node xs) * γ.emptyVal
            + forestSum β.toFun γ xs
            - β.toFun (BTree.node xs) * γ.emptyVal
      ring
    have hS2 : forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
        = bSeriesConvAug β (γ.shiftBy (BTree.node [])) (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
          = β.toFun (BTree.node xs) * (γ.shiftBy (BTree.node [])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [])).emptyVal
      ring
    have hS3 :
        forestSum β.toFun (γ.shiftBy (BTree.node [BTree.node []])) xs
          = bSeriesConvAug β (γ.shiftBy (BTree.node [BTree.node []]))
              (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [BTree.node []])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [BTree.node []])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [BTree.node []])) xs
          = β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [BTree.node []])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [BTree.node []])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [BTree.node []])).emptyVal
      ring
    have hS4 :
        forestSum β.toFun (γ.shiftBy (BTree.node [BTree.node [e]])) xs
          = bSeriesConvAug β (γ.shiftBy (BTree.node [BTree.node [e]]))
              (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [BTree.node [e]])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [BTree.node [e]])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [BTree.node [e]])) xs
          = β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [BTree.node [e]])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [BTree.node [e]])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [BTree.node [e]])).emptyVal
      ring
    rw [bSeriesConvAug_node_cons_node_singleton_node_singleton_depth_one_expand_compact
      β γ e he xs, hS1, hS2, hS3, hS4]
  have aux : ∀ (L : List (List (Option BTree × ℝ))),
      (L.map (fun forest =>
          forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
            * bSeriesConvAug β γ
                (BTree.node
                  (BTree.node [BTree.node [e]]
                    :: forest.filterMap (fun ec => ec.1))))).sum
        = (L.map (fun forest =>
            forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node
                    (BTree.node [BTree.node [e]]
                      :: forest.filterMap (fun ec => ec.1))))).sum
            * γ.emptyVal
          + β.toFun (BTree.node [BTree.node [e]])
            * ((L.map (fun forest =>
                forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β γ
                      (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
                  * γ.emptyVal)
          + β.toFun (BTree.node [e])
            * ((L.map (fun forest =>
                forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β (γ.shiftBy (BTree.node []))
                      (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
                  * (γ.shiftBy (BTree.node [])).emptyVal)
          + β.toFun e
            * ((L.map (fun forest =>
                forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β (γ.shiftBy (BTree.node [BTree.node []]))
                      (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
                  * (γ.shiftBy (BTree.node [BTree.node []])).emptyVal)
          + ((L.map (fun forest =>
              forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                * bSeriesConvAug β (γ.shiftBy (BTree.node [BTree.node [e]]))
                    (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
            - (L.map (fun forest =>
                forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
                  * β.toFun
                      (BTree.node (forest.filterMap (fun ec => ec.1))))).sum
                * (γ.shiftBy (BTree.node [BTree.node [e]])).emptyVal) := by
    intro L
    induction L with
    | nil => simp
    | cons fhd ftl ihL =>
      simp only [List.map_cons, List.sum_cons, ihL]
      rw [keyPt (fhd.filterMap (fun ec => ec.1))]
      ring
  change ((BTree.innerCutForest cs α.toFun).map (fun forest =>
      forest.foldr (fun ec acc => ec.2 * acc) (1 : ℝ)
        * bSeriesConvAug β γ
            (BTree.node
              (BTree.node [BTree.node [e]]
                :: forest.filterMap (fun ec => ec.1))))).sum
    = forestSum α.toFun (β.shiftBy (BTree.node [BTree.node [e]])) cs
        * γ.emptyVal
      + β.toFun (BTree.node [BTree.node [e]])
        * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
      + β.toFun (BTree.node [e])
        * forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [])) cs
      + β.toFun e
        * forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [BTree.node []])) cs
      + forestSum (fun σ => bSeriesConvAug α β σ)
        (γ.shiftBy (BTree.node [BTree.node [e]])) cs
  rw [aux (BTree.innerCutForest cs α.toFun)]
  simp only [forestSum, AugSeries.shiftBy_node] at hih_γ hih_γn hih_γnn hih_γnne ⊢
  linear_combination -β.toFun (BTree.node [BTree.node [e]]) * hih_γ
    - β.toFun (BTree.node [e]) * hih_γn - β.toFun e * hih_γnn - hih_γnne

/-! ## Cycle 602: depth-3 mixed-children associativity headline -/

/-- Aggregate shift identity for a head of order ≤ 1 (top-level form
mirroring the cycle 599 `shift_depth_one_agg` inline lemma, but
parameterised by an explicit tail-IH). -/
private theorem shift_one_agg
    (α β γ : AugSeries) (m : BTree) (hm : m.order ≤ 1)
    (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum α.toFun
        ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy m) cs
      = forestSum α.toFun (β.shiftBy m) cs * γ.emptyVal
        + β.toFun m * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + forestSum (fun σ => bSeriesConvAug α β σ) (γ.shiftBy m) cs := by
  have hih_γ := hih γ
  have hih_γm := hih (γ.shiftBy m)
  have keyPt : ∀ xs : List BTree,
      bSeriesConvAug β γ (BTree.node (m :: xs))
        = β.toFun (BTree.node (m :: xs)) * γ.emptyVal
          + β.toFun m
            * (bSeriesConvAug β γ (BTree.node xs)
                - β.toFun (BTree.node xs) * γ.emptyVal)
          + (bSeriesConvAug β (γ.shiftBy m) (BTree.node xs)
              - β.toFun (BTree.node xs) * (γ.shiftBy m).emptyVal) := by
    intro xs
    have hS1 : forestSum β.toFun γ xs
        = bSeriesConvAug β γ (BTree.node xs)
            - β.toFun (BTree.node xs) * γ.emptyVal := by
      rw [bSeriesConvAug_node β γ xs]
      change forestSum β.toFun γ xs
          = β.toFun (BTree.node xs) * γ.emptyVal
            + forestSum β.toFun γ xs
            - β.toFun (BTree.node xs) * γ.emptyVal
      ring
    have hS2 : forestSum β.toFun (γ.shiftBy m) xs
        = bSeriesConvAug β (γ.shiftBy m) (BTree.node xs)
            - β.toFun (BTree.node xs) * (γ.shiftBy m).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy m) xs]
      change forestSum β.toFun (γ.shiftBy m) xs
          = β.toFun (BTree.node xs) * (γ.shiftBy m).emptyVal
            + forestSum β.toFun (γ.shiftBy m) xs
            - β.toFun (BTree.node xs) * (γ.shiftBy m).emptyVal
      ring
    rw [bSeriesConvAug_node_cons_depth_one_expand_compact β γ m hm xs,
      hS1, hS2]
  have aux : ∀ (L : List (List (Option BTree × ℝ))),
      (L.map (fun forest =>
          forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
            * bSeriesConvAug β γ
                (BTree.node (m :: forest.filterMap (fun e => e.1))))).sum
        = (L.map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node (m :: forest.filterMap (fun e => e.1))))).sum
            * γ.emptyVal
          + β.toFun m
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β γ
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * γ.emptyVal)
          + ((L.map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * bSeriesConvAug β (γ.shiftBy m)
                    (BTree.node (forest.filterMap (fun e => e.1))))).sum
            - (L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * β.toFun
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
                * (γ.shiftBy m).emptyVal) := by
    intro L
    induction L with
    | nil => simp
    | cons fhd ftl ihL =>
      simp only [List.map_cons, List.sum_cons, ihL]
      rw [keyPt (fhd.filterMap (fun e => e.1))]
      ring
  change ((BTree.innerCutForest cs α.toFun).map (fun forest =>
      forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
        * bSeriesConvAug β γ
            (BTree.node (m :: forest.filterMap (fun e => e.1))))).sum
    = forestSum α.toFun (β.shiftBy m) cs * γ.emptyVal
      + β.toFun m * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
      + forestSum (fun σ => bSeriesConvAug α β σ) (γ.shiftBy m) cs
  rw [aux (BTree.innerCutForest cs α.toFun)]
  simp only [forestSum, AugSeries.shiftBy_node] at hih_γ hih_γm ⊢
  linear_combination -β.toFun m * hih_γ - hih_γm

/-- Aggregate shift identity for a singleton head `node [d]` with
`d` of order ≤ 1 (top-level form of cycle 599's inline
`shift_singleton_agg`, parameterised by an explicit tail-IH). -/
private theorem shift_node_singleton_agg
    (α β γ : AugSeries) (d : BTree) (hd : d.order ≤ 1)
    (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum α.toFun
        ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
          (BTree.node [d])) cs
      = forestSum α.toFun (β.shiftBy (BTree.node [d])) cs * γ.emptyVal
        + β.toFun (BTree.node [d])
          * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + β.toFun d
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [])) cs
        + forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [d])) cs := by
  have hih_γ := hih γ
  have hih_γn := hih (γ.shiftBy (BTree.node []))
  have hih_γd := hih (γ.shiftBy (BTree.node [d]))
  have keyPt : ∀ xs : List BTree,
      bSeriesConvAug β γ (BTree.node (BTree.node [d] :: xs))
        = β.toFun (BTree.node (BTree.node [d] :: xs)) * γ.emptyVal
          + β.toFun (BTree.node [d])
            * (bSeriesConvAug β γ (BTree.node xs)
                - β.toFun (BTree.node xs) * γ.emptyVal)
          + β.toFun d
            * (bSeriesConvAug β (γ.shiftBy (BTree.node [])) (BTree.node xs)
                - β.toFun (BTree.node xs)
                  * (γ.shiftBy (BTree.node [])).emptyVal)
          + (bSeriesConvAug β (γ.shiftBy (BTree.node [d])) (BTree.node xs)
              - β.toFun (BTree.node xs)
                * (γ.shiftBy (BTree.node [d])).emptyVal) := by
    intro xs
    have hS1 : forestSum β.toFun γ xs
        = bSeriesConvAug β γ (BTree.node xs)
            - β.toFun (BTree.node xs) * γ.emptyVal := by
      rw [bSeriesConvAug_node β γ xs]
      change forestSum β.toFun γ xs
          = β.toFun (BTree.node xs) * γ.emptyVal
            + forestSum β.toFun γ xs
            - β.toFun (BTree.node xs) * γ.emptyVal
      ring
    have hS2 : forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
        = bSeriesConvAug β (γ.shiftBy (BTree.node [])) (BTree.node xs)
            - β.toFun (BTree.node xs)
                * (γ.shiftBy (BTree.node [])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
          = β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [])).emptyVal
      ring
    have hS3 : forestSum β.toFun (γ.shiftBy (BTree.node [d])) xs
        = bSeriesConvAug β (γ.shiftBy (BTree.node [d])) (BTree.node xs)
            - β.toFun (BTree.node xs)
                * (γ.shiftBy (BTree.node [d])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [d])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [d])) xs
          = β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [d])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [d])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [d])).emptyVal
      ring
    rw [bSeriesConvAug_node_cons_node_singleton_depth_one_expand_compact
      β γ d hd xs, hS1, hS2, hS3]
  have aux : ∀ (L : List (List (Option BTree × ℝ))),
      (L.map (fun forest =>
          forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
            * bSeriesConvAug β γ
                (BTree.node
                  (BTree.node [d] :: forest.filterMap (fun e => e.1))))).sum
        = (L.map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node
                    (BTree.node [d] :: forest.filterMap (fun e => e.1))))).sum
            * γ.emptyVal
          + β.toFun (BTree.node [d])
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β γ
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * γ.emptyVal)
          + β.toFun d
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β (γ.shiftBy (BTree.node []))
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * (γ.shiftBy (BTree.node [])).emptyVal)
          + ((L.map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * bSeriesConvAug β (γ.shiftBy (BTree.node [d]))
                    (BTree.node (forest.filterMap (fun e => e.1))))).sum
            - (L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * β.toFun
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
                * (γ.shiftBy (BTree.node [d])).emptyVal) := by
    intro L
    induction L with
    | nil => simp
    | cons fhd ftl ihL =>
      simp only [List.map_cons, List.sum_cons, ihL]
      rw [keyPt (fhd.filterMap (fun e => e.1))]
      ring
  change ((BTree.innerCutForest cs α.toFun).map (fun forest =>
      forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
        * bSeriesConvAug β γ
            (BTree.node
              (BTree.node [d] :: forest.filterMap (fun e => e.1))))).sum
    = forestSum α.toFun (β.shiftBy (BTree.node [d])) cs * γ.emptyVal
      + β.toFun (BTree.node [d])
        * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
      + β.toFun d
        * forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [])) cs
      + forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [d])) cs
  rw [aux (BTree.innerCutForest cs α.toFun)]
  simp only [forestSum, AugSeries.shiftBy_node] at hih_γ hih_γn hih_γd ⊢
  linear_combination -β.toFun (BTree.node [d]) * hih_γ
    - β.toFun d * hih_γn - hih_γd

/-! ## Cycle 605: add the triple-leaf order-4 head shape -/

/-- Aggregate shift identity for the order-4 triple-leaf head
`node [leaf, leaf, leaf]`. -/
private theorem shift_triple_leaf_agg
    (α β γ : AugSeries) (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum α.toFun
        ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) cs
      = forestSum α.toFun
          (β.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) cs
          * γ.emptyVal
        + β.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
          * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + β.toFun BTree.leaf ^ 3
          * forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [])) cs
        + 3 * β.toFun BTree.leaf ^ 2
          * forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [BTree.leaf])) cs
        + 3 * β.toFun BTree.leaf
          * forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) cs
        + forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) cs := by
  have hih_γ := hih γ
  have hih_γn := hih (γ.shiftBy (BTree.node []))
  have hih_γl := hih (γ.shiftBy (BTree.node [BTree.leaf]))
  have hih_γll := hih (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf]))
  have hih_γlll :=
    hih (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))
  have keyPt : ∀ xs : List BTree,
      bSeriesConvAug β γ
          (BTree.node
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: xs))
        = β.toFun
            (BTree.node
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: xs))
            * γ.emptyVal
          + β.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
            * (bSeriesConvAug β γ (BTree.node xs)
                - β.toFun (BTree.node xs) * γ.emptyVal)
          + β.toFun BTree.leaf ^ 3
            * (bSeriesConvAug β (γ.shiftBy (BTree.node [])) (BTree.node xs)
                - β.toFun (BTree.node xs)
                  * (γ.shiftBy (BTree.node [])).emptyVal)
          + 3 * β.toFun BTree.leaf ^ 2
            * (bSeriesConvAug β (γ.shiftBy (BTree.node [BTree.leaf]))
                (BTree.node xs)
                - β.toFun (BTree.node xs)
                  * (γ.shiftBy (BTree.node [BTree.leaf])).emptyVal)
          + 3 * β.toFun BTree.leaf
            * (bSeriesConvAug β
                (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf]))
                (BTree.node xs)
                - β.toFun (BTree.node xs)
                  * (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])).emptyVal)
          + (bSeriesConvAug β
              (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))
              (BTree.node xs)
              - β.toFun (BTree.node xs)
                * (γ.shiftBy
                    (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).emptyVal) := by
    intro xs
    have hS1 : forestSum β.toFun γ xs
        = bSeriesConvAug β γ (BTree.node xs)
            - β.toFun (BTree.node xs) * γ.emptyVal := by
      rw [bSeriesConvAug_node β γ xs]
      change forestSum β.toFun γ xs
          = β.toFun (BTree.node xs) * γ.emptyVal
            + forestSum β.toFun γ xs
            - β.toFun (BTree.node xs) * γ.emptyVal
      ring
    have hS2 : forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
        = bSeriesConvAug β (γ.shiftBy (BTree.node [])) (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
          = β.toFun (BTree.node xs) * (γ.shiftBy (BTree.node [])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [])).emptyVal
      ring
    have hS3 :
        forestSum β.toFun (γ.shiftBy (BTree.node [BTree.leaf])) xs
          = bSeriesConvAug β (γ.shiftBy (BTree.node [BTree.leaf]))
              (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [BTree.leaf])).emptyVal := by
      rw [bSeriesConvAug_node β (γ.shiftBy (BTree.node [BTree.leaf])) xs]
      change forestSum β.toFun (γ.shiftBy (BTree.node [BTree.leaf])) xs
          = β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [BTree.leaf])).emptyVal
            + forestSum β.toFun (γ.shiftBy (BTree.node [BTree.leaf])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy (BTree.node [BTree.leaf])).emptyVal
      ring
    have hS4 :
        forestSum β.toFun
            (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) xs
          = bSeriesConvAug β
              (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf]))
              (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy
                  (BTree.node [BTree.leaf, BTree.leaf])).emptyVal := by
      rw [bSeriesConvAug_node β
        (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) xs]
      change forestSum β.toFun
            (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) xs
          = β.toFun (BTree.node xs)
              * (γ.shiftBy
                  (BTree.node [BTree.leaf, BTree.leaf])).emptyVal
            + forestSum β.toFun
                (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy
                  (BTree.node [BTree.leaf, BTree.leaf])).emptyVal
      ring
    have hS5 :
        forestSum β.toFun
            (γ.shiftBy
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) xs
          = bSeriesConvAug β
              (γ.shiftBy
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))
              (BTree.node xs)
            - β.toFun (BTree.node xs)
              * (γ.shiftBy
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).emptyVal := by
      rw [bSeriesConvAug_node β
        (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) xs]
      change forestSum β.toFun
            (γ.shiftBy
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) xs
          = β.toFun (BTree.node xs)
              * (γ.shiftBy
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).emptyVal
            + forestSum β.toFun
                (γ.shiftBy
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) xs
            - β.toFun (BTree.node xs)
              * (γ.shiftBy
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).emptyVal
      ring
    rw [bSeriesConvAug_node_cons_node_triple_leaf_expand_compact β γ xs,
      hS1, hS2, hS3, hS4, hS5]
  have aux : ∀ (L : List (List (Option BTree × ℝ))),
      (L.map (fun forest =>
          forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
            * bSeriesConvAug β γ
                (BTree.node
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]
                    :: forest.filterMap (fun e => e.1))))).sum
        = (L.map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node
                    (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]
                      :: forest.filterMap (fun e => e.1))))).sum
            * γ.emptyVal
          + β.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β γ
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * γ.emptyVal)
          + β.toFun BTree.leaf ^ 3
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β (γ.shiftBy (BTree.node []))
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * (γ.shiftBy (BTree.node [])).emptyVal)
          + 3 * β.toFun BTree.leaf ^ 2
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β (γ.shiftBy (BTree.node [BTree.leaf]))
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * (γ.shiftBy (BTree.node [BTree.leaf])).emptyVal)
          + 3 * β.toFun BTree.leaf
            * ((L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * bSeriesConvAug β
                      (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf]))
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * (γ.shiftBy
                      (BTree.node [BTree.leaf, BTree.leaf])).emptyVal)
          + ((L.map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * bSeriesConvAug β
                    (γ.shiftBy
                      (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))
                    (BTree.node (forest.filterMap (fun e => e.1))))).sum
            - (L.map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * β.toFun
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
                * (γ.shiftBy
                    (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).emptyVal) := by
    intro L
    induction L with
    | nil => simp
    | cons fhd ftl ihL =>
      simp only [List.map_cons, List.sum_cons, ihL]
      rw [keyPt (fhd.filterMap (fun e => e.1))]
      ring
  change ((BTree.innerCutForest cs α.toFun).map (fun forest =>
      forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
        * bSeriesConvAug β γ
            (BTree.node
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]
                :: forest.filterMap (fun e => e.1))))).sum
    = forestSum α.toFun
        (β.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) cs
        * γ.emptyVal
      + β.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
        * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
      + β.toFun BTree.leaf ^ 3
        * forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [])) cs
      + 3 * β.toFun BTree.leaf ^ 2
        * forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [BTree.leaf])) cs
      + 3 * β.toFun BTree.leaf
        * forestSum (fun σ => bSeriesConvAug α β σ)
          (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) cs
      + forestSum (fun σ => bSeriesConvAug α β σ)
        (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) cs
  rw [aux (BTree.innerCutForest cs α.toFun)]
  simp only [forestSum, AugSeries.shiftBy_node] at hih_γ hih_γn hih_γl hih_γll hih_γlll ⊢
  linear_combination
    -β.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) * hih_γ
    - β.toFun BTree.leaf ^ 3 * hih_γn
    - (3 * β.toFun BTree.leaf ^ 2) * hih_γl
    - (3 * β.toFun BTree.leaf) * hih_γll
    - hih_γlll

/-- Head case for `forestSum_assoc_depth_three` when the head child has
order ≤ 1 (i.e. is `BTree.leaf` or `BTree.node []`). -/
private theorem forestSum_assoc_three_one_head
    (α β γ : AugSeries) (hβ : β.IsUnital) (m : BTree) (hm : m.order ≤ 1)
    (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum (fun σ => bSeriesConvAug α β σ) γ (m :: cs)
      + forestSum α.toFun β (m :: cs) * γ.emptyVal
    = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩ (m :: cs) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hih_γ := hih γ
  have hgβ_m : bSeriesConvAug α β m = α.toFun m + β.toFun m := by
    rcases (order_le_one_iff m).mp hm with rfl | rfl
    · rw [bSeriesConvAug_leaf, hβ']; ring
    · rw [bSeriesConvAug_node_nil, hβ']; ring
  rw [forestSum_cons_depth_one_compact
        ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ m hm cs,
      forestSum_cons_depth_one_compact α β m hm cs,
      forestSum_cons_depth_one_compact
        α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ m hm cs]
  change bSeriesConvAug α β m
          * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + forestSum (fun σ => bSeriesConvAug α β σ) (γ.shiftBy m) cs
        + (α.toFun m * forestSum α.toFun β cs
            + forestSum α.toFun (β.shiftBy m) cs) * γ.emptyVal
      = α.toFun m
          * forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩ cs
        + forestSum α.toFun
            ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy m) cs
  rw [hgβ_m, shift_one_agg α β γ m hm cs hih]
  linear_combination α.toFun m * hih_γ

/-- Head case for `forestSum_assoc_depth_three` when the head child is
`BTree.node [d]` with `d` of order ≤ 1. -/
private theorem forestSum_assoc_three_singleton_head
    (α β γ : AugSeries) (hβ : β.IsUnital) (d : BTree) (hd : d.order ≤ 1)
    (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum (fun σ => bSeriesConvAug α β σ) γ (BTree.node [d] :: cs)
      + forestSum α.toFun β (BTree.node [d] :: cs) * γ.emptyVal
    = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩
        (BTree.node [d] :: cs) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hih_γ := hih γ
  have hgβ_d : bSeriesConvAug α β d = α.toFun d + β.toFun d := by
    rcases (order_le_one_iff d).mp hd with rfl | rfl
    · rw [bSeriesConvAug_leaf, hβ']; ring
    · rw [bSeriesConvAug_node_nil, hβ']; ring
  have hgβ_node :
      bSeriesConvAug α β (BTree.node [d])
        = α.toFun (BTree.node [d])
          + α.toFun d * β.toFun (BTree.node [])
          + β.toFun (BTree.node [d]) := by
    rw [bSeriesConvAug_node_cons_depth_one_expand_compact α β d hd []]
    simp [forestSum, BTree.innerCutForest, hβ']
  rw [forestSum_cons_node_singleton_depth_one_compact
        ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ d hd cs,
      forestSum_cons_node_singleton_depth_one_compact α β d hd cs,
      forestSum_cons_node_singleton_depth_one_compact
        α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ d hd cs]
  change bSeriesConvAug α β (BTree.node [d])
          * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + bSeriesConvAug α β d
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [])) cs
        + forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [d])) cs
        + (α.toFun (BTree.node [d]) * forestSum α.toFun β cs
              + α.toFun d
                * forestSum α.toFun (β.shiftBy (BTree.node [])) cs
              + forestSum α.toFun (β.shiftBy (BTree.node [d])) cs)
            * γ.emptyVal
      = α.toFun (BTree.node [d])
          * forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩ cs
        + α.toFun d
          * forestSum α.toFun
              ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
                (BTree.node [])) cs
        + forestSum α.toFun
            ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
              (BTree.node [d])) cs
  rw [hgβ_node, hgβ_d,
      shift_one_agg α β γ (BTree.node []) (by simp) cs hih,
      shift_node_singleton_agg α β γ d hd cs hih]
  linear_combination α.toFun (BTree.node [d]) * hih_γ

/-- Head case for `forestSum_assoc_depth_three` when the head child is
`BTree.node [a, b]` with `a, b` of order ≤ 1. -/
private theorem forestSum_assoc_three_pair_head
    (α β γ : AugSeries) (hβ : β.IsUnital)
    (a b : BTree) (ha : a.order ≤ 1) (hb : b.order ≤ 1)
    (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum (fun σ => bSeriesConvAug α β σ) γ (BTree.node [a, b] :: cs)
      + forestSum α.toFun β (BTree.node [a, b] :: cs) * γ.emptyVal
    = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩
        (BTree.node [a, b] :: cs) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hih_γ := hih γ
  have hgβ_a : bSeriesConvAug α β a = α.toFun a + β.toFun a := by
    rcases (order_le_one_iff a).mp ha with rfl | rfl
    · rw [bSeriesConvAug_leaf, hβ']; ring
    · rw [bSeriesConvAug_node_nil, hβ']; ring
  have hgβ_b : bSeriesConvAug α β b = α.toFun b + β.toFun b := by
    rcases (order_le_one_iff b).mp hb with rfl | rfl
    · rw [bSeriesConvAug_leaf, hβ']; ring
    · rw [bSeriesConvAug_node_nil, hβ']; ring
  have hgβ_pair :
      bSeriesConvAug α β (BTree.node [a, b])
        = α.toFun (BTree.node [a, b])
          + α.toFun a * α.toFun b * β.toFun (BTree.node [])
          + α.toFun b * β.toFun (BTree.node [a])
          + α.toFun a * β.toFun (BTree.node [b])
          + β.toFun (BTree.node [a, b]) := by
    rw [bSeriesConvAug_node_cons_depth_one_expand_compact α β a ha [b],
        forestSum_cons_depth_one_compact α β b hb [],
        forestSum_cons_depth_one_compact α (β.shiftBy a) b hb []]
    simp only [forestSum, BTree.innerCutForest, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.foldr_nil, List.filterMap_nil,
      one_mul, add_zero, AugSeries.shiftBy_node, hβ']
    ring
  rw [forestSum_cons_node_pair_depth_one_compact
        ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ a b ha hb cs,
      forestSum_cons_node_pair_depth_one_compact α β a b ha hb cs,
      forestSum_cons_node_pair_depth_one_compact
        α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ a b ha hb cs]
  change bSeriesConvAug α β (BTree.node [a, b])
          * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + bSeriesConvAug α β a * bSeriesConvAug α β b
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [])) cs
        + bSeriesConvAug α β b
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [a])) cs
        + bSeriesConvAug α β a
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [b])) cs
        + forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [a, b])) cs
        + (α.toFun (BTree.node [a, b]) * forestSum α.toFun β cs
              + α.toFun a * α.toFun b
                  * forestSum α.toFun (β.shiftBy (BTree.node [])) cs
              + α.toFun b
                  * forestSum α.toFun (β.shiftBy (BTree.node [a])) cs
              + α.toFun a
                  * forestSum α.toFun (β.shiftBy (BTree.node [b])) cs
              + forestSum α.toFun (β.shiftBy (BTree.node [a, b])) cs)
            * γ.emptyVal
      = α.toFun (BTree.node [a, b])
          * forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩ cs
        + α.toFun a * α.toFun b
          * forestSum α.toFun
              ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
                (BTree.node [])) cs
        + α.toFun b
          * forestSum α.toFun
              ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
                (BTree.node [a])) cs
        + α.toFun a
          * forestSum α.toFun
              ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
                (BTree.node [b])) cs
        + forestSum α.toFun
            ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
              (BTree.node [a, b])) cs
  rw [hgβ_pair, hgβ_a, hgβ_b,
      shift_one_agg α β γ (BTree.node []) (by simp) cs hih,
      shift_node_singleton_agg α β γ a ha cs hih,
      shift_node_singleton_agg α β γ b hb cs hih,
      shift_pair_agg α β γ a b ha hb cs hih]
  linear_combination α.toFun (BTree.node [a, b]) * hih_γ

/-- Head case for `forestSum_assoc_depth_three` when the head child is
`BTree.node [BTree.node [e]]` with `e` of order ≤ 1. -/
private theorem forestSum_assoc_three_singleton_node_singleton_head
    (α β γ : AugSeries) (hβ : β.IsUnital) (e : BTree) (he : e.order ≤ 1)
    (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum (fun σ => bSeriesConvAug α β σ) γ
        (BTree.node [BTree.node [e]] :: cs)
      + forestSum α.toFun β (BTree.node [BTree.node [e]] :: cs)
          * γ.emptyVal
    = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩
        (BTree.node [BTree.node [e]] :: cs) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hih_γ := hih γ
  have hgβ_e : bSeriesConvAug α β e = α.toFun e + β.toFun e := by
    rcases (order_le_one_iff e).mp he with rfl | rfl
    · rw [bSeriesConvAug_leaf, hβ']; ring
    · rw [bSeriesConvAug_node_nil, hβ']; ring
  have hgβ_inner :
      bSeriesConvAug α β (BTree.node [e])
        = α.toFun (BTree.node [e])
          + α.toFun e * β.toFun (BTree.node [])
          + β.toFun (BTree.node [e]) := by
    rw [bSeriesConvAug_node_cons_depth_one_expand_compact α β e he []]
    simp [forestSum, BTree.innerCutForest, hβ']
  have hgβ_outer :
      bSeriesConvAug α β (BTree.node [BTree.node [e]])
        = α.toFun (BTree.node [BTree.node [e]])
          + α.toFun (BTree.node [e]) * β.toFun (BTree.node [])
          + α.toFun e * β.toFun (BTree.node [BTree.node []])
          + β.toFun (BTree.node [BTree.node [e]]) := by
    rw [bSeriesConvAug_node_cons_node_singleton_depth_one_expand_compact
          α β e he []]
    simp [forestSum, BTree.innerCutForest, hβ']
  rw [forestSum_cons_node_singleton_node_singleton_depth_one_compact
        ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ e he cs,
      forestSum_cons_node_singleton_node_singleton_depth_one_compact
        α β e he cs,
      forestSum_cons_node_singleton_node_singleton_depth_one_compact
        α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ e he cs]
  change bSeriesConvAug α β (BTree.node [BTree.node [e]])
          * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + bSeriesConvAug α β (BTree.node [e])
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [])) cs
        + bSeriesConvAug α β e
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [BTree.node []])) cs
        + forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [BTree.node [e]])) cs
        + (α.toFun (BTree.node [BTree.node [e]])
              * forestSum α.toFun β cs
            + α.toFun (BTree.node [e])
                * forestSum α.toFun (β.shiftBy (BTree.node [])) cs
            + α.toFun e
                * forestSum α.toFun
                    (β.shiftBy (BTree.node [BTree.node []])) cs
            + forestSum α.toFun
                (β.shiftBy (BTree.node [BTree.node [e]])) cs)
            * γ.emptyVal
      = α.toFun (BTree.node [BTree.node [e]])
          * forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩ cs
        + α.toFun (BTree.node [e])
          * forestSum α.toFun
              ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
                (BTree.node [])) cs
        + α.toFun e
          * forestSum α.toFun
              ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
                (BTree.node [BTree.node []])) cs
        + forestSum α.toFun
            ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
              (BTree.node [BTree.node [e]])) cs
  rw [hgβ_outer, hgβ_inner, hgβ_e,
      shift_one_agg α β γ (BTree.node []) (by simp) cs hih,
      shift_node_singleton_agg α β γ (BTree.node []) (by simp) cs hih,
      shift_singleton_node_singleton_agg α β γ e he cs hih]
  linear_combination α.toFun (BTree.node [BTree.node [e]]) * hih_γ

/-- Head case for the new order-4 triple-leaf child
`BTree.node [leaf, leaf, leaf]`. -/
private theorem forestSum_assoc_three_triple_leaf_head
    (α β γ : AugSeries) (hβ : β.IsUnital) (cs : List BTree)
    (hih : ∀ δ : AugSeries,
      forestSum (fun σ => bSeriesConvAug α β σ) δ cs
        + forestSum α.toFun β cs * δ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs) :
    forestSum (fun σ => bSeriesConvAug α β σ) γ
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: cs)
      + forestSum α.toFun β
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: cs)
          * γ.emptyVal
    = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :: cs) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hih_γ := hih γ
  have hgβ_leaf :
      bSeriesConvAug α β BTree.leaf
        = α.toFun BTree.leaf + β.toFun BTree.leaf := by
    rw [bSeriesConvAug_leaf, hβ']
    ring
  have hgβ_triple :
      bSeriesConvAug α β
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
        = α.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
          + α.toFun BTree.leaf ^ 3 * β.toFun (BTree.node [])
          + 3 * α.toFun BTree.leaf ^ 2
              * β.toFun (BTree.node [BTree.leaf])
          + 3 * α.toFun BTree.leaf
              * β.toFun (BTree.node [BTree.leaf, BTree.leaf])
          + β.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) := by
    simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest, hβ']
    ring
  rw [forestSum_cons_node_triple_leaf_compact
        ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ cs,
      forestSum_cons_node_triple_leaf_compact α β cs,
      forestSum_cons_node_triple_leaf_compact
        α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ cs]
  change bSeriesConvAug α β
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
          * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + bSeriesConvAug α β BTree.leaf ^ 3
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [])) cs
        + 3 * bSeriesConvAug α β BTree.leaf ^ 2
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [BTree.leaf])) cs
        + 3 * bSeriesConvAug α β BTree.leaf
          * forestSum (fun σ => bSeriesConvAug α β σ)
              (γ.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) cs
        + forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) cs
        + (α.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
              * forestSum α.toFun β cs
            + α.toFun BTree.leaf ^ 3
              * forestSum α.toFun (β.shiftBy (BTree.node [])) cs
            + 3 * α.toFun BTree.leaf ^ 2
              * forestSum α.toFun
                  (β.shiftBy (BTree.node [BTree.leaf])) cs
            + 3 * α.toFun BTree.leaf
              * forestSum α.toFun
                  (β.shiftBy (BTree.node [BTree.leaf, BTree.leaf])) cs
            + forestSum α.toFun
                (β.shiftBy
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) cs)
            * γ.emptyVal
      = α.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
          * forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩ cs
        + α.toFun BTree.leaf ^ 3
          * forestSum α.toFun
              ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
                (BTree.node [])) cs
        + 3 * α.toFun BTree.leaf ^ 2
          * forestSum α.toFun
              ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
                (BTree.node [BTree.leaf])) cs
        + 3 * α.toFun BTree.leaf
          * forestSum α.toFun
              ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
                (BTree.node [BTree.leaf, BTree.leaf])) cs
        + forestSum α.toFun
            ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) cs
  rw [hgβ_triple, hgβ_leaf,
      shift_one_agg α β γ (BTree.node []) (by simp) cs hih,
      shift_node_singleton_agg α β γ BTree.leaf (by simp) cs hih,
      shift_pair_agg α β γ BTree.leaf BTree.leaf (by simp) (by simp) cs hih,
      shift_triple_leaf_agg α β γ cs hih]
  linear_combination
    α.toFun (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) * hih_γ

/-- Forest-level associativity for unital `β`, valid for any `γ`, on
lists whose children have order at most three.  Extends the cycle 598 /
cycle 599 ladder one rung further. -/
private theorem forestSum_assoc_depth_three
    (α β : AugSeries) (hβ : β.IsUnital) :
    ∀ (children : List BTree), (∀ c ∈ children, c.order ≤ 3) →
      ∀ (γ : AugSeries),
        forestSum (fun σ => bSeriesConvAug α β σ) γ children
          + forestSum α.toFun β children * γ.emptyVal
          = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩
              children := by
  intro children
  induction children with
  | nil =>
    intro _ γ
    simp only [forestSum, BTree.innerCutForest, List.map_cons, List.map_nil,
               List.sum_cons, List.sum_nil, List.foldr_nil,
               List.filterMap_nil, one_mul, add_zero]
    rw [bSeriesConvAug_node_nil β γ]
    ring
  | cons c cs ih =>
    intro hch γ
    have hc3 : c.order ≤ 3 := hch c List.mem_cons_self
    have hcs : ∀ c' ∈ cs, c'.order ≤ 3 :=
      fun c' hc' => hch c' (List.mem_cons_of_mem c hc')
    have hih : ∀ δ : AugSeries,
        forestSum (fun σ => bSeriesConvAug α β σ) δ cs
          + forestSum α.toFun β cs * δ.emptyVal
          = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs :=
      fun δ => ih hcs δ
    rcases (BTree.order_le_three_iff c).mp hc3 with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact forestSum_assoc_three_one_head α β γ hβ BTree.leaf
        (by simp) cs hih
    · exact forestSum_assoc_three_one_head α β γ hβ (BTree.node [])
        (by simp) cs hih
    · exact forestSum_assoc_three_singleton_head α β γ hβ BTree.leaf
        (by simp) cs hih
    · exact forestSum_assoc_three_singleton_head α β γ hβ (BTree.node [])
        (by simp) cs hih
    · exact forestSum_assoc_three_singleton_node_singleton_head α β γ hβ
        BTree.leaf (by simp) cs hih
    · exact forestSum_assoc_three_singleton_node_singleton_head α β γ hβ
        (BTree.node []) (by simp) cs hih
    · exact forestSum_assoc_three_pair_head α β γ hβ BTree.leaf BTree.leaf
        (by simp) (by simp) cs hih
    · exact forestSum_assoc_three_pair_head α β γ hβ BTree.leaf
        (BTree.node []) (by simp) (by simp) cs hih
    · exact forestSum_assoc_three_pair_head α β γ hβ (BTree.node [])
        BTree.leaf (by simp) (by simp) cs hih
    · exact forestSum_assoc_three_pair_head α β γ hβ (BTree.node [])
        (BTree.node []) (by simp) (by simp) cs hih

/-- Forest-level associativity for unital `β`, valid for any `γ`, on
lists whose children have order at most three, except that the new
order-4 triple-leaf shape is also allowed as a head/tail child. -/
private theorem forestSum_assoc_three_with_triple_leaf
    (α β : AugSeries) (hβ : β.IsUnital) :
    ∀ (children : List BTree), (∀ c ∈ children,
        c.order ≤ 3 ∨ c = BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) →
      ∀ (γ : AugSeries),
        forestSum (fun σ => bSeriesConvAug α β σ) γ children
          + forestSum α.toFun β children * γ.emptyVal
          = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩
              children := by
  intro children
  induction children with
  | nil =>
    intro _ γ
    simp only [forestSum, BTree.innerCutForest, List.map_cons, List.map_nil,
               List.sum_cons, List.sum_nil, List.foldr_nil,
               List.filterMap_nil, one_mul, add_zero]
    rw [bSeriesConvAug_node_nil β γ]
    ring
  | cons c cs ih =>
    intro hch γ
    have hc : c.order ≤ 3
        ∨ c = BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :=
      hch c List.mem_cons_self
    have hcs : ∀ c' ∈ cs,
        c'.order ≤ 3
          ∨ c' = BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] :=
      fun c' hc' => hch c' (List.mem_cons_of_mem c hc')
    have hih : ∀ δ : AugSeries,
        forestSum (fun σ => bSeriesConvAug α β σ) δ cs
          + forestSum α.toFun β cs * δ.emptyVal
          = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β δ σ⟩ cs :=
      fun δ => ih hcs δ
    rcases hc with hc3 | htriple
    · rcases (BTree.order_le_three_iff c).mp hc3 with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact forestSum_assoc_three_one_head α β γ hβ BTree.leaf
          (by simp) cs hih
      · exact forestSum_assoc_three_one_head α β γ hβ (BTree.node [])
          (by simp) cs hih
      · exact forestSum_assoc_three_singleton_head α β γ hβ BTree.leaf
          (by simp) cs hih
      · exact forestSum_assoc_three_singleton_head α β γ hβ (BTree.node [])
          (by simp) cs hih
      · exact forestSum_assoc_three_singleton_node_singleton_head α β γ hβ
          BTree.leaf (by simp) cs hih
      · exact forestSum_assoc_three_singleton_node_singleton_head α β γ hβ
          (BTree.node []) (by simp) cs hih
      · exact forestSum_assoc_three_pair_head α β γ hβ BTree.leaf BTree.leaf
          (by simp) (by simp) cs hih
      · exact forestSum_assoc_three_pair_head α β γ hβ BTree.leaf
          (BTree.node []) (by simp) (by simp) cs hih
      · exact forestSum_assoc_three_pair_head α β γ hβ (BTree.node [])
          BTree.leaf (by simp) (by simp) cs hih
      · exact forestSum_assoc_three_pair_head α β γ hβ (BTree.node [])
          (BTree.node []) (by simp) (by simp) cs hih
    · subst c
      exact forestSum_assoc_three_triple_leaf_head α β γ hβ cs hih

/-- **Cycle 602 headline (depth-3 mixed children)**: unital
associativity of `bSeriesConvAug` at any node whose root children all
have order ≤ 3. -/
theorem mul_assoc_at_node_depth_three_children
    (α β γ : AugSeries) (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital)
    (children : List BTree) (hchildren : ∀ c ∈ children, c.order ≤ 3) :
    bSeriesConvAug ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ
        (BTree.node children)
      = bSeriesConvAug α ⟨1, fun σ => bSeriesConvAug β γ σ⟩
        (BTree.node children) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  rw [bSeriesConvAug_node ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ children,
      bSeriesConvAug_node α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ children]
  show bSeriesConvAug α β (BTree.node children) * γ.emptyVal + _
       = α.toFun (BTree.node children) * 1 + _
  rw [bSeriesConvAug_node α β children, hβ', hγ', mul_one, mul_one]
  have key := forestSum_assoc_depth_three α β hβ children hchildren γ
  rw [hγ', mul_one] at key
  simp only [forestSum] at key
  show α.toFun (BTree.node children)
       + ((BTree.innerCutForest children α.toFun).map (fun forest =>
           forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
             * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
       + ((BTree.innerCutForest children
             (fun σ => bSeriesConvAug α β σ)).map (fun forest =>
           forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
             * γ.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
       = α.toFun (BTree.node children)
         + ((BTree.innerCutForest children α.toFun).map (fun forest =>
             forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
               * bSeriesConvAug β γ
                   (BTree.node (forest.filterMap (fun e => e.1))))).sum
  linarith

/-- **Cycle 605 headline extension**: unital associativity of
`bSeriesConvAug` at any node whose root children either have order at most
three or are the order-4 triple-leaf shape. -/
theorem mul_assoc_at_node_with_triple_leaf_children
    (α β γ : AugSeries) (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital)
    (children : List BTree) (hchildren : ∀ c ∈ children,
      c.order ≤ 3 ∨ c = BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) :
    bSeriesConvAug ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ
        (BTree.node children)
      = bSeriesConvAug α ⟨1, fun σ => bSeriesConvAug β γ σ⟩
        (BTree.node children) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  rw [bSeriesConvAug_node ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ children,
      bSeriesConvAug_node α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ children]
  show bSeriesConvAug α β (BTree.node children) * γ.emptyVal + _
       = α.toFun (BTree.node children) * 1 + _
  rw [bSeriesConvAug_node α β children, hβ', hγ', mul_one, mul_one]
  have key := forestSum_assoc_three_with_triple_leaf α β hβ children hchildren γ
  rw [hγ', mul_one] at key
  simp only [forestSum] at key
  show α.toFun (BTree.node children)
       + ((BTree.innerCutForest children α.toFun).map (fun forest =>
           forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
             * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
       + ((BTree.innerCutForest children
             (fun σ => bSeriesConvAug α β σ)).map (fun forest =>
           forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
             * γ.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
       = α.toFun (BTree.node children)
         + ((BTree.innerCutForest children α.toFun).map (fun forest =>
             forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
               * bSeriesConvAug β γ
                   (BTree.node (forest.filterMap (fun e => e.1))))).sum
  linarith

end ButcherTableau
