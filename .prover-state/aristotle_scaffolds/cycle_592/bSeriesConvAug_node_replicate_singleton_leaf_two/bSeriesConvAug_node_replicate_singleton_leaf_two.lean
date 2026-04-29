import Mathlib

inductive BTree where
  | leaf : BTree
  | node : List BTree → BTree
  deriving Repr

namespace ButcherTableau

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

structure AugSeries where
  emptyVal : ℝ
  toFun    : BTree → ℝ

noncomputable def bSeriesConvAug (α β : AugSeries) (τ : BTree) : ℝ :=
  ((τ.innerCut α.toFun).map fun c =>
      match c.1 with
      | some trunk => c.2 * β.toFun trunk
      | none       => c.2 * β.emptyVal).sum

open Finset

/-- Closed form for `bSeriesConvAug` on the two-child shape from cycle 590. -/
theorem bSeriesConvAug_two_singleton_leaves (α β : AugSeries) :
    bSeriesConvAug α β
        (BTree.node [BTree.node [BTree.leaf], BTree.node [BTree.leaf]])
      = α.toFun (BTree.node [BTree.node [BTree.leaf],
            BTree.node [BTree.leaf]]) * β.emptyVal
        + β.toFun (BTree.node [BTree.node [BTree.leaf],
            BTree.node [BTree.leaf]])
        + α.toFun (BTree.node [BTree.leaf]) ^ 2
            * β.toFun (BTree.node [])
        + 2 * α.toFun (BTree.node [BTree.leaf])
            * β.toFun (BTree.node [BTree.node [BTree.leaf]])
        + 2 * α.toFun (BTree.node [BTree.leaf]) * α.toFun BTree.leaf
            * β.toFun (BTree.node [BTree.node []])
        + α.toFun BTree.leaf
            * β.toFun (BTree.node [BTree.node [BTree.leaf], BTree.node []])
        + α.toFun BTree.leaf
            * β.toFun (BTree.node [BTree.node [], BTree.node [BTree.leaf]])
        + α.toFun BTree.leaf ^ 2
            * β.toFun (BTree.node [BTree.node [], BTree.node []]) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]
  ring

def threeChoice (n : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
    (fun p => Disjoint p.1 p.2)

def trunkChildren (n : ℕ) (S₁ S₂ : Finset (Fin n)) : List BTree :=
  ((List.finRange n).filter (fun i => i ∉ S₁)).map fun i =>
    if i ∈ S₂ then BTree.node [] else BTree.node [BTree.leaf]

noncomputable def repSingletonLeafContrib
    (α β : AugSeries) (n : ℕ) (S₁ S₂ : Finset (Fin n)) : ℝ :=
  α.toFun (BTree.node [BTree.leaf]) ^ S₁.card
    * α.toFun BTree.leaf ^ S₂.card
    * β.toFun (BTree.node (trunkChildren n S₁ S₂))

/-- Sanity bridge: the parametric RHS at `n = 2` agrees with the
existing closed form `bSeriesConvAug_two_singleton_leaves`.
This is a finite enumeration: `threeChoice 2` has 9 disjoint pairs. -/
theorem bSeriesConvAug_node_replicate_singleton_leaf_two
    (α β : AugSeries) :
    α.toFun (BTree.node (List.replicate 2 (BTree.node [BTree.leaf])))
        * β.emptyVal
      + ∑ p ∈ threeChoice 2,
          repSingletonLeafContrib α β 2 p.1 p.2
    = bSeriesConvAug α β
        (BTree.node [BTree.node [BTree.leaf], BTree.node [BTree.leaf]]) := by
  sorry

end ButcherTableau
