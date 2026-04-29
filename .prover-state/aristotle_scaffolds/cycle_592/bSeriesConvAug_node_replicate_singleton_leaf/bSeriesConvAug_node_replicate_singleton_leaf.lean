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

/-- Disjoint pairs `(S₁, S₂)` of subsets of `Fin n`. -/
def threeChoice (n : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
    (fun p => Disjoint p.1 p.2)

/-- Trunk forest for a disjoint pair `(S₁, S₂)`. -/
def trunkChildren (n : ℕ) (S₁ S₂ : Finset (Fin n)) : List BTree :=
  ((List.finRange n).filter (fun i => i ∉ S₁)).map fun i =>
    if i ∈ S₂ then BTree.node [] else BTree.node [BTree.leaf]

noncomputable def repSingletonLeafContrib
    (α β : AugSeries) (n : ℕ) (S₁ S₂ : Finset (Fin n)) : ℝ :=
  α.toFun (BTree.node [BTree.leaf]) ^ S₁.card
    * α.toFun BTree.leaf ^ S₂.card
    * β.toFun (BTree.node (trunkChildren n S₁ S₂))

/-- Parametric closed form for `bSeriesConvAug` on
`BTree.node (List.replicate n (BTree.node [BTree.leaf]))`.

For each position in `Fin n` the inner-cut machinery offers three options
(fully cut at the child root, partial-trunk cut keeping the root and
pruning the inner leaf, fully kept).  The three-way per-position cut is
encoded by a disjoint pair `(S₁, S₂) ∈ threeChoice n`.  Prove by
induction on `n` using `List.replicate_succ` to peel one position. -/
theorem bSeriesConvAug_node_replicate_singleton_leaf
    (α β : AugSeries) (n : ℕ) :
    bSeriesConvAug α β
        (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
      = α.toFun (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
            * β.emptyVal
        + ∑ p ∈ threeChoice n,
            repSingletonLeafContrib α β n p.1 p.2 := by
  sorry

end ButcherTableau
