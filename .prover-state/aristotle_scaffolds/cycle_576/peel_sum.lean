import Mathlib

open Finset

namespace AristotleScaffold

/-- Inner-cut option pairs are (Option BTree × ℝ). -/

/-- Local restatement of `BTree`. -/
inductive BTree where
  | leaf : BTree
  | node : List BTree → BTree
  deriving Inhabited

/-- Local restatement of `BTree.order`. -/
def BTree.order : BTree → ℕ
  | BTree.leaf => 1
  | BTree.node children => 1 + (children.map BTree.order).sum
decreasing_by
  all_goals (simp_wf; sorry)

/-- Local restatement of `BTree.innerCut` and `BTree.innerCutForest`. -/
mutual
  def BTree.innerCut (τ : BTree) (α : BTree → ℝ) :
      List (Option BTree × ℝ) :=
    match τ with
    | BTree.leaf => [(some BTree.leaf, (1 : ℝ)), (none, α BTree.leaf)]
    | BTree.node children =>
        (none, α (BTree.node children)) ::
          (BTree.innerCutForest children α).map (fun cs =>
            (some (BTree.node (cs.filterMap (fun c => c.1))),
              cs.foldr (fun c acc => c.2 * acc) (1 : ℝ)))
  termination_by sizeOf τ
  decreasing_by all_goals (simp_wf; sorry)

  def BTree.innerCutForest (children : List BTree)
      (α : BTree → ℝ) : List (List (Option BTree × ℝ)) :=
    match children with
    | [] => [[]]
    | head :: tail =>
        List.flatMap
          (fun c => (BTree.innerCutForest tail α).map (fun cs => c :: cs))
          (head.innerCut α)
  termination_by sizeOf children
  decreasing_by all_goals (simp_wf; sorry)
end

/-- The bSeries-only admissible-cut convolution. -/
def bSeriesConv (α β : BTree → ℝ) (τ : BTree) : ℝ :=
  ((τ.innerCut α).filterMap fun c => c.1.map (fun t => c.2 * β t)).sum

/-- Proper bSeries-side cut convolution: trunk strictly smaller than τ. -/
def bSeriesConvNonRoot (α : BTree → ℝ) (τ : BTree)
    (β : ∀ σ : BTree, σ.order < τ.order → ℝ) : ℝ :=
  ((τ.innerCut α).filterMap fun c =>
    c.1.map fun trunk =>
      if h : trunk.order < τ.order then c.2 * β trunk h else 0).sum

/-- Headline peeling lemma: split the bSeries convolution into the
canonical no-cut β τ root contribution plus the proper trunk
contributions. -/
theorem bSeriesConv_eq_root_plus_nonRoot
    (α β : BTree → ℝ) (τ : BTree) :
    bSeriesConv α β τ
      = β τ + bSeriesConvNonRoot α τ (fun σ _ => β σ) := by
  sorry

end AristotleScaffold
