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

/-- Closed form for the smallest tree exhibiting a partial-trunk cut.

For `BTree.node [BTree.node [BTree.leaf]]`, the inner-cut list has four
entries:
* `(none, α(node [node [leaf]]))`, contributing the full-prune branch;
* `(some (node []), α(node [leaf]))`, pruning the whole child;
* `(some (node [node [leaf]]), 1)`, the no-prune branch;
* `(some (node [node []]), α(leaf))`, the new partial-trunk branch that
  cuts the inner leaf while keeping the child root. -/
theorem bSeriesConvAug_singleton_singleton_leaf (α β : AugSeries) :
    bSeriesConvAug α β (BTree.node [BTree.node [BTree.leaf]])
      = α.toFun (BTree.node [BTree.node [BTree.leaf]]) * β.emptyVal
        + β.toFun (BTree.node [BTree.node [BTree.leaf]])
        + α.toFun (BTree.node [BTree.leaf]) * β.toFun (BTree.node [])
        + α.toFun BTree.leaf * β.toFun (BTree.node [BTree.node []]) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]
  ring

/-- Depth-3 unital associativity sanity check at the first tree with a
partial-trunk cut, `BTree.node [BTree.node [BTree.leaf]]`. -/
theorem mul_assoc_at_singleton_singleton_leaf
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node [BTree.node [BTree.leaf]])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node [BTree.node [BTree.leaf]]) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  rw [bSeriesConvAug_singleton_singleton_leaf,
      bSeriesConvAug_singleton_singleton_leaf]
  simp only [bSeriesConvAug_leaf, bSeriesConvAug_node_nil,
    bSeriesConvAug_node_singleton_leaf, bSeriesConvAug_node_node_nil,
    bSeriesConvAug_singleton_singleton_leaf]
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

/-- Binomial identity used to lift unital depth-2 associativity to all
`List.replicate n BTree.leaf` shapes.  For any function `h : ℕ → ℝ`,
the sum of `(b+a)^|S| · h(n-|S|)` over subsets of `Fin n` agrees with
the disjoint-pair sum of `a^|S| · ∑_T b^|T| · h(n-|S|-|T|)`. -/
private lemma replicate_leaf_assoc_aux (a b : ℝ) :
    ∀ (n : ℕ) (h : ℕ → ℝ),
      (∑ S : Finset (Fin n), (b + a) ^ S.card * h (n - S.card))
        = ∑ S : Finset (Fin n), a ^ S.card *
            ∑ T : Finset (Fin (n - S.card)), b ^ T.card *
              h (n - S.card - T.card) := by
  intro n
  induction n with
  | zero =>
      intro h
      simp [show ∀ (s : Finset (Fin 0)), s = ∅ from fun s => by ext x; exact x.elim0]
  | succ n ih =>
      intro h
      have hcard : ∀ S : Finset (Fin n), S.card ≤ n := fun S => by
        simpa [Finset.card_univ, Fintype.card_fin] using S.card_le_univ
      -- Step A: split outer LHS sum.
      rw [sum_finset_fin_succ_card_eq n
            (fun k => (b + a) ^ k * h ((n + 1) - k))]
      -- Convert each LHS summand to use (n - |S|) form.
      have lhs1 : ∀ S : Finset (Fin n),
          (b + a) ^ S.card * h (n + 1 - S.card)
            = (b + a) ^ S.card * (fun k => h (k + 1)) (n - S.card) := fun S => by
        have hS := hcard S
        have heq : n + 1 - S.card = (n - S.card) + 1 := by omega
        simp [heq]
      have lhs2 : ∀ S : Finset (Fin n),
          (b + a) ^ (S.card + 1) * h (n + 1 - (S.card + 1))
            = (b + a) * ((b + a) ^ S.card * h (n - S.card)) := fun S => by
        have hS := hcard S
        have heq : n + 1 - (S.card + 1) = n - S.card := by omega
        rw [pow_succ, heq]; ring
      rw [Finset.sum_congr rfl (fun S _ => lhs1 S),
          Finset.sum_congr rfl (fun S _ => lhs2 S),
          ← Finset.mul_sum]
      -- Apply IH to h' := h ∘ (· + 1) and to h.
      rw [ih (fun k => h (k + 1)), ih h]
      -- Step B: split outer RHS sum.
      rw [sum_finset_fin_succ_card_eq n
            (fun k => a ^ k *
              ∑ T : Finset (Fin (n + 1 - k)), b ^ T.card *
                h (n + 1 - k - T.card))]
      -- Convert each RHS outer summand: rewrite (n+1 - |S|) as (n - |S|)+1
      -- and split inner sum analogously.
      have rhs1 : ∀ S : Finset (Fin n),
          a ^ S.card *
            (∑ T : Finset (Fin (n + 1 - S.card)), b ^ T.card *
              h (n + 1 - S.card - T.card))
            = a ^ S.card *
                (∑ T : Finset (Fin (n - S.card)), b ^ T.card *
                  (fun k => h (k + 1)) (n - S.card - T.card))
              + b * (a ^ S.card *
                  ∑ T : Finset (Fin (n - S.card)), b ^ T.card *
                    h (n - S.card - T.card)) := fun S => by
        have hS := hcard S
        have hsub : n + 1 - S.card = (n - S.card) + 1 := by omega
        rw [hsub]
        rw [sum_finset_fin_succ_card_eq (n - S.card)
              (fun k => b ^ k * h ((n - S.card + 1) - k))]
        rw [mul_add]
        congr 1
        · refine congrArg _ (Finset.sum_congr rfl (fun T _ => ?_))
          have hT : T.card ≤ n - S.card := by
            simpa [Finset.card_univ, Fintype.card_fin] using T.card_le_univ
          have heq : (n - S.card + 1) - T.card = (n - S.card - T.card) + 1 := by
            omega
          simp [heq]
        · simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun T _ => ?_)
          have hT : T.card ≤ n - S.card := by
            simpa [Finset.card_univ, Fintype.card_fin] using T.card_le_univ
          have heq : (n - S.card + 1) - (T.card + 1) = n - S.card - T.card := by
            omega
          rw [pow_succ, heq]
          ring
      have rhs2 : ∀ S : Finset (Fin n),
          a ^ (S.card + 1) *
            (∑ T : Finset (Fin (n + 1 - (S.card + 1))), b ^ T.card *
              h (n + 1 - (S.card + 1) - T.card))
            = a * (a ^ S.card *
                ∑ T : Finset (Fin (n - S.card)), b ^ T.card *
                  h (n - S.card - T.card)) := fun S => by
        have hS := hcard S
        have heq : n + 1 - (S.card + 1) = n - S.card := by omega
        rw [pow_succ, heq]
        ring
      rw [Finset.sum_congr rfl (fun S _ => rhs1 S),
          Finset.sum_congr rfl (fun S _ => rhs2 S),
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- Closed form for `bSeriesConvAug` on a node whose children are
`n` leaves: a `Finset (Fin n)`-powerset sum over the leaves to cut. -/
theorem bSeriesConvAug_node_replicate_leaf (α β : AugSeries) (n : ℕ) :
    bSeriesConvAug α β (BTree.node (List.replicate n BTree.leaf))
      = α.toFun (BTree.node (List.replicate n BTree.leaf)) * β.emptyVal
        + ∑ S : Finset (Fin n), α.toFun BTree.leaf ^ S.card *
            β.toFun (BTree.node (List.replicate (n - S.card) BTree.leaf)) := by
  rw [bSeriesConvAug_node]
  congr 1
  rw [← cutSum_filterMap_eq_map β.toFun]
  exact innerCutForest_replicate_leaf_sum α.toFun β.toFun n

/-- Closed form for `bSeriesConvAug` on a two-leaf node. -/
theorem bSeriesConvAug_node_two_leaves (α β : AugSeries) :
    bSeriesConvAug α β (BTree.node [BTree.leaf, BTree.leaf])
      = α.toFun (BTree.node [BTree.leaf, BTree.leaf]) * β.emptyVal
        + β.toFun (BTree.node [BTree.leaf, BTree.leaf])
        + 2 * α.toFun BTree.leaf * β.toFun (BTree.node [BTree.leaf])
        + α.toFun BTree.leaf * α.toFun BTree.leaf * β.toFun (BTree.node []) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]
  ring

/-- Depth-2 unital associativity sanity check at
`BTree.node [BTree.leaf, BTree.leaf]` (the next size-3 tree after the
single-leaf and `node []`-only depth-2 cases). -/
theorem mul_assoc_at_node_two_leaves
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node [BTree.leaf, BTree.leaf])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node [BTree.leaf, BTree.leaf]) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  rw [bSeriesConvAug_node_two_leaves, bSeriesConvAug_node_two_leaves]
  simp only [bSeriesConvAug_leaf, bSeriesConvAug_node_nil,
    bSeriesConvAug_node_singleton_leaf, bSeriesConvAug_node_two_leaves]
  rw [hβ', hγ']
  ring

/-- **Target 1 (cycle 586)**: Depth-2 unital associativity of `bSeriesConvAug`
on every node whose children are `n` leaves.

Combines the closed form `bSeriesConvAug_node_replicate_leaf` with the
binomial identity `replicate_leaf_assoc_aux`. -/
theorem mul_assoc_at_node_replicate_leaf
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) (n : ℕ) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node (List.replicate n BTree.leaf))
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node (List.replicate n BTree.leaf)) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  rw [bSeriesConvAug_node_replicate_leaf, bSeriesConvAug_node_replicate_leaf]
  dsimp only
  simp only [bSeriesConvAug_leaf, bSeriesConvAug_node_replicate_leaf,
    hβ', hγ', mul_one, mul_add, Finset.sum_add_distrib]
  linear_combination replicate_leaf_assoc_aux (α.toFun BTree.leaf)
    (β.toFun BTree.leaf) n
    (fun k => γ.toFun (BTree.node (List.replicate k BTree.leaf)))

/-- Cons unfolding of `BTree.innerCutForest` on an empty-node prefix:
prepending one `node []` splits as cut-head and kept-head over the tail
forest.  Local copy of the private helper from `Section386Conv` since the
original is file-private. -/
private theorem innerCutForest_node_nil_cons_aux (α : BTree → ℝ)
    (tail : List BTree) :
    BTree.innerCutForest (BTree.node [] :: tail) α
      = (BTree.innerCutForest tail α).map
          (fun cs => (none, α (BTree.node [])) :: cs)
        ++ (BTree.innerCutForest tail α).map
          (fun cs => (some (BTree.node []), (1 : ℝ)) :: cs) := by
  conv_lhs => rw [BTree.innerCutForest]
  rw [innerCut_node_nil]
  simp [List.flatMap]

/-- The list enumeration of inner cuts of
`BTree.node (List.replicate n (BTree.node []))` reindexes to the
`Finset (Fin n)` powerset sum.  Local analogue of
`innerCutForest_replicate_leaf_sum` for the `node []` shape; the original
private lemma in `Section386Conv` is not visible here. -/
private theorem innerCutForest_replicate_node_nil_sum_aux
    (α β : BTree → ℝ) (n : ℕ) :
    (List.filterMap
        ((fun c => Option.map (fun t => c.2 * β t) c.1) ∘ fun cs =>
          (some (BTree.node (List.filterMap (fun c => c.1) cs)),
           List.foldr (fun c acc => c.2 * acc) 1 cs))
        (BTree.innerCutForest (List.replicate n (BTree.node [])) α)).sum
      =
        ∑ S : Finset (Fin n),
          α (BTree.node []) ^ S.card *
            β (BTree.node (List.replicate (n - S.card) (BTree.node []))) := by
  induction n generalizing β with
  | zero =>
      rw [cutSum_filterMap_eq_map]
      simp [BTree.innerCutForest]
      rw [show (default : Finset (Fin 0)) = ∅ from rfl]
      simp
  | succ n ih =>
      rw [cutSum_filterMap_eq_map β,
          List.replicate_succ, innerCutForest_node_nil_cons_aux,
          List.map_append, List.sum_append,
          List.map_map, List.map_map]
      have hcut_fun :
          ((fun cs : List (Option BTree × ℝ) =>
              List.foldr (fun c acc => c.2 * acc) 1 cs *
                β (BTree.node (List.filterMap (fun c => c.1) cs))) ∘
            fun cs => (none, α (BTree.node [])) :: cs)
            = (fun cs : List (Option BTree × ℝ) =>
                α (BTree.node []) *
                  (List.foldr (fun c acc => c.2 * acc) 1 cs *
                    β (BTree.node (List.filterMap (fun c => c.1) cs)))) := by
        funext cs
        simp [Function.comp]
        ring
      let β_kept : BTree → ℝ := fun t =>
        match t with
        | BTree.leaf => 0
        | BTree.node xs => β (BTree.node (BTree.node [] :: xs))
      have hkept_fun :
          ((fun cs : List (Option BTree × ℝ) =>
              List.foldr (fun c acc => c.2 * acc) 1 cs *
                β (BTree.node (List.filterMap (fun c => c.1) cs))) ∘
            fun cs => (some (BTree.node []), (1 : ℝ)) :: cs)
            = (fun cs : List (Option BTree × ℝ) =>
                List.foldr (fun c acc => c.2 * acc) 1 cs *
                  β_kept (BTree.node (List.filterMap (fun c => c.1) cs))) := by
        funext cs
        simp [Function.comp, β_kept, one_mul]
      rw [hcut_fun, hkept_fun]
      have hcut_factor :
          (List.map (fun cs : List (Option BTree × ℝ) =>
                α (BTree.node []) *
                  (List.foldr (fun c acc => c.2 * acc) 1 cs *
                    β (BTree.node (List.filterMap (fun c => c.1) cs))))
              (BTree.innerCutForest (List.replicate n (BTree.node [])) α)).sum
            = α (BTree.node []) *
              (List.filterMap
                  ((fun c : Option BTree × ℝ =>
                      Option.map (fun t => c.2 * β t) c.1) ∘ fun cs =>
                    (some (BTree.node (List.filterMap (fun c => c.1) cs)),
                     List.foldr (fun c acc => c.2 * acc) 1 cs))
                  (BTree.innerCutForest (List.replicate n (BTree.node [])) α)).sum := by
        rw [cutSum_filterMap_eq_map β]
        induction (BTree.innerCutForest (List.replicate n (BTree.node [])) α) with
        | nil => simp
        | cons head tail ih' =>
            simp [List.map_cons, List.sum_cons, ih', mul_add]
      rw [hcut_factor]
      rw [show (List.map (fun cs : List (Option BTree × ℝ) =>
            List.foldr (fun c acc => c.2 * acc) 1 cs *
              β_kept (BTree.node (List.filterMap (fun c => c.1) cs)))
            (BTree.innerCutForest (List.replicate n (BTree.node [])) α))
          = List.filterMap
              ((fun c : Option BTree × ℝ =>
                  Option.map (fun t => c.2 * β_kept t) c.1) ∘ fun cs =>
                (some (BTree.node (List.filterMap (fun c => c.1) cs)),
                 List.foldr (fun c acc => c.2 * acc) 1 cs))
              (BTree.innerCutForest (List.replicate n (BTree.node [])) α) from
          (cutSum_filterMap_eq_map β_kept _).symm]
      rw [ih β, ih β_kept]
      rw [sum_finset_fin_succ_card_eq n
            (fun k => α (BTree.node []) ^ k *
              β (BTree.node (List.replicate ((n + 1) - k) (BTree.node []))))]
      have hkept_match :
          (∑ S : Finset (Fin n), α (BTree.node []) ^ S.card *
              β_kept (BTree.node (List.replicate (n - S.card) (BTree.node []))))
            = ∑ S : Finset (Fin n), α (BTree.node []) ^ S.card *
                β (BTree.node
                  (List.replicate ((n + 1) - S.card) (BTree.node []))) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        have hle : S.card ≤ n := by
          have := S.card_le_univ
          simpa [Finset.card_univ, Fintype.card_fin] using this
        congr 2
        show β_kept (BTree.node (List.replicate (n - S.card) (BTree.node [])))
              = β (BTree.node
                  (List.replicate ((n + 1) - S.card) (BTree.node [])))
        simp [β_kept, ← List.replicate_succ, Nat.succ_sub hle]
      have hcut_match :
          α (BTree.node []) *
              (∑ S : Finset (Fin n), α (BTree.node []) ^ S.card *
                β (BTree.node (List.replicate (n - S.card) (BTree.node []))))
            = ∑ S : Finset (Fin n), α (BTree.node []) ^ (S.card + 1) *
                β (BTree.node
                  (List.replicate ((n + 1) - (S.card + 1)) (BTree.node []))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro S _
        have hsub : (n + 1) - (S.card + 1) = n - S.card := by omega
        rw [hsub, pow_succ]
        ring
      rw [hcut_match, hkept_match]
      ring

/-- Closed form for `bSeriesConvAug` on a node whose children are `n`
copies of `BTree.node []`: a `Finset (Fin n)`-powerset sum over which
empty-node children to cut. -/
theorem bSeriesConvAug_node_replicate_node_nil (α β : AugSeries) (n : ℕ) :
    bSeriesConvAug α β (BTree.node (List.replicate n (BTree.node [])))
      = α.toFun (BTree.node (List.replicate n (BTree.node []))) * β.emptyVal
        + ∑ S : Finset (Fin n), α.toFun (BTree.node []) ^ S.card *
            β.toFun (BTree.node
              (List.replicate (n - S.card) (BTree.node []))) := by
  rw [bSeriesConvAug_node]
  congr 1
  rw [← cutSum_filterMap_eq_map β.toFun]
  exact innerCutForest_replicate_node_nil_sum_aux α.toFun β.toFun n

/-- **Cycle 588 target**: depth-2 unital associativity of `bSeriesConvAug`
on every node whose children are `n` copies of `BTree.node []`.

Combines the closed form `bSeriesConvAug_node_replicate_node_nil` with
the binomial identity `replicate_leaf_assoc_aux`. -/
theorem mul_assoc_at_node_replicate_node_nil
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) (n : ℕ) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node (List.replicate n (BTree.node [])))
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node (List.replicate n (BTree.node []))) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  rw [bSeriesConvAug_node_replicate_node_nil,
      bSeriesConvAug_node_replicate_node_nil]
  dsimp only
  simp only [bSeriesConvAug_node_nil, bSeriesConvAug_node_replicate_node_nil,
    hβ', hγ', mul_one, mul_add, Finset.sum_add_distrib]
  simp_rw [show α.toFun (BTree.node []) + β.toFun (BTree.node [])
          = β.toFun (BTree.node []) + α.toFun (BTree.node []) from add_comm _ _]
  linear_combination replicate_leaf_assoc_aux (α.toFun (BTree.node []))
    (β.toFun (BTree.node [])) n
    (fun k => γ.toFun (BTree.node (List.replicate k (BTree.node []))))

/-- `n = 2` safety-net specialization of
`mul_assoc_at_node_replicate_node_nil`. -/
theorem mul_assoc_at_node_two_node_nils
    (α β γ : AugSeries)
    (hα : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node [BTree.node [], BTree.node []])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node [BTree.node [], BTree.node []]) := by
  have h := mul_assoc_at_node_replicate_node_nil α β γ hα hβ hγ 2
  simpa [List.replicate] using h

/-- Closed form for `bSeriesConvAug` on a node whose two children are both
`BTree.node [BTree.leaf]`.  Each child contributes three cut options
(fully cut at its own root, partial-trunk cut keeping the root and pruning
the leaf, fully kept), so the forest enumeration has nine entries plus
the top-level prune. -/
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

/-- Closed form for `bSeriesConvAug` on a node whose three children are
all `BTree.node [BTree.leaf]`.  The displayed terms are the concrete
`n = 3` disjoint `(S₁, S₂)` enumeration: each child is either cut at
its root, partially cut to `node []`, or fully kept. -/
theorem bSeriesConvAug_three_singleton_leaves (α β : AugSeries) :
    bSeriesConvAug α β
        (BTree.node
          [BTree.node [BTree.leaf], BTree.node [BTree.leaf],
           BTree.node [BTree.leaf]])
      = α.toFun (BTree.node
          [BTree.node [BTree.leaf], BTree.node [BTree.leaf],
           BTree.node [BTree.leaf]]) * β.emptyVal
        + β.toFun (BTree.node
          [BTree.node [BTree.leaf], BTree.node [BTree.leaf],
           BTree.node [BTree.leaf]])
        + α.toFun BTree.leaf
            * β.toFun (BTree.node
              [BTree.node [], BTree.node [BTree.leaf],
               BTree.node [BTree.leaf]])
        + α.toFun BTree.leaf
            * β.toFun (BTree.node
              [BTree.node [BTree.leaf], BTree.node [],
               BTree.node [BTree.leaf]])
        + α.toFun BTree.leaf
            * β.toFun (BTree.node
              [BTree.node [BTree.leaf], BTree.node [BTree.leaf],
               BTree.node []])
        + α.toFun BTree.leaf ^ 2
            * β.toFun (BTree.node
              [BTree.node [], BTree.node [], BTree.node [BTree.leaf]])
        + α.toFun BTree.leaf ^ 2
            * β.toFun (BTree.node
              [BTree.node [], BTree.node [BTree.leaf],
               BTree.node []])
        + α.toFun BTree.leaf ^ 2
            * β.toFun (BTree.node
              [BTree.node [BTree.leaf], BTree.node [], BTree.node []])
        + α.toFun BTree.leaf ^ 3
            * β.toFun (BTree.node
              [BTree.node [], BTree.node [], BTree.node []])
        + 3 * α.toFun (BTree.node [BTree.leaf])
            * β.toFun (BTree.node
              [BTree.node [BTree.leaf], BTree.node [BTree.leaf]])
        + 3 * α.toFun (BTree.node [BTree.leaf]) * α.toFun BTree.leaf
            * β.toFun (BTree.node [BTree.node [], BTree.node [BTree.leaf]])
        + 3 * α.toFun (BTree.node [BTree.leaf]) * α.toFun BTree.leaf
            * β.toFun (BTree.node [BTree.node [BTree.leaf], BTree.node []])
        + 3 * α.toFun (BTree.node [BTree.leaf]) * α.toFun BTree.leaf ^ 2
            * β.toFun (BTree.node [BTree.node [], BTree.node []])
        + 3 * α.toFun (BTree.node [BTree.leaf]) ^ 2
            * β.toFun (BTree.node [BTree.node [BTree.leaf]])
        + 3 * α.toFun (BTree.node [BTree.leaf]) ^ 2 * α.toFun BTree.leaf
            * β.toFun (BTree.node [BTree.node []])
        + α.toFun (BTree.node [BTree.leaf]) ^ 3
            * β.toFun (BTree.node []) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]
  ring

/-- Closed form for `bSeriesConvAug` on the asymmetric two-child shape
`[BTree.node [BTree.leaf], BTree.node []]`.  Used by Theorem B's
expansion of `(βγ)` on the inner trunks. -/
private theorem bSeriesConvAug_node_singleton_leaf_node_nil (α β : AugSeries) :
    bSeriesConvAug α β
        (BTree.node [BTree.node [BTree.leaf], BTree.node []])
      = α.toFun (BTree.node [BTree.node [BTree.leaf], BTree.node []])
            * β.emptyVal
        + β.toFun (BTree.node [BTree.node [BTree.leaf], BTree.node []])
        + α.toFun (BTree.node [BTree.leaf]) * α.toFun (BTree.node [])
            * β.toFun (BTree.node [])
        + α.toFun (BTree.node [BTree.leaf])
            * β.toFun (BTree.node [BTree.node []])
        + α.toFun (BTree.node [])
            * β.toFun (BTree.node [BTree.node [BTree.leaf]])
        + α.toFun BTree.leaf * α.toFun (BTree.node [])
            * β.toFun (BTree.node [BTree.node []])
        + α.toFun BTree.leaf
            * β.toFun (BTree.node [BTree.node [], BTree.node []]) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]
  ring

/-- Closed form for `bSeriesConvAug` on the asymmetric two-child shape
`[BTree.node [], BTree.node [BTree.leaf]]`. -/
private theorem bSeriesConvAug_node_nil_node_singleton_leaf
    (α β : AugSeries) :
    bSeriesConvAug α β
        (BTree.node [BTree.node [], BTree.node [BTree.leaf]])
      = α.toFun (BTree.node [BTree.node [], BTree.node [BTree.leaf]])
            * β.emptyVal
        + β.toFun (BTree.node [BTree.node [], BTree.node [BTree.leaf]])
        + α.toFun (BTree.node []) * α.toFun (BTree.node [BTree.leaf])
            * β.toFun (BTree.node [])
        + α.toFun (BTree.node [])
            * β.toFun (BTree.node [BTree.node [BTree.leaf]])
        + α.toFun (BTree.node []) * α.toFun BTree.leaf
            * β.toFun (BTree.node [BTree.node []])
        + α.toFun (BTree.node [BTree.leaf])
            * β.toFun (BTree.node [BTree.node []])
        + α.toFun BTree.leaf
            * β.toFun (BTree.node [BTree.node [], BTree.node []]) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]
  ring

/-- Closed form for `bSeriesConvAug` on `BTree.node [BTree.node [],
BTree.node []]`.  Direct two-empty-children evaluation. -/
private theorem bSeriesConvAug_two_node_nils (α β : AugSeries) :
    bSeriesConvAug α β (BTree.node [BTree.node [], BTree.node []])
      = α.toFun (BTree.node [BTree.node [], BTree.node []]) * β.emptyVal
        + β.toFun (BTree.node [BTree.node [], BTree.node []])
        + α.toFun (BTree.node []) ^ 2 * β.toFun (BTree.node [])
        + 2 * α.toFun (BTree.node [])
            * β.toFun (BTree.node [BTree.node []]) := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]
  ring

/-- Depth-3 unital associativity sanity check at the two-child order-2
shape `BTree.node [BTree.node [BTree.leaf], BTree.node [BTree.leaf]]`. -/
theorem mul_assoc_at_two_singleton_leaves
    (α β γ : AugSeries)
    (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node [BTree.node [BTree.leaf], BTree.node [BTree.leaf]])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
          (BTree.node [BTree.node [BTree.leaf],
            BTree.node [BTree.leaf]]) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  rw [bSeriesConvAug_two_singleton_leaves,
      bSeriesConvAug_two_singleton_leaves]
  simp only [bSeriesConvAug_leaf, bSeriesConvAug_node_nil,
    bSeriesConvAug_node_singleton_leaf, bSeriesConvAug_node_node_nil,
    bSeriesConvAug_singleton_singleton_leaf,
    bSeriesConvAug_two_singleton_leaves,
    bSeriesConvAug_node_singleton_leaf_node_nil,
    bSeriesConvAug_node_nil_node_singleton_leaf,
    bSeriesConvAug_two_node_nils,
    hβ', hγ', mul_one]
  ring

/-- Depth-3 unital associativity sanity check at the three-child
order-2 shape `BTree.node [node [leaf], node [leaf], node [leaf]]`. -/
theorem mul_assoc_at_three_singleton_leaves
    (α β γ : AugSeries) (hβ : β.IsUnital) (hγ : γ.IsUnital) :
    bSeriesConvAug ⟨1, fun τ => bSeriesConvAug α β τ⟩ γ
        (BTree.node
          [BTree.node [BTree.leaf], BTree.node [BTree.leaf],
           BTree.node [BTree.leaf]])
      = bSeriesConvAug α ⟨1, fun τ => bSeriesConvAug β γ τ⟩
        (BTree.node
          [BTree.node [BTree.leaf], BTree.node [BTree.leaf],
           BTree.node [BTree.leaf]]) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest, hβ', hγ']
  ring

section ThreeChoice

/-- Disjoint-pair combinator. Encodes the per-position three-way choice
on `BTree.node (List.replicate n (BTree.node [BTree.leaf]))`:
- `i ∈ S₁`: cut at the child root.
- `i ∈ S₂`: partial-trunk cut, prune the inner leaf.
- `i ∉ S₁ ∪ S₂`: keep the child fully.
The carrier filter enforces `S₁ ∩ S₂ = ∅`. -/
def threeChoice (n : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  Finset.univ.filter (fun p => p.1 ∩ p.2 = ∅)

theorem threeChoice_zero : threeChoice 0 = {(∅, ∅)} := by
  decide

theorem mem_threeChoice_iff (n : ℕ) (S₁ S₂ : Finset (Fin n)) :
    (S₁, S₂) ∈ threeChoice n ↔ Disjoint S₁ S₂ := by
  simp [threeChoice, Finset.disjoint_iff_inter_eq_empty]

theorem threeChoice_one :
    threeChoice 1 = {(∅, ∅), (∅, {0}), ({0}, ∅)} := by
  decide

end ThreeChoice

/-- Cons-layer specialization of `bSeriesConvAug_node`: same root-prune
plus inner-forest split, expressed for an explicit head child `c` and
tail `cs`.  This is the list-cons form that the unital associativity
inductive step decomposes through. -/
theorem bSeriesConvAug_node_cons (α β : AugSeries) (c : BTree)
    (cs : List BTree) :
    bSeriesConvAug α β (BTree.node (c :: cs))
      = α.toFun (BTree.node (c :: cs)) * β.emptyVal
        + ((BTree.innerCutForest (c :: cs) α.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node (forest.filterMap (fun e => e.1))))).sum :=
  bSeriesConvAug_node α β (c :: cs)

/-- Sanity bridge for `bSeriesConvAug_node_cons`: instantiated at
`c = leaf, cs = [leaf]`, the cons-form RHS evaluates to the explicit
two-leaf closed form `bSeriesConvAug_node_two_leaves` (line 329). -/
theorem bSeriesConvAug_node_cons_two_leaves_consistency
    (α β : AugSeries) :
    α.toFun (BTree.node [BTree.leaf, BTree.leaf]) * β.emptyVal
      + ((BTree.innerCutForest (BTree.leaf :: [BTree.leaf]) α.toFun).map
          (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun
                  (BTree.node (forest.filterMap (fun e => e.1))))).sum
      = α.toFun (BTree.node [BTree.leaf, BTree.leaf]) * β.emptyVal
        + β.toFun (BTree.node [BTree.leaf, BTree.leaf])
        + 2 * α.toFun BTree.leaf * β.toFun (BTree.node [BTree.leaf])
        + α.toFun BTree.leaf * α.toFun BTree.leaf
            * β.toFun (BTree.node []) := by
  simp [BTree.innerCutForest, BTree.innerCut]
  ring

/-- Forest-level base case for `bSeriesConvAug`'s inner-forest sum: at the
empty children list there is exactly one forest (the empty list), whose
weight contribution is `β.toFun (BTree.node [])`. -/
theorem bSeriesConvAug_innerForest_nil (α β : AugSeries) :
    ((BTree.innerCutForest [] α.toFun).map (fun forest =>
        forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
          * β.toFun
              (BTree.node (forest.filterMap (fun e => e.1))))).sum
      = β.toFun (BTree.node []) := by
  simp [BTree.innerCutForest]

/-- Auxiliary identity: sum of a flatMap applied through a `head :: forest`
list-cons unfolds as a sum over heads, with each head's contribution
splitting on whether `head.1` is `none` (weight `head.2 * tailSum`) or
`some trunk` (weight `head.2 * forest.foldr * β.toFun (node (trunk :: filt))`). -/
private lemma innerForest_split_aux
    (β : AugSeries) (cs : List BTree) (αFun : BTree → ℝ)
    (L : List (Option BTree × ℝ)) :
    ((L.flatMap (fun head =>
        (BTree.innerCutForest cs αFun).map (fun cs' => head :: cs'))).map
        (fun forest =>
          forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
            * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
      = (L.filterMap (fun head =>
            match head.1 with
            | none => some head.2
            | some _ => none)).sum
              * ((BTree.innerCutForest cs αFun).map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + (L.flatMap (fun head =>
            match head.1 with
            | none => ([] : List ℝ)
            | some trunk =>
              (BTree.innerCutForest cs αFun).map (fun forest =>
                head.2
                  * forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * β.toFun
                      (BTree.node
                        (trunk :: forest.filterMap (fun e => e.1)))))).sum := by
  -- Abbreviate the tail forest sum.
  set tailSum : ℝ :=
      ((BTree.innerCutForest cs αFun).map (fun forest =>
        forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
          * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
    with htail
  induction L with
  | nil => simp [htail]
  | cons head tail ih =>
    rcases hh : head.1 with _ | trunk
    · -- head.1 = none.  The outer filterMap's match emits `some head.2`,
      -- the outer flatMap's match emits `[]`.
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.filterMap_cons, hh, List.map_map, Function.comp_def,
        List.sum_cons, List.nil_append]
      rw [ih]
      -- After simp, the per-head sum has been simplified using `hh` for
      -- the filterMap.  The remaining task is to show the head's
      -- contribution is `head.2 * tailSum`.
      have hphead : ((BTree.innerCutForest cs αFun).map (fun x =>
          (head :: x).foldr (fun e acc => e.2 * acc) (1 : ℝ)
            * β.toFun (BTree.node (x.filterMap (fun e => e.1))))).sum
          = head.2 * tailSum := by
        rw [show (fun x : List (Option BTree × ℝ) =>
                (head :: x).foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * β.toFun (BTree.node (x.filterMap (fun e => e.1))))
              = (fun x => head.2 *
                  (x.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun (BTree.node (x.filterMap (fun e => e.1)))))
              from by
          funext x
          show head.2 * x.foldr (fun e acc => e.2 * acc) (1 : ℝ) * _ = _
          ring]
        rw [List.sum_map_mul_left, htail]
      rw [hphead]
      ring
    · -- head.1 = some trunk.
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.filterMap_cons, hh, List.map_map, Function.comp_def]
      rw [ih]
      -- Show pointwise equality on the per-head sum.
      have hphead : ((BTree.innerCutForest cs αFun).map (fun x =>
          (head :: x).foldr (fun e acc => e.2 * acc) (1 : ℝ)
            * β.toFun
                (BTree.node (trunk :: x.filterMap (fun e => e.1))))).sum
          = ((BTree.innerCutForest cs αFun).map (fun x =>
              head.2 * x.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun
                    (BTree.node (trunk :: x.filterMap (fun e => e.1))))).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro x _
        show head.2 * x.foldr (fun e acc => e.2 * acc) (1 : ℝ) * _ = _
        ring
      rw [hphead]
      ring

/-- Forest-level cons split for `bSeriesConvAug`.  The inner forest sum on
`c :: cs` decomposes as a per-head two-branch split (prune the head root
vs. keep it) times the inner forest sum on `cs`.  The first summand is
the prune-root branch (weight `α.toFun c`); the second summand collects
the keep-root contributions, indexed by entries of `BTree.innerCut c`
whose first component is `some trunk`. -/
theorem bSeriesConvAug_innerForest_cons (α β : AugSeries)
    (c : BTree) (cs : List BTree) :
    ((BTree.innerCutForest (c :: cs) α.toFun).map (fun forest =>
        forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
          * β.toFun
              (BTree.node (forest.filterMap (fun e => e.1))))).sum
      = α.toFun c
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun
                    (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + ((BTree.innerCut c α.toFun).flatMap (fun head =>
            match head.1 with
            | none      => ([] : List ℝ)
            | some trunk =>
              (BTree.innerCutForest cs α.toFun).map (fun forest =>
                head.2
                  * forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * β.toFun
                      (BTree.node
                        (trunk :: forest.filterMap (fun e => e.1)))))).sum := by
  -- Unfold the cons of innerCutForest.
  have hfc : BTree.innerCutForest (c :: cs) α.toFun
      = (c.innerCut α.toFun).flatMap (fun head =>
          (BTree.innerCutForest cs α.toFun).map (fun cs' => head :: cs')) := by
    rw [BTree.innerCutForest]
  rw [hfc, innerForest_split_aux β cs α.toFun (c.innerCut α.toFun)]
  -- Reduce the filterMap-sum on `c.innerCut α.toFun` to `α.toFun c`.
  have hfilt : ((c.innerCut α.toFun).filterMap (fun head =>
        match head.1 with
        | none => some head.2
        | some _ => none)).sum = α.toFun c := by
    cases c with
    | leaf => simp [BTree.innerCut]
    | node children =>
      rw [innerCut_node]
      simp only [List.filterMap_cons, List.sum_cons]
      have htail :
          (((BTree.innerCutForest children α.toFun).map (fun cs =>
              (some (BTree.node (cs.filterMap (fun c => c.1))),
                cs.foldr (fun c acc => c.2 * acc) (1 : ℝ)))).filterMap
            (fun head =>
              match head.1 with
              | none => some head.2
              | some _ => none)) = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro x hx
        rcases List.mem_map.mp hx with ⟨_, _, rfl⟩
        rfl
      rw [htail]
      simp
  rw [hfilt]

/-- A `BTree` has order at most one iff it is `BTree.leaf` or
`BTree.node []`.  Used to dispatch on depth-1 children in cycle 598's
unital associativity headline. -/
private theorem order_le_one_iff (c : BTree) :
    c.order ≤ 1 ↔ c = BTree.leaf ∨ c = BTree.node [] := by
  cases c with
  | leaf => simp
  | node ch =>
    cases ch with
    | nil => simp
    | cons hd tl =>
      have hpos : 0 < hd.order := BTree.order_pos hd
      simp only [BTree.order_node_sum, List.map_cons, List.sum_cons]
      constructor
      · intro h; omega
      · rintro (h | h) <;> simp_all

/-- Auxiliary `AugSeries`: `β` shifted by prepending a child `c` to the
child list of every node argument.  Used to express the forest-level
cons recurrence for depth-1 children.  The `BTree.leaf` branch of
`toFun` is irrelevant because forest residuals are always node trees. -/
private def AugSeries.shiftBy (β : AugSeries) (c : BTree) : AugSeries where
  emptyVal := β.toFun (BTree.node [c])
  toFun := fun
    | BTree.leaf => 0
    | BTree.node xs => β.toFun (BTree.node (c :: xs))

@[simp] private theorem AugSeries.shiftBy_node (β : AugSeries) (c : BTree)
    (xs : List BTree) :
    (β.shiftBy c).toFun (BTree.node xs) = β.toFun (BTree.node (c :: xs)) := rfl

/-- Cons recurrence for `bSeriesConvAug`'s inner-forest sum when the head
child `c` has order ≤ 1.  In that case `c.innerCut α.toFun` has exactly
two entries (the trivial prune and the no-prune), so the keep-root
contribution from `bSeriesConvAug_innerForest_cons` simplifies to a
forest sum on `cs` with `β` shifted by `c`. -/
private theorem forestSum_cons_depth_one (α β : AugSeries) (c : BTree)
    (hc : c.order ≤ 1) (cs : List BTree) :
    ((BTree.innerCutForest (c :: cs) α.toFun).map (fun forest =>
        forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
          * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
      = α.toFun c
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + ((BTree.innerCutForest cs α.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * (β.shiftBy c).toFun
                  (BTree.node (forest.filterMap (fun e => e.1))))).sum := by
  rw [bSeriesConvAug_innerForest_cons]
  congr 1
  rcases (order_le_one_iff c).mp hc with rfl | rfl
  · -- c = BTree.leaf
    rw [innerCut_leaf]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply congrArg List.sum
    apply List.map_congr_left
    intro forest _
    simp [AugSeries.shiftBy]
  · -- c = BTree.node []
    rw [innerCut_node_nil]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply congrArg List.sum
    apply List.map_congr_left
    intro forest _
    simp [AugSeries.shiftBy]

/-- Pointwise expansion of `bSeriesConvAug β γ` at a depth-1 head cons.
Combines `bSeriesConvAug_node` with `forestSum_cons_depth_one` to peel
the head `c` off the residual node argument.  Used inside
`forestSum_assoc_depth_one` to rewrite the RHS keep-root term. -/
private lemma bSeriesConvAug_node_cons_depth_one_expand
    (β γ : AugSeries) (c : BTree) (hc : c.order ≤ 1) (xs : List BTree) :
    bSeriesConvAug β γ (BTree.node (c :: xs))
      = β.toFun (BTree.node (c :: xs)) * γ.emptyVal
        + β.toFun c
          * ((BTree.innerCutForest xs β.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * γ.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + ((BTree.innerCutForest xs β.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * γ.toFun
                  (BTree.node (c :: forest.filterMap (fun e => e.1))))).sum := by
  rw [bSeriesConvAug_node β γ (c :: xs),
      forestSum_cons_depth_one β γ c hc xs]
  simp only [AugSeries.shiftBy_node]
  ring

/-- Forest-level associativity for unital `β`, valid for any `γ` (not
necessarily unital), on lists of order-1 children.  The third summand
on the LHS uses `γ.emptyVal` to compensate for the keep-root branch on
the inner `bSeriesConvAug β γ` expansion in the RHS — it vanishes in
the unital headline.

Universal in `γ` so that the inductive step (peeling head `c`) can
specialize to both `γ` and `γ.shiftBy c`. -/
private theorem forestSum_assoc_depth_one (α β : AugSeries) (hβ : β.IsUnital) :
    ∀ (children : List BTree), (∀ c ∈ children, c.order ≤ 1) →
      ∀ (γ : AugSeries),
        ((BTree.innerCutForest children
            (fun σ => bSeriesConvAug α β σ)).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * γ.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + ((BTree.innerCutForest children α.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
            * γ.emptyVal
        = ((BTree.innerCutForest children α.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * bSeriesConvAug β γ
                  (BTree.node (forest.filterMap (fun e => e.1))))).sum := by
  have hβ' : β.emptyVal = 1 := hβ
  intro children
  induction children with
  | nil =>
    intro _ γ
    simp only [BTree.innerCutForest, List.map_cons, List.map_nil,
               List.sum_cons, List.sum_nil, List.foldr_nil,
               List.filterMap_nil, one_mul, add_zero]
    rw [bSeriesConvAug_node_nil β γ]
    ring
  | cons c cs ih =>
    intro hch γ
    have hc : c.order ≤ 1 := hch c List.mem_cons_self
    have hcs : ∀ c' ∈ cs, c'.order ≤ 1 :=
      fun c' hc' => hch c' (List.mem_cons_of_mem c hc')
    -- IH instances
    have hih_γ := ih hcs γ
    have hih_γc := ih hcs (γ.shiftBy c)
    -- bSCA α β c reduces for c of order ≤ 1 under unital β
    have hgβ_c : bSeriesConvAug α β c = α.toFun c + β.toFun c := by
      rcases (order_le_one_iff c).mp hc with rfl | rfl
      · rw [bSeriesConvAug_leaf, hβ']; ring
      · rw [bSeriesConvAug_node_nil, hβ']; ring
    -- Apply forestSum_cons_depth_one to expand each forestSum on (c::cs).
    rw [show (fun σ : BTree => bSeriesConvAug α β σ)
          = (⟨1, fun σ => bSeriesConvAug α β σ⟩ : AugSeries).toFun from rfl,
        forestSum_cons_depth_one ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ c hc cs,
        forestSum_cons_depth_one α β c hc cs]
    -- For the RHS, package the residual as an AugSeries and apply.
    rw [show (fun forest : List (Option BTree × ℝ) =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * bSeriesConvAug β γ
                    (BTree.node (forest.filterMap (fun e => e.1))))
          = (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * (⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).toFun
                    (BTree.node (forest.filterMap (fun e => e.1)))) from rfl,
        forestSum_cons_depth_one α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ c hc cs]
    -- Beta-reduce structure projections.
    simp only [AugSeries.shiftBy_node]
    -- Substitute bSCA α β c.
    rw [hgβ_c]
    -- Pointwise expansion: bSCA β γ (node(c::xs)) decomposes via two
    -- applications of bSeriesConvAug_node into a polynomial in
    -- bSCA β γ (node xs), bSCA β (γ.shiftBy c) (node xs), and β (node ·).
    have keyPt : ∀ xs : List BTree,
        bSeriesConvAug β γ (BTree.node (c :: xs))
          = β.toFun (BTree.node (c :: xs)) * γ.emptyVal
            + β.toFun c
              * (bSeriesConvAug β γ (BTree.node xs)
                  - β.toFun (BTree.node xs) * γ.emptyVal)
            + (bSeriesConvAug β (γ.shiftBy c) (BTree.node xs)
                - β.toFun (BTree.node xs) * (γ.shiftBy c).emptyVal) := by
      intro xs
      have hS1 : ((BTree.innerCutForest xs β.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * γ.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
            = bSeriesConvAug β γ (BTree.node xs)
                - β.toFun (BTree.node xs) * γ.emptyVal := by
        rw [bSeriesConvAug_node β γ xs]; ring
      have hS2 : ((BTree.innerCutForest xs β.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * γ.toFun
                  (BTree.node (c :: forest.filterMap (fun e => e.1))))).sum
            = bSeriesConvAug β (γ.shiftBy c) (BTree.node xs)
                - β.toFun (BTree.node xs) * (γ.shiftBy c).emptyVal := by
        rw [bSeriesConvAug_node β (γ.shiftBy c) xs]
        simp only [AugSeries.shiftBy_node]; ring
      rw [bSeriesConvAug_node_cons_depth_one_expand β γ c hc xs, hS1, hS2]
    -- Lift the pointwise expansion to a sum-level identity by list induction.
    have aux : ∀ (L : List (List (Option BTree × ℝ))),
        (L.map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * bSeriesConvAug β γ
                  (BTree.node (c :: forest.filterMap (fun e => e.1))))).sum
          = (L.map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun
                    (BTree.node (c :: forest.filterMap (fun e => e.1))))).sum
              * γ.emptyVal
            + β.toFun c
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
                  * bSeriesConvAug β (γ.shiftBy c)
                      (BTree.node (forest.filterMap (fun e => e.1))))).sum
              - (L.map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * β.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
                  * (γ.shiftBy c).emptyVal) := by
      intro L
      induction L with
      | nil => simp
      | cons fhd ftl ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        rw [keyPt (fhd.filterMap (fun e => e.1))]
        ring
    -- Apply aux + IH at γ + IH at γ.shiftBy c to close keyAgg.
    have keyAgg :
        ((BTree.innerCutForest cs α.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * bSeriesConvAug β γ
                  (BTree.node (c :: forest.filterMap (fun e => e.1))))).sum
          = ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun
                    (BTree.node (c :: forest.filterMap (fun e => e.1))))).sum
              * γ.emptyVal
            + β.toFun c
              * ((BTree.innerCutForest cs
                    (fun σ => bSeriesConvAug α β σ)).map (fun forest =>
                  forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                    * γ.toFun
                        (BTree.node (forest.filterMap (fun e => e.1))))).sum
            + ((BTree.innerCutForest cs
                  (fun σ => bSeriesConvAug α β σ)).map (fun forest =>
                forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                  * γ.toFun
                      (BTree.node
                        (c :: forest.filterMap (fun e => e.1))))).sum := by
      rw [aux (BTree.innerCutForest cs α.toFun)]
      simp only [AugSeries.shiftBy_node] at hih_γc
      linear_combination -β.toFun c * hih_γ - hih_γc
    -- Conclude by linear combination of IH and the aggregate decomposition.
    linear_combination α.toFun c * hih_γ - keyAgg

/-- **Cycle 598 headline (depth-1 mixed children)**: unital
associativity of `bSeriesConvAug` at any node whose root children all
have order ≤ 1, i.e. each root child is `BTree.leaf` or
`BTree.node []`.  Generalises the four landed slices
`mul_assoc_at_node_replicate_leaf`,
`mul_assoc_at_node_replicate_node_nil`,
`mul_assoc_at_node_two_leaves`, and `mul_assoc_at_node_two_node_nils`
to arbitrary mixed-leaf / `node []` children at the root.  Strictly
smaller than the full unital associativity headline (which would need
mutual `BTree.rec` / `List.rec` and is bigger than one cycle). -/
theorem mul_assoc_at_node_depth_one_children
    (α β γ : AugSeries) (_ : α.IsUnital) (hβ : β.IsUnital) (hγ : γ.IsUnital)
    (children : List BTree) (hch : ∀ c ∈ children, c.order ≤ 1) :
    bSeriesConvAug ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ (BTree.node children)
      = bSeriesConvAug α ⟨1, fun σ => bSeriesConvAug β γ σ⟩
          (BTree.node children) := by
  have hβ' : β.emptyVal = 1 := hβ
  have hγ' : γ.emptyVal = 1 := hγ
  -- Expand both sides via bSeriesConvAug_node, then expand the inner
  -- bSeriesConvAug α β on the LHS via bSeriesConvAug_node again.
  rw [bSeriesConvAug_node ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ children,
      bSeriesConvAug_node α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ children]
  show bSeriesConvAug α β (BTree.node children) * γ.emptyVal + _
       = α.toFun (BTree.node children) * 1 + _
  rw [bSeriesConvAug_node α β children, hβ', hγ', mul_one, mul_one]
  have key := forestSum_assoc_depth_one α β hβ children hch γ
  rw [hγ', mul_one] at key
  -- Beta-reduce the AugSeries field projections so that linarith sees
  -- the same forest-sum expressions as `key`.
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

/-- Cons recurrence for the inner-forest sum when the head child is the
depth-2 shape `BTree.node [d]` with `d.order ≤ 1`.  The two keep-root
branches are the child-pruned trunk `node []` and the no-prune trunk
`node [d]`. -/
private theorem forestSum_cons_node_singleton_depth_one
    (α β : AugSeries) (d : BTree) (hd : d.order ≤ 1) (cs : List BTree) :
    ((BTree.innerCutForest (BTree.node [d] :: cs) α.toFun).map (fun forest =>
        forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
          * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
      = α.toFun (BTree.node [d])
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + α.toFun d
          * ((BTree.innerCutForest cs α.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * (β.shiftBy (BTree.node [])).toFun
                    (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + ((BTree.innerCutForest cs α.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * (β.shiftBy (BTree.node [d])).toFun
                  (BTree.node (forest.filterMap (fun e => e.1))))).sum := by
  rw [bSeriesConvAug_innerForest_cons]
  rcases (order_le_one_iff d).mp hd with rfl | rfl
  · rw [innerCut_node_singleton_leaf]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Option.isSome, Bool.true_eq_false, ↓reduceIte, List.map_append,
      List.sum_append, List.map_map, Function.comp_def, List.filterMap_cons,
      Option.map_some, List.foldr_cons, one_mul, AugSeries.shiftBy_node]
    have hscale :
        (List.map
            (fun forest =>
              α.toFun BTree.leaf * forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun
                    (BTree.node
                      (BTree.node [] :: forest.filterMap (fun e => e.1))))
            (BTree.innerCutForest cs α.toFun)).sum
          = α.toFun BTree.leaf
              * (List.map
                  (fun forest =>
                    forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                      * β.toFun
                          (BTree.node
                            (BTree.node [] :: forest.filterMap (fun e => e.1))))
                  (BTree.innerCutForest cs α.toFun)).sum := by
      induction BTree.innerCutForest cs α.toFun with
      | nil => simp
      | cons forest tail ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ring
    rw [hscale]
    simp
    ring
  · rw [innerCut_node]
    simp only [BTree.innerCutForest, innerCut_node_nil, List.map_cons,
      List.map_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil,
      List.filterMap_cons, List.filterMap_nil, List.foldr_cons,
      List.foldr_nil, mul_one, one_mul, Option.map_none, Option.map_some,
      List.map_append, List.sum_append, List.map_map, Function.comp_def,
      AugSeries.shiftBy_node]
    have hscale :
        (List.map
            (fun forest =>
              α.toFun (BTree.node []) * forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * β.toFun
                    (BTree.node
                      (BTree.node [] :: forest.filterMap (fun e => e.1))))
            (BTree.innerCutForest cs α.toFun)).sum
          = α.toFun (BTree.node [])
              * (List.map
                  (fun forest =>
                    forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                      * β.toFun
                          (BTree.node
                            (BTree.node [] :: forest.filterMap (fun e => e.1))))
                  (BTree.innerCutForest cs α.toFun)).sum := by
      induction BTree.innerCutForest cs α.toFun with
      | nil => simp
      | cons forest tail ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ring
    rw [hscale]
    simp
    ring

/-- Pointwise expansion of `bSeriesConvAug β γ` at a cons whose head is
`BTree.node [d]` with `d.order ≤ 1`. -/
private lemma bSeriesConvAug_node_cons_node_singleton_depth_one_expand
    (β γ : AugSeries) (d : BTree) (hd : d.order ≤ 1) (xs : List BTree) :
    bSeriesConvAug β γ (BTree.node (BTree.node [d] :: xs))
      = β.toFun (BTree.node (BTree.node [d] :: xs)) * γ.emptyVal
        + β.toFun (BTree.node [d])
          * ((BTree.innerCutForest xs β.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * γ.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + β.toFun d
          * ((BTree.innerCutForest xs β.toFun).map (fun forest =>
              forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
                * γ.toFun
                    (BTree.node
                      (BTree.node [] :: forest.filterMap (fun e => e.1))))).sum
        + ((BTree.innerCutForest xs β.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * γ.toFun
                  (BTree.node
                    (BTree.node [d] :: forest.filterMap (fun e => e.1))))).sum := by
  rw [bSeriesConvAug_node β γ (BTree.node [d] :: xs),
      forestSum_cons_node_singleton_depth_one β γ d hd xs]
  simp only [AugSeries.shiftBy_node]
  ring

/-- The recurring forest-sum contribution in the node form of
`bSeriesConvAug`.  Kept private so the public statements can continue to
match the expanded textbook-facing form. -/
private noncomputable def forestSum (coeff : BTree → ℝ) (δ : AugSeries)
    (children : List BTree) : ℝ :=
  ((BTree.innerCutForest children coeff).map (fun forest =>
    forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
      * δ.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum

private theorem forestSum_cons_depth_one_compact
    (α β : AugSeries) (c : BTree) (hc : c.order ≤ 1) (cs : List BTree) :
    forestSum α.toFun β (c :: cs)
      = α.toFun c * forestSum α.toFun β cs
        + forestSum α.toFun (β.shiftBy c) cs := by
  simpa [forestSum] using forestSum_cons_depth_one α β c hc cs

private theorem forestSum_cons_node_singleton_depth_one_compact
    (α β : AugSeries) (d : BTree) (hd : d.order ≤ 1) (cs : List BTree) :
    forestSum α.toFun β (BTree.node [d] :: cs)
      = α.toFun (BTree.node [d]) * forestSum α.toFun β cs
        + α.toFun d * forestSum α.toFun (β.shiftBy (BTree.node [])) cs
        + forestSum α.toFun (β.shiftBy (BTree.node [d])) cs := by
  simpa [forestSum] using
    forestSum_cons_node_singleton_depth_one α β d hd cs

private lemma bSeriesConvAug_node_cons_depth_one_expand_compact
    (β γ : AugSeries) (c : BTree) (hc : c.order ≤ 1) (xs : List BTree) :
    bSeriesConvAug β γ (BTree.node (c :: xs))
      = β.toFun (BTree.node (c :: xs)) * γ.emptyVal
        + β.toFun c * forestSum β.toFun γ xs
        + forestSum β.toFun (γ.shiftBy c) xs := by
  simpa [forestSum] using
    bSeriesConvAug_node_cons_depth_one_expand β γ c hc xs

private lemma bSeriesConvAug_node_cons_node_singleton_depth_one_expand_compact
    (β γ : AugSeries) (d : BTree) (hd : d.order ≤ 1) (xs : List BTree) :
    bSeriesConvAug β γ (BTree.node (BTree.node [d] :: xs))
      = β.toFun (BTree.node (BTree.node [d] :: xs)) * γ.emptyVal
        + β.toFun (BTree.node [d]) * forestSum β.toFun γ xs
        + β.toFun d * forestSum β.toFun (γ.shiftBy (BTree.node [])) xs
        + forestSum β.toFun (γ.shiftBy (BTree.node [d])) xs := by
  simpa [forestSum] using
    bSeriesConvAug_node_cons_node_singleton_depth_one_expand β γ d hd xs

/-- Forest-level associativity for unital `β`, valid for any `γ`, on
lists whose children have order at most two.  This is the cycle 599
structural step: the head child may itself be a one-child depth-1 node,
while the tail is handled by induction. -/
private theorem forestSum_assoc_depth_two (α β : AugSeries) (hβ : β.IsUnital) :
    ∀ (children : List BTree), (∀ c ∈ children, c.order ≤ 2) →
      ∀ (γ : AugSeries),
        ((BTree.innerCutForest children
            (fun σ => bSeriesConvAug α β σ)).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * γ.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
        + ((BTree.innerCutForest children α.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * β.toFun (BTree.node (forest.filterMap (fun e => e.1))))).sum
            * γ.emptyVal
        = ((BTree.innerCutForest children α.toFun).map (fun forest =>
            forest.foldr (fun e acc => e.2 * acc) (1 : ℝ)
              * bSeriesConvAug β γ
                  (BTree.node (forest.filterMap (fun e => e.1))))).sum := by
  have hβ' : β.emptyVal = 1 := hβ
  intro children
  induction children with
  | nil =>
    intro _ γ
    simp only [BTree.innerCutForest, List.map_cons, List.map_nil,
               List.sum_cons, List.sum_nil, List.foldr_nil,
               List.filterMap_nil, one_mul, add_zero]
    rw [bSeriesConvAug_node_nil β γ]
    ring
  | cons c cs ih =>
    intro hch γ
    have hc2 : c.order ≤ 2 := hch c List.mem_cons_self
    have hcs : ∀ c' ∈ cs, c'.order ≤ 2 :=
      fun c' hc' => hch c' (List.mem_cons_of_mem c hc')
    have hih_γ := ih hcs γ
    change forestSum (fun σ => bSeriesConvAug α β σ) γ cs
        + forestSum α.toFun β cs * γ.emptyVal
      = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩ cs at hih_γ
    change forestSum (fun σ => bSeriesConvAug α β σ) γ (c :: cs)
        + forestSum α.toFun β (c :: cs) * γ.emptyVal
      = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩ (c :: cs)

    have shift_depth_one_agg (m : BTree) (hm : m.order ≤ 1) :
        forestSum α.toFun
            ((⟨1, fun σ => bSeriesConvAug β γ σ⟩ : AugSeries).shiftBy m) cs
          = forestSum α.toFun (β.shiftBy m) cs * γ.emptyVal
            + β.toFun m * forestSum (fun σ => bSeriesConvAug α β σ) γ cs
            + forestSum (fun σ => bSeriesConvAug α β σ) (γ.shiftBy m) cs := by
      have hih_γm := ih hcs (γ.shiftBy m)
      change forestSum (fun σ => bSeriesConvAug α β σ) (γ.shiftBy m) cs
          + forestSum α.toFun β cs * (γ.shiftBy m).emptyVal
        = forestSum α.toFun
            ⟨1, fun σ => bSeriesConvAug β (γ.shiftBy m) σ⟩ cs at hih_γm
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

    have shift_singleton_agg (d : BTree) (hd : d.order ≤ 1) :
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
      have hih_γn := ih hcs (γ.shiftBy (BTree.node []))
      change forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [])) cs
          + forestSum α.toFun β cs * (γ.shiftBy (BTree.node [])).emptyVal
        = forestSum α.toFun
            ⟨1, fun σ => bSeriesConvAug β (γ.shiftBy (BTree.node [])) σ⟩ cs
          at hih_γn
      have hih_γd := ih hcs (γ.shiftBy (BTree.node [d]))
      change forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [d])) cs
          + forestSum α.toFun β cs * (γ.shiftBy (BTree.node [d])).emptyVal
        = forestSum α.toFun
            ⟨1, fun σ => bSeriesConvAug β (γ.shiftBy (BTree.node [d])) σ⟩ cs
          at hih_γd
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

    have depth_one_head_case (m : BTree) (hm : m.order ≤ 1) :
        forestSum (fun σ => bSeriesConvAug α β σ) γ (m :: cs)
          + forestSum α.toFun β (m :: cs) * γ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩
            (m :: cs) := by
      have hih_γm := ih hcs (γ.shiftBy m)
      change forestSum (fun σ => bSeriesConvAug α β σ) (γ.shiftBy m) cs
          + forestSum α.toFun β cs * (γ.shiftBy m).emptyVal
        = forestSum α.toFun
            ⟨1, fun σ => bSeriesConvAug β (γ.shiftBy m) σ⟩ cs at hih_γm
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
      rw [hgβ_m, shift_depth_one_agg m hm]
      linear_combination α.toFun m * hih_γ

    have singleton_head_case (d : BTree) (hd : d.order ≤ 1) :
        forestSum (fun σ => bSeriesConvAug α β σ) γ
            (BTree.node [d] :: cs)
          + forestSum α.toFun β (BTree.node [d] :: cs) * γ.emptyVal
        = forestSum α.toFun ⟨1, fun σ => bSeriesConvAug β γ σ⟩
            (BTree.node [d] :: cs) := by
      have hih_γn := ih hcs (γ.shiftBy (BTree.node []))
      change forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [])) cs
          + forestSum α.toFun β cs * (γ.shiftBy (BTree.node [])).emptyVal
        = forestSum α.toFun
            ⟨1, fun σ => bSeriesConvAug β (γ.shiftBy (BTree.node [])) σ⟩ cs
          at hih_γn
      have hih_γd := ih hcs (γ.shiftBy (BTree.node [d]))
      change forestSum (fun σ => bSeriesConvAug α β σ)
            (γ.shiftBy (BTree.node [d])) cs
          + forestSum α.toFun β cs * (γ.shiftBy (BTree.node [d])).emptyVal
        = forestSum α.toFun
            ⟨1, fun σ => bSeriesConvAug β (γ.shiftBy (BTree.node [d])) σ⟩ cs
          at hih_γd
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
      rw [hgβ_node, hgβ_d, shift_depth_one_agg (BTree.node []) (by simp),
        shift_singleton_agg d hd]
      linear_combination α.toFun (BTree.node [d]) * hih_γ

    rcases (BTree.order_le_two_iff c).mp hc2 with rfl | rfl | rfl | rfl
    · exact depth_one_head_case BTree.leaf (by simp)
    · exact depth_one_head_case (BTree.node []) (by simp)
    · exact singleton_head_case BTree.leaf (by simp)
    · exact singleton_head_case (BTree.node []) (by simp)

/-- **Cycle 599 headline (depth-2 mixed children)**: unital
associativity of `bSeriesConvAug` at any node whose root children all
have order ≤ 2. -/
theorem mul_assoc_at_node_depth_two_children
    (α β γ : AugSeries) (hβ : β.IsUnital) (hγ : γ.IsUnital)
    (children : List BTree) (hchildren : ∀ c ∈ children, c.order ≤ 2) :
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
  have key := forestSum_assoc_depth_two α β hβ children hchildren γ
  rw [hγ', mul_one] at key
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
