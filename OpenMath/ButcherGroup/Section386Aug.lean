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

end ButcherTableau
