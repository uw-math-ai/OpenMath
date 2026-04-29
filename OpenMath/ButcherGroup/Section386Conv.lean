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

/-- Proper bSeries-side cut convolution for inverse recursion.  The no-cut
trunk has the same order as `τ`, so this helper asks only for coefficients of
strictly smaller trunks and contributes `0` to the no-cut branch. -/
noncomputable def bSeriesConvNonRoot (α : BTree → ℝ) (τ : BTree)
    (β : ∀ σ : BTree, σ.order < τ.order → ℝ) : ℝ :=
  ((τ.innerCut α).filterMap fun c =>
    c.1.map fun trunk =>
      if h : trunk.order < τ.order then c.2 * β trunk h else 0).sum

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

theorem bSeriesConv_node_node_nil_consistency
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    t₁.bSeries (BTree.node [BTree.node []])
      + bSeriesConv (t₁.bSeries) (t₂.bSeries) (BTree.node [BTree.node []])
    = (ButcherProduct t₁ t₂).bSeries (BTree.node [BTree.node []]) := by
  rw [ButcherProduct.bSeries_node_node_nil_eq]
  simp [bSeriesConv, BTree.innerCut, BTree.innerCutForest]
  rw [bSeries_node_node_nil t₁, bSeries_node_node_nil t₂, bSeries_node_nil t₂]
  ring

/-! ### Cycle 568: list-to-powerset reindexing for the all-leaves family.

The cycle 567 singleton-leaf consistency check is now extended to the
parametric `BTree.node (List.replicate n BTree.leaf)` family. The pure
combinatorial bridge from the list enumeration of inner cuts to the
existing `Finset (Fin n)` powerset sum is captured by
`innerCutForest_replicate_leaf_sum`. -/

/-- Cons unfolding of `BTree.innerCutForest` on a leaf prefix:
prepending one leaf splits as kept-head and cut-head over the tail forest. -/
private theorem innerCutForest_leaf_cons (α : BTree → ℝ) (tail : List BTree) :
    BTree.innerCutForest (BTree.leaf :: tail) α
      = (BTree.innerCutForest tail α).map
          (fun cs => (some BTree.leaf, (1 : ℝ)) :: cs)
        ++ (BTree.innerCutForest tail α).map
            (fun cs => (none, α BTree.leaf) :: cs) := by
  conv_lhs => rw [BTree.innerCutForest]
  rw [innerCut_leaf]
  simp [List.flatMap]

/-- Cons unfolding of `BTree.innerCutForest` on an empty-node prefix:
prepending one `node []` splits as cut-head and kept-head over the tail forest. -/
private theorem innerCutForest_node_nil_cons (α : BTree → ℝ) (tail : List BTree) :
    BTree.innerCutForest (BTree.node [] :: tail) α
      = (BTree.innerCutForest tail α).map
          (fun cs => (none, α (BTree.node [])) :: cs)
        ++ (BTree.innerCutForest tail α).map
          (fun cs => (some (BTree.node []), (1 : ℝ)) :: cs) := by
  conv_lhs => rw [BTree.innerCutForest]
  rw [innerCut_node_nil]
  simp [List.flatMap]

/-- Cardinality decomposition: a sum over `Finset (Fin (n+1))` indexed by
cardinality is the kept-head/cut-head split over `Finset (Fin n)`. -/
private lemma sum_finset_fin_succ_card_eq {M : Type*} [AddCommMonoid M] (n : ℕ)
    (φ : ℕ → M) :
    ∑ S' : Finset (Fin (n + 1)), φ S'.card
      = (∑ S : Finset (Fin n), φ S.card)
      + ∑ S : Finset (Fin n), φ (S.card + 1) := by
  classical
  -- Convert each Finset-sum to a `range`/`choose` sum, then use Pascal.
  have h_univ_pow : ∀ m : ℕ,
      (Finset.univ : Finset (Finset (Fin m))) =
        (Finset.univ : Finset (Fin m)).powerset := by
    intro m; ext; simp
  have key : ∀ m : ℕ, ∀ ψ : ℕ → M,
      ∑ S : Finset (Fin m), ψ S.card =
        ∑ k ∈ Finset.range (m + 1), m.choose k • ψ k := by
    intro m ψ
    rw [show (∑ S : Finset (Fin m), ψ S.card) =
          ∑ S ∈ (Finset.univ : Finset (Finset (Fin m))), ψ S.card from rfl]
    rw [h_univ_pow m, Finset.sum_powerset_apply_card ψ]
    simp [Finset.card_univ, Fintype.card_fin]
  rw [key (n + 1) φ, key n φ, key n (fun k => φ (k + 1))]
  -- Reindex the second sum: k → k + 1, picking up `range_succ`.
  rw [Finset.sum_range_succ' (fun k => (n + 1).choose k • φ k) (n + 1)]
  simp only [Nat.choose_zero_right, one_smul]
  -- LHS now: (∑ k ∈ range (n+1), (n+1).choose (k+1) • φ (k+1)) + φ 0
  -- RHS: (∑ k ∈ range (n+1), n.choose k • φ k) + (∑ k ∈ range (n+1), n.choose k • φ (k+1))
  rw [Finset.sum_range_succ' (fun k => n.choose k • φ k) n]
  simp only [Nat.choose_zero_right, one_smul]
  -- Goal now: (∑ k ∈ range (n+1), (n+1).choose (k+1) • φ (k+1)) + φ 0
  --   = ((∑ k ∈ range n, n.choose (k+1) • φ (k+1)) + φ 0) + ∑ k ∈ range (n+1), n.choose k • φ (k+1)
  rw [add_assoc, add_comm (φ 0), ← add_assoc]
  congr 1
  rw [Finset.sum_range_succ (fun k => n.choose k • φ (k + 1)) n]
  -- Now: ∑ k ∈ range (n+1), (n+1).choose (k+1) • φ (k+1)
  --    = ∑ k ∈ range n, n.choose (k+1) • φ (k+1)
  --      + ((∑ k ∈ range n, n.choose k • φ (k+1)) + n.choose n • φ (n+1))
  rw [Finset.sum_range_succ (fun k => (n+1).choose (k + 1) • φ (k+1)) n]
  rw [show (n + 1).choose (n + 1) = 1 from Nat.choose_self _, one_smul]
  rw [show n.choose n = 1 from Nat.choose_self _, one_smul]
  rw [show (∑ k ∈ Finset.range n, (n+1).choose (k+1) • φ (k+1))
        = ∑ k ∈ Finset.range n,
            (n.choose (k+1) • φ (k+1) + n.choose k • φ (k+1)) from by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Nat.choose_succ_succ', add_smul, add_comm]]
  rw [Finset.sum_add_distrib]
  abel

/-- A `BTree`-coefficient version of the cut sum on a leaf-only forest:
the filterMap-style admissible cut sum equals the simpler list-map form
because the kept option is always `some`. -/
private theorem cutSum_filterMap_eq_map (β : BTree → ℝ)
    (F : List (List (Option BTree × ℝ))) :
    List.filterMap
      ((fun c : Option BTree × ℝ => Option.map (fun t => c.2 * β t) c.1) ∘ fun cs =>
        (some (BTree.node (List.filterMap (fun c => c.1) cs)),
         List.foldr (fun c acc => c.2 * acc) 1 cs)) F
      = List.map
        (fun cs => List.foldr (fun c acc => c.2 * acc) 1 cs *
              β (BTree.node (List.filterMap (fun c => c.1) cs))) F := by
  rw [List.filterMap_eq_map_iff_forall_eq_some.mpr]
  intro cs _
  simp [Function.comp]

/-- The list enumeration of inner cuts of `BTree.node (List.replicate n BTree.leaf)`
reindexes to the `Finset (Fin n)` powerset sum from cycle 542. -/
private theorem innerCutForest_replicate_leaf_sum (α β : BTree → ℝ) (n : ℕ) :
    (List.filterMap
        ((fun c => Option.map (fun t => c.2 * β t) c.1) ∘ fun cs =>
          (some (BTree.node (List.filterMap (fun c => c.1) cs)),
           List.foldr (fun c acc => c.2 * acc) 1 cs))
        (BTree.innerCutForest (List.replicate n BTree.leaf) α)).sum
      =
        ∑ S : Finset (Fin n),
          α BTree.leaf ^ S.card *
            β (BTree.node (List.replicate (n - S.card) BTree.leaf)) := by
  induction n generalizing β with
  | zero =>
      rw [cutSum_filterMap_eq_map]
      simp [BTree.innerCutForest]
      rw [show (default : Finset (Fin 0)) = ∅ from rfl]
      simp
  | succ n ih =>
      rw [cutSum_filterMap_eq_map β,
          List.replicate_succ, innerCutForest_leaf_cons,
          List.map_append, List.sum_append,
          List.map_map, List.map_map]
      -- Kept branch: re-express via β_kept (xs ↦ β(leaf :: xs)).
      let β_kept : BTree → ℝ := fun t =>
        match t with
        | BTree.leaf => 0
        | BTree.node xs => β (BTree.node (BTree.leaf :: xs))
      have hkept_fun :
          ((fun cs : List (Option BTree × ℝ) =>
              List.foldr (fun c acc => c.2 * acc) 1 cs *
                β (BTree.node (List.filterMap (fun c => c.1) cs))) ∘
            fun cs => (some BTree.leaf, (1 : ℝ)) :: cs)
            = (fun cs : List (Option BTree × ℝ) =>
                List.foldr (fun c acc => c.2 * acc) 1 cs *
                  β_kept (BTree.node (List.filterMap (fun c => c.1) cs))) := by
        funext cs
        simp [Function.comp, β_kept, one_mul]
      have hcut_fun :
          ((fun cs : List (Option BTree × ℝ) =>
              List.foldr (fun c acc => c.2 * acc) 1 cs *
                β (BTree.node (List.filterMap (fun c => c.1) cs))) ∘
            fun cs => (none, α BTree.leaf) :: cs)
            = (fun cs : List (Option BTree × ℝ) =>
                α BTree.leaf *
                  (List.foldr (fun c acc => c.2 * acc) 1 cs *
                    β (BTree.node (List.filterMap (fun c => c.1) cs)))) := by
        funext cs
        simp [Function.comp]
        ring
      rw [hkept_fun, hcut_fun]
      -- Re-fold both via cutSum_filterMap_eq_map for IH application.
      rw [show (List.map (fun cs : List (Option BTree × ℝ) =>
            List.foldr (fun c acc => c.2 * acc) 1 cs *
              β_kept (BTree.node (List.filterMap (fun c => c.1) cs)))
            (BTree.innerCutForest (List.replicate n BTree.leaf) α))
          = List.filterMap
              ((fun c : Option BTree × ℝ =>
                  Option.map (fun t => c.2 * β_kept t) c.1) ∘ fun cs =>
                (some (BTree.node (List.filterMap (fun c => c.1) cs)),
                 List.foldr (fun c acc => c.2 * acc) 1 cs))
              (BTree.innerCutForest (List.replicate n BTree.leaf) α) from
          (cutSum_filterMap_eq_map β_kept _).symm]
      have hcut_factor :
          (List.map (fun cs : List (Option BTree × ℝ) =>
                α BTree.leaf *
                  (List.foldr (fun c acc => c.2 * acc) 1 cs *
                    β (BTree.node (List.filterMap (fun c => c.1) cs))))
              (BTree.innerCutForest (List.replicate n BTree.leaf) α)).sum
            = α BTree.leaf *
              (List.filterMap
                  ((fun c : Option BTree × ℝ =>
                      Option.map (fun t => c.2 * β t) c.1) ∘ fun cs =>
                    (some (BTree.node (List.filterMap (fun c => c.1) cs)),
                     List.foldr (fun c acc => c.2 * acc) 1 cs))
                  (BTree.innerCutForest (List.replicate n BTree.leaf) α)).sum := by
        rw [cutSum_filterMap_eq_map β]
        induction (BTree.innerCutForest (List.replicate n BTree.leaf) α) with
        | nil => simp
        | cons head tail ih' =>
            simp [List.map_cons, List.sum_cons, ih', mul_add]
      rw [hcut_factor, ih β_kept, ih β]
      -- RHS via Pascal split.
      rw [sum_finset_fin_succ_card_eq n
            (fun k => α BTree.leaf ^ k *
              β (BTree.node (List.replicate ((n + 1) - k) BTree.leaf)))]
      -- Match each branch.
      have hkept_match :
          (∑ S : Finset (Fin n), α BTree.leaf ^ S.card *
              β_kept (BTree.node (List.replicate (n - S.card) BTree.leaf)))
            = ∑ S : Finset (Fin n), α BTree.leaf ^ S.card *
                β (BTree.node (List.replicate ((n + 1) - S.card) BTree.leaf)) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        have hle : S.card ≤ n := by
          have := S.card_le_univ
          simpa [Finset.card_univ, Fintype.card_fin] using this
        congr 2
        show β_kept (BTree.node (List.replicate (n - S.card) BTree.leaf))
              = β (BTree.node (List.replicate ((n + 1) - S.card) BTree.leaf))
        simp [β_kept, ← List.replicate_succ, Nat.succ_sub hle]
      have hcut_match :
          α BTree.leaf *
              (∑ S : Finset (Fin n), α BTree.leaf ^ S.card *
                β (BTree.node (List.replicate (n - S.card) BTree.leaf)))
            = ∑ S : Finset (Fin n), α BTree.leaf ^ (S.card + 1) *
                β (BTree.node (List.replicate ((n + 1) - (S.card + 1)) BTree.leaf)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro S _
        have hsub : (n + 1) - (S.card + 1) = n - S.card := by omega
        rw [hsub, pow_succ]
        ring
      rw [hkept_match, hcut_match]

/-- The list enumeration of inner cuts of
`BTree.node (List.replicate n (BTree.node []))` reindexes to the
`Finset (Fin n)` powerset sum from the §384 all-empty-node closed form. -/
private theorem innerCutForest_replicate_node_nil_sum (α β : BTree → ℝ) (n : ℕ) :
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
          List.replicate_succ, innerCutForest_node_nil_cons,
          List.map_append, List.sum_append,
          List.map_map, List.map_map]
      -- Cut branch: the head is pruned, contributing its coefficient.
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
      -- Kept branch: re-express via `β_kept (xs) = β(node [] :: xs)`.
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

/-- Headline parametric all-leaves consistency for `bSeriesConv`:
`t₂` cuts on a leaf-children node decompose into the cycle 542 product
closed form once the trunk-keeping `t₁`-correction is added. -/
theorem bSeriesConv_node_replicate_leaf_consistency
    {s_ t_ : ℕ} (t₁ : ButcherTableau s_) (t₂ : ButcherTableau t_) (n : ℕ) :
    bSeriesConv (fun τ => t₁.bSeries τ) (fun τ => t₂.bSeries τ)
        (BTree.node (List.replicate n BTree.leaf))
      + t₁.bSeries (BTree.node (List.replicate n BTree.leaf))
    = (ButcherProduct t₁ t₂).bSeries
        (BTree.node (List.replicate n BTree.leaf)) := by
  rw [ButcherProduct.bSeries_node_replicate_leaf_eq]
  unfold bSeriesConv
  rw [innerCut_node]
  -- The leading `(none, α (node ...))` is filtered out (root pruned), leaving the
  -- list enumeration mapped over `innerCutForest`.
  simp only [List.filterMap_cons, Option.map_none, List.filterMap_map]
  rw [innerCutForest_replicate_leaf_sum
        (fun τ => t₁.bSeries τ) (fun τ => t₂.bSeries τ) n]
  rw [add_comm]
  rfl

/-- Headline parametric all-empty-node consistency for `bSeriesConv`:
`t₂` cuts on a `node []`-children node decompose into the cycle 544
product closed form once the trunk-keeping `t₁`-correction is added. -/
theorem bSeriesConv_node_replicate_node_nil_consistency
    {s_ t_ : ℕ} (t₁ : ButcherTableau s_) (t₂ : ButcherTableau t_) (n : ℕ) :
    bSeriesConv (fun τ => t₁.bSeries τ) (fun τ => t₂.bSeries τ)
        (BTree.node (List.replicate n (BTree.node [])))
      + t₁.bSeries (BTree.node (List.replicate n (BTree.node [])))
    = (ButcherProduct t₁ t₂).bSeries
        (BTree.node (List.replicate n (BTree.node []))) := by
  rw [ButcherProduct.bSeries_node_replicate_node_nil_eq]
  unfold bSeriesConv
  rw [innerCut_node]
  simp only [List.filterMap_cons, Option.map_none, List.filterMap_map]
  rw [innerCutForest_replicate_node_nil_sum
        (fun τ => t₁.bSeries τ) (fun τ => t₂.bSeries τ) n]
  rw [add_comm]
  rfl

/-- Stagewise root-preserving inner-cut sum, indexed by a stage `i` of
the second method. Bridges `bSeriesConv` (which evaluates trunks via
`t₂.bSeries`) to the recursion needed by `convAt`. -/
noncomputable def cutAt (α : BTree → ℝ) {t : ℕ} (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin t) : ℝ :=
  ((τ.innerCut α).filterMap fun c =>
    c.1.map (fun trunk => c.2 * t₂.elementaryWeight trunk i)).sum

@[simp]
theorem cutAt_leaf (α : BTree → ℝ) {t : ℕ} (t₂ : ButcherTableau t)
    (i : Fin t) :
    cutAt α t₂ BTree.leaf i = 1 := by
  simp [cutAt, BTree.innerCut]

@[simp]
theorem cutAt_node_nil (α : BTree → ℝ) {t : ℕ} (t₂ : ButcherTableau t)
    (i : Fin t) :
    cutAt α t₂ (BTree.node []) i = 1 := by
  simp [cutAt, BTree.innerCut, BTree.innerCutForest]

private theorem list_sum_flatMap {α : Type*} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [List.flatMap, List.sum_append]
      change (List.map (fun a => (f a).sum) l).sum =
        (List.map (fun a => (f a).sum) l).sum
      rfl

private theorem list_sum_mul_finset_sum {ι γ : Type*} [Fintype ι]
    (L : List γ) (a : ι → ℝ) (w : γ → ℝ) (g : γ → ι → ℝ) :
    (L.map (fun x => w x * (∑ j : ι, a j * g x j))).sum
      = ∑ j : ι, a j * (L.map fun x => w x * g x j).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, ih, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp
      ring

private theorem cutAt_node_eq_innerCutForest_sum
    (α : BTree → ℝ) {t : ℕ} (t₂ : ButcherTableau t) (i : Fin t)
    (children : List BTree) :
    cutAt α t₂ (BTree.node children) i =
      (List.map
        (fun cs =>
          (cs.foldr (fun c acc => c.2 * acc) 1)
            * t₂.elementaryWeight
                (BTree.node (cs.filterMap fun c => c.1)) i)
        (BTree.innerCutForest children α)).sum := by
  unfold cutAt
  rw [innerCut_node]
  simp only [List.filterMap_cons, Option.map_none, List.filterMap_map]
  rw [cutSum_filterMap_eq_map (fun τ => t₂.elementaryWeight τ i)]

private theorem innerCut_stage_factor_sum_eq
    (α : BTree → ℝ) {t : ℕ} (t₂ : ButcherTableau t) (i : Fin t)
    (τ : BTree) :
    (List.map
        (fun c : Option BTree × ℝ =>
          match c.1 with
          | none => c.2
          | some trunk =>
              c.2 * (∑ j : Fin t, t₂.A i j * t₂.elementaryWeight trunk j))
        (τ.innerCut α)).sum
      = α τ + ∑ j : Fin t, t₂.A i j * cutAt α t₂ τ j := by
  cases τ with
  | leaf =>
      simp [BTree.innerCut, cutAt]
      ring
  | node children =>
      rw [innerCut_node]
      simp only [List.map_cons, List.sum_cons, List.map_map]
      congr 1
      change (List.map
          (fun cs : List (Option BTree × ℝ) =>
            cs.foldr (fun c acc => c.2 * acc) 1 *
              (∑ j : Fin t, t₂.A i j *
                t₂.elementaryWeight
                  (BTree.node (cs.filterMap fun c => c.1)) j))
          (BTree.innerCutForest children α)).sum
        =
        ∑ j : Fin t, t₂.A i j * cutAt α t₂ (BTree.node children) j
      rw [show
          (∑ j : Fin t, t₂.A i j * cutAt α t₂ (BTree.node children) j)
            =
          ∑ j : Fin t, t₂.A i j *
            (List.map
              (fun cs =>
                cs.foldr (fun c acc => c.2 * acc) 1 *
                  t₂.elementaryWeight
                    (BTree.node (cs.filterMap fun c => c.1)) j)
              (BTree.innerCutForest children α)).sum from by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [cutAt_node_eq_innerCutForest_sum]]
      rw [list_sum_mul_finset_sum
        (BTree.innerCutForest children α)
        (fun j : Fin t => t₂.A i j)
        (fun cs : List (Option BTree × ℝ) => cs.foldr (fun c acc => c.2 * acc) 1)
        (fun cs j => t₂.elementaryWeight
          (BTree.node (cs.filterMap fun c => c.1)) j)]

private theorem innerCutForest_cons_choice_sum
    {t : ℕ} (t₂ : ButcherTableau t) (i : Fin t)
    (forest : List (List (Option BTree × ℝ))) (c : Option BTree × ℝ) :
    (List.map
        (fun cs =>
          ((c :: cs).foldr (fun c acc => c.2 * acc) 1)
            * t₂.elementaryWeight
                (BTree.node ((c :: cs).filterMap fun c => c.1)) i)
        forest).sum
      =
        (match c.1 with
        | none => c.2
        | some trunk =>
            c.2 * (∑ j : Fin t, t₂.A i j * t₂.elementaryWeight trunk j))
        *
        (List.map
          (fun cs =>
            (cs.foldr (fun c acc => c.2 * acc) 1)
              * t₂.elementaryWeight
                  (BTree.node (cs.filterMap fun c => c.1)) i)
          forest).sum := by
  cases c with
  | mk opt w =>
      cases opt with
      | none =>
          simpa [mul_assoc] using
            (List.sum_map_mul_left forest
              (fun cs : List (Option BTree × ℝ) =>
                cs.foldr (fun c acc => c.2 * acc) 1 *
                  t₂.elementaryWeight
                    (BTree.node (cs.filterMap fun c => c.1)) i) w)
      | some trunk =>
          simp only [List.foldr_cons, List.filterMap_cons]
          let row : ℝ := ∑ j : Fin t, t₂.A i j * t₂.elementaryWeight trunk j
          have hfun :
              (fun cs : List (Option BTree × ℝ) =>
                w * cs.foldr (fun c acc => c.2 * acc) 1 *
                  t₂.elementaryWeight
                    (BTree.node (trunk :: List.filterMap (fun c => c.1) cs)) i)
                =
              fun cs : List (Option BTree × ℝ) =>
                (w * row) *
                  (cs.foldr (fun c acc => c.2 * acc) 1 *
                    t₂.elementaryWeight
                      (BTree.node (List.filterMap (fun c => c.1) cs)) i) := by
            funext cs
            simp [row, elementaryWeight_node_cons]
            ring
          rw [hfun]
          simpa [row, mul_assoc] using
            (List.sum_map_mul_left forest
              (fun cs : List (Option BTree × ℝ) =>
                cs.foldr (fun c acc => c.2 * acc) 1 *
                  t₂.elementaryWeight
                    (BTree.node (cs.filterMap fun c => c.1)) i) (w * row))

private theorem innerCutForest_sum_foldr_eq
    (α : BTree → ℝ) {t : ℕ} (t₂ : ButcherTableau t) (i : Fin t)
    (children : List BTree) :
    (List.map
        (fun cs =>
          (cs.foldr (fun c acc => c.2 * acc) 1)
            * t₂.elementaryWeight
                (BTree.node (cs.filterMap fun c => c.1)) i)
        (BTree.innerCutForest children α)).sum
      = children.foldr
          (fun child acc =>
            acc * (α child + ∑ j : Fin t, t₂.A i j * cutAt α t₂ child j)) 1 := by
  induction children with
  | nil =>
      simp [BTree.innerCutForest, ButcherTableau.elementaryWeight]
  | cons head tail ih =>
      conv_lhs => rw [BTree.innerCutForest]
      rw [List.map_flatMap, list_sum_flatMap]
      simp only [List.map_map]
      rw [show
          (List.map
            (fun a : Option BTree × ℝ =>
              (List.map
                ((fun cs =>
                  cs.foldr (fun c acc => c.2 * acc) 1 *
                    t₂.elementaryWeight (BTree.node (cs.filterMap fun c => c.1)) i) ∘
                    fun cs => a :: cs)
                (BTree.innerCutForest tail α)).sum)
            (head.innerCut α)).sum
          =
          (List.map
            (fun a : Option BTree × ℝ =>
              (match a.1 with
              | none => a.2
              | some trunk =>
                  a.2 * (∑ j : Fin t, t₂.A i j *
                    t₂.elementaryWeight trunk j)) *
              (List.map
                (fun cs =>
                  cs.foldr (fun c acc => c.2 * acc) 1 *
                    t₂.elementaryWeight (BTree.node (cs.filterMap fun c => c.1)) i)
                (BTree.innerCutForest tail α)).sum)
            (head.innerCut α)).sum from by
              refine congrArg List.sum ?_
              refine List.map_congr_left ?_
              intro a ha
              simpa [Function.comp] using
                (innerCutForest_cons_choice_sum t₂ i
                  (BTree.innerCutForest tail α) a)]
      rw [List.sum_map_mul_right]
      rw [innerCut_stage_factor_sum_eq, ih]
      simp [List.foldr]
      ring

private theorem foldr_mul_add_eq_powerset_sum_stage {α : Type*}
    (children : List α) (x y : α → ℝ) :
    children.foldr (fun c acc => acc * (x c + y c)) 1
      = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ k ∈ T, x children[k]) * ∏ k ∈ Finset.univ \ T, y children[k] := by
  have hprod : children.foldr (fun c acc => acc * (x c + y c)) 1
      = ∏ k : Fin children.length, (x children[k] + y children[k]) := by
    induction children with
    | nil => simp
    | cons c cs ih =>
      show cs.foldr (fun c acc => acc * (x c + y c)) 1 * (x c + y c)
           = ∏ k : Fin (cs.length + 1), (x (c :: cs)[k] + y (c :: cs)[k])
      rw [ih, Fin.prod_univ_succ]
      have h0 : (c :: cs)[(0 : Fin (cs.length + 1))] = c := rfl
      have hsucc : ∀ k : Fin cs.length,
          (c :: cs)[(k.succ : Fin (cs.length + 1))] = cs[k] := fun _ => rfl
      rw [h0]
      simp_rw [hsucc]
      ring
  rw [hprod, Finset.prod_add]

private theorem innerCutForest_stage_sum_eq
    (α : BTree → ℝ) {t : ℕ} (t₂ : ButcherTableau t) (i : Fin t)
    (children : List BTree)
    (IH : ∀ c ∈ children, ∀ j : Fin t,
      cutAt α t₂ c j = ButcherProduct.convAt t₂ α c j) :
    (List.map
        (fun cs =>
          (cs.foldr (fun c acc => c.2 * acc) 1)
            * t₂.elementaryWeight
                (BTree.node (cs.filterMap fun c => c.1)) i)
        (BTree.innerCutForest children α)).sum
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ S, α (children.get p))
            * ∏ p ∈ Sᶜ,
                (∑ j : Fin t, t₂.A i j *
                  ButcherProduct.convAt t₂ α (children.get p) j) := by
  rw [innerCutForest_sum_foldr_eq]
  rw [foldr_mul_add_eq_powerset_sum_stage children
    (fun c => α c)
    (fun c => ∑ j : Fin t, t₂.A i j * cutAt α t₂ c j)]
  rw [Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  refine Finset.prod_congr rfl ?_
  intro p hp
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [show children[p] = children.get p from rfl]
  rw [IH (children.get p) (List.get_mem children p) j]

theorem cutAt_eq_convAt (α : BTree → ℝ) {t : ℕ} (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin t) :
    cutAt α t₂ τ i = ButcherProduct.convAt t₂ α τ i := by
  revert i
  induction τ using BTree.rec
    (motive_2 := fun children =>
      ∀ c ∈ children, ∀ j : Fin t,
        cutAt α t₂ c j = ButcherProduct.convAt t₂ α c j) with
  | leaf =>
      intro i
      simp [cutAt_leaf, ButcherProduct.convAt_leaf]
  | node children IH =>
      intro i
      rw [cutAt_node_eq_innerCutForest_sum,
        innerCutForest_stage_sum_eq α t₂ i children IH,
        ButcherProduct.convAt_node]
  | nil c hc j => simp at hc
  | cons head tail ih_head ih_tail c hc j =>
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact ih_head j
      · exact ih_tail c hmem j

private theorem option_filterMap_sum_eq_map (β : BTree → ℝ)
    (L : List (Option BTree × ℝ)) :
    (L.filterMap fun c => c.1.map (fun trunk => c.2 * β trunk)).sum
      =
    (L.map fun c =>
      match c.1 with
      | none => 0
      | some trunk => c.2 * β trunk).sum := by
  induction L with
  | nil => simp
  | cons c cs ih =>
      cases c with
      | mk opt w =>
          cases opt <;> simp [ih]

private theorem option_weighted_sum_comm
    {t : ℕ} (t₂ : ButcherTableau t)
    (L : List (Option BTree × ℝ)) :
    (L.map
        (fun c =>
          match c.1 with
          | none => 0
          | some trunk => c.2 * t₂.bSeries trunk)).sum
      =
    ∑ i : Fin t, t₂.b i *
      (L.map
        (fun c =>
          match c.1 with
          | none => 0
          | some trunk => c.2 * t₂.elementaryWeight trunk i)).sum := by
  induction L with
  | nil => simp
  | cons c cs ih =>
      cases c with
      | mk opt w =>
          cases opt with
          | none =>
              simp [ih]
          | some trunk =>
              rw [List.map_cons, List.sum_cons, ih]
              unfold bSeries
              change w * (∑ i : Fin t, t₂.b i * t₂.elementaryWeight trunk i) +
                  ∑ i : Fin t, t₂.b i *
                    (cs.map
                      (fun c =>
                        match c.1 with
                        | none => 0
                        | some trunk => c.2 * t₂.elementaryWeight trunk i)).sum
                =
                ∑ i : Fin t, t₂.b i *
                  (w * t₂.elementaryWeight trunk i +
                    (cs.map
                      (fun c =>
                        match c.1 with
                        | none => 0
                        | some trunk => c.2 * t₂.elementaryWeight trunk i)).sum)
              rw [show
                  w * (∑ i : Fin t, t₂.b i * t₂.elementaryWeight trunk i)
                    = ∑ i : Fin t, t₂.b i * (w * t₂.elementaryWeight trunk i) from by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro i _
                    ring]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i _
              ring

private theorem bSeriesConv_eq_b_weighted_cutAt
    {t : ℕ} (t₂ : ButcherTableau t) (α : BTree → ℝ) (τ : BTree) :
    bSeriesConv α (t₂.bSeries) τ
      = ∑ i : Fin t, t₂.b i * cutAt α t₂ τ i := by
  unfold bSeriesConv cutAt
  rw [option_filterMap_sum_eq_map (fun τ => t₂.bSeries τ)]
  rw [option_weighted_sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [option_filterMap_sum_eq_map (fun trunk => t₂.elementaryWeight trunk i)]

theorem bSeriesConv_eq_b_weighted_convAt
    {t : ℕ} (t₂ : ButcherTableau t) (α : BTree → ℝ) (τ : BTree) :
    bSeriesConv α (t₂.bSeries) τ
      = ∑ i : Fin t, t₂.b i * ButcherProduct.convAt t₂ α τ i := by
  rw [bSeriesConv_eq_b_weighted_cutAt]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [cutAt_eq_convAt]

theorem ButcherProduct.bSeriesConv_consistency
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (τ : BTree) :
    (ButcherProduct t₁ t₂).bSeries τ
      = t₁.bSeries τ + bSeriesConv (t₁.bSeries) (t₂.bSeries) τ := by
  rw [ButcherProduct.bSeries_eq_split, bSeriesConv_eq_b_weighted_convAt]

/-! ### Cycle 572: locality of `bSeriesConv` in its coefficient maps.

`bSeriesConv α β τ` evaluates `α` and `β` only on subtrees of `τ`. This
locality is the structural prerequisite for the unrestricted
`IsG1Equiv.product_congr` lift in `OpenMath/ButcherGroup.lean`. -/

/-- Locality of `BTree.innerCut` in the cut coefficient `α`. If two
coefficient maps agree on every tree of order at most `p`, the inner-cut
list is the same on every tree of order ≤ `p`. -/
private theorem innerCut_eq_of_agree {α α' : BTree → ℝ} {p : ℕ}
    (hα : ∀ t : BTree, t.order ≤ p → α t = α' t) :
    ∀ τ : BTree, τ.order ≤ p → τ.innerCut α = τ.innerCut α' := by
  intro τ
  induction τ using BTree.rec
    (motive_2 := fun children =>
      (∀ c ∈ children, c.order ≤ p) →
        BTree.innerCutForest children α = BTree.innerCutForest children α')
    with
  | leaf =>
      intro h
      rw [innerCut_leaf, innerCut_leaf, hα BTree.leaf h]
  | node children IH =>
      intro h
      have hchild_le : ∀ c ∈ children, c.order ≤ p := by
        intro c hc
        have hc_in : c.order ∈ children.map BTree.order :=
          List.mem_map_of_mem hc
        have hsum : c.order ≤ (children.map BTree.order).sum :=
          List.single_le_sum (fun n _ => Nat.zero_le n) _ hc_in
        rw [BTree.order_node_sum] at h
        omega
      rw [innerCut_node, innerCut_node, hα _ h, IH hchild_le]
  | nil =>
      rw [BTree.innerCutForest, BTree.innerCutForest]
  | cons head tail ih_head ih_tail =>
      rename_i h
      have h_head : head.order ≤ p := h head List.mem_cons_self
      have h_tail : ∀ c ∈ tail, c.order ≤ p := fun c hc =>
        h c (List.mem_cons_of_mem _ hc)
      have eq_head : head.innerCut α = head.innerCut α' := ih_head h_head
      have eq_tail : BTree.innerCutForest tail α = BTree.innerCutForest tail α' :=
        ih_tail h_tail
      rw [BTree.innerCutForest, BTree.innerCutForest, eq_head, eq_tail]

/-- Structural invariant: every trunk option produced by `BTree.innerCut τ α`
has order at most `τ.order`. The cut coefficient `α` does not affect the
list of trunk options. -/
private theorem innerCut_trunk_order_le
    (α : BTree → ℝ) (τ : BTree) :
    ∀ c ∈ τ.innerCut α, ∀ t : BTree, c.1 = some t → t.order ≤ τ.order := by
  induction τ using BTree.rec
    (motive_2 := fun children =>
      ∀ cs ∈ BTree.innerCutForest children α,
        ((cs.filterMap (fun c => c.1)).map BTree.order).sum
          ≤ (children.map BTree.order).sum) with
  | leaf =>
      intro c hc t ht
      rw [innerCut_leaf] at hc
      simp [List.mem_cons] at hc
      rcases hc with hc | hc
      · rw [hc] at ht
        simp at ht
        rw [← ht]
      · rw [hc] at ht
        simp at ht
  | node children IH =>
      intro c hc t ht
      rw [innerCut_node] at hc
      simp only [List.mem_cons] at hc
      rcases hc with hc | hc
      · rw [hc] at ht; simp at ht
      · rw [List.mem_map] at hc
        obtain ⟨cs, hcs, heq⟩ := hc
        rw [← heq] at ht
        simp at ht
        rw [← ht, BTree.order_node_sum, BTree.order_node_sum]
        have hbound := IH cs hcs
        omega
  | nil =>
      rename_i cs hcs
      rw [BTree.innerCutForest] at hcs
      simp at hcs
      subst hcs
      simp
  | cons head tail ih_head ih_tail =>
      rename_i cs hcs
      rw [BTree.innerCutForest] at hcs
      rw [List.mem_flatMap] at hcs
      obtain ⟨c, hc, hin⟩ := hcs
      rw [List.mem_map] at hin
      obtain ⟨tail_cs, htail_cs, heq⟩ := hin
      rw [← heq]
      have htail_bound :
          ((tail_cs.filterMap (fun d => d.1)).map BTree.order).sum
            ≤ (tail.map BTree.order).sum := ih_tail tail_cs htail_cs
      simp only [List.map_cons, List.sum_cons]
      cases hopt : c.1 with
      | none =>
          simp [hopt]
          omega
      | some t =>
          have ht_bound : t.order ≤ head.order :=
            ih_head c hc t hopt
          simp [hopt, List.map_cons, List.sum_cons]
          omega

/-- List-level β-locality: replacing `β` by `β'` agreeing on entries with
trunk-order at most `p` keeps the filterMap-sum invariant. -/
private theorem sum_filterMap_β_eq_of_agree
    {β β' : BTree → ℝ} {p : ℕ}
    (hβ : ∀ t : BTree, t.order ≤ p → β t = β' t)
    (L : List (Option BTree × ℝ))
    (hL : ∀ c ∈ L, ∀ t : BTree, c.1 = some t → t.order ≤ p) :
    (L.filterMap (fun c => c.1.map (fun t => c.2 * β t))).sum
      = (L.filterMap (fun c => c.1.map (fun t => c.2 * β' t))).sum := by
  induction L with
  | nil => simp
  | cons c tail ih =>
      have hctail : ∀ c' ∈ tail, ∀ t, c'.1 = some t → t.order ≤ p :=
        fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
      cases hopt : c.1 with
      | none =>
          simp [hopt, ih hctail]
      | some t =>
          have ht : t.order ≤ p :=
            hL c List.mem_cons_self t hopt
          simp [hopt, ih hctail, hβ t ht]

/-- **Headline locality** for `bSeriesConv`: replacing both coefficient
maps `α, β` by `α', β'` agreeing on trees of order ≤ `p` keeps
`bSeriesConv α β τ` invariant for every `τ` of order ≤ `p`. -/
theorem bSeriesConv_congr_of_le
    {α α' β β' : BTree → ℝ} {p : ℕ}
    (hα : ∀ t : BTree, t.order ≤ p → α t = α' t)
    (hβ : ∀ t : BTree, t.order ≤ p → β t = β' t)
    {τ : BTree} (hτ : τ.order ≤ p) :
    bSeriesConv α β τ = bSeriesConv α' β' τ := by
  unfold bSeriesConv
  rw [innerCut_eq_of_agree hα τ hτ]
  apply sum_filterMap_β_eq_of_agree hβ
  intro c hc t ht
  have := innerCut_trunk_order_le α' τ c hc t ht
  exact this.trans hτ

/-! ### Cycle 576: structural strengthening of `innerCut_trunk_order_le`.

For the §388 inverse-coefficient cancellation, we need to know that the
*only* entry in `τ.innerCut α` whose trunk option has full order
`τ.order` is the canonical "no cut" entry `(some τ, 1)`. This refines
`innerCut_trunk_order_le` (which only gives `≤`) and lets us peel the
`(some τ, 1)` summand from `bSeriesConv α β τ`. -/

/-- Helper: the canonical no-cut forest entry has trunk filterMap equal
to the children list. -/
private theorem canon_filterMap (children : List BTree) :
    (children.map (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ))).filterMap
      (fun c => c.1) = children := by
  induction children with
  | nil => simp
  | cons h t ih => simp [ih]

/-- Helper: the canonical no-cut forest entry has weight foldr equal to 1. -/
private theorem canon_foldr (children : List BTree) :
    (children.map (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ))).foldr
      (fun c acc => c.2 * acc) (1 : ℝ) = 1 := by
  induction children with
  | nil => simp
  | cons h t ih => simp [ih]

/-- Helper: the canonical no-cut forest entry has trunk-order sum equal
to the children-order sum. -/
private theorem canon_order_sum (children : List BTree) :
    ((children.map (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ))).filterMap
      (fun c => c.1) |>.map BTree.order).sum
      = (children.map BTree.order).sum := by
  rw [canon_filterMap]

/-- Structural strengthening of `innerCut_trunk_order_le`: every entry
in `τ.innerCut α` is either a `none` cut, a `some t` cut with trunk
order strictly less than `τ.order`, or the canonical no-cut
`(some τ, 1)`. The forest-level dual identifies the canonical no-cut
list explicitly as `children.map (fun c => (some c, 1))`. -/
theorem innerCut_root_only_at_full_order
    (α : BTree → ℝ) (τ : BTree) :
    ∀ c ∈ τ.innerCut α,
      c.1 = none
        ∨ (∃ t, c.1 = some t ∧ t.order < τ.order)
        ∨ c = (some τ, 1) := by
  induction τ using BTree.rec
    (motive_2 := fun children =>
      ∀ cs ∈ BTree.innerCutForest children α,
        ((cs.filterMap (fun c => c.1)).map BTree.order).sum
            < (children.map BTree.order).sum
          ∨ cs = children.map (fun c => (some c, (1 : ℝ)))) with
  | leaf =>
      intro c hc
      rw [innerCut_leaf] at hc
      simp at hc
      rcases hc with hc | hc
      · right; right; exact hc
      · left; rw [hc]
  | node children IH =>
      intro c hc
      rw [innerCut_node] at hc
      simp only [List.mem_cons] at hc
      rcases hc with hc | hc
      · left; rw [hc]
      · rw [List.mem_map] at hc
        obtain ⟨cs, hcs, heq⟩ := hc
        have hIH := IH cs hcs
        rcases hIH with hlt | hcanon
        · right; left
          refine ⟨BTree.node (cs.filterMap (fun c => c.1)), ?_, ?_⟩
          · rw [← heq]
          · rw [BTree.order_node_sum, BTree.order_node_sum]; omega
        · right; right
          rw [← heq, hcanon, canon_filterMap, canon_foldr]
  | nil =>
      rename_i cs hcs
      rw [BTree.innerCutForest] at hcs
      simp at hcs
      subst hcs
      right
      simp
  | cons head tail ih_head ih_tail =>
      rename_i cs hcs
      rw [BTree.innerCutForest] at hcs
      rw [List.mem_flatMap] at hcs
      obtain ⟨c, hc, hin⟩ := hcs
      rw [List.mem_map] at hin
      obtain ⟨tail_cs, htail_cs, heq⟩ := hin
      rw [← heq]
      have h_head := ih_head c hc
      have h_tail := ih_tail tail_cs htail_cs
      have h_head_pos : 0 < head.order := BTree.order_pos head
      cases hopt : c.1 with
      | none =>
          left
          simp only [List.filterMap_cons, hopt, List.map_cons, List.sum_cons]
          rcases h_tail with ht | hcanon
          · omega
          · rw [hcanon, canon_filterMap]; omega
      | some t =>
          rcases h_head with hnone | ⟨t', ht'_eq, ht'_lt⟩ | hcanon
          · exfalso; rw [hopt] at hnone; cases hnone
          · rw [hopt] at ht'_eq
            obtain rfl : t' = t := by exact (Option.some.inj ht'_eq.symm)
            left
            simp only [List.filterMap_cons, hopt, List.map_cons, List.sum_cons]
            rcases h_tail with ht | hcanon
            · omega
            · rw [hcanon, canon_filterMap]; omega
          · have hc1 : c.1 = some head := by rw [hcanon]
            have _hc2 : c.2 = 1 := by rw [hcanon]
            rw [hc1] at hopt
            obtain rfl : t = head := by
              have := Option.some.inj hopt
              exact this.symm
            rcases h_tail with ht | hcanon_tail
            · left
              simp only [List.filterMap_cons, hc1, List.map_cons, List.sum_cons]
              omega
            · right
              rw [hcanon, hcanon_tail]
              simp [List.map_cons]

/-! ### Cycle 577: peeling the canonical no-cut summand. -/

private theorem innerCutForest_root_only_at_full_order
    (α : BTree → ℝ) (children : List BTree) :
    ∀ cs ∈ BTree.innerCutForest children α,
      ((cs.filterMap (fun c => c.1)).map BTree.order).sum
          < (children.map BTree.order).sum
        ∨ cs = children.map (fun c => (some c, (1 : ℝ))) := by
  induction children with
  | nil =>
      intro cs hcs
      rw [BTree.innerCutForest] at hcs
      simp at hcs
      subst hcs
      right
      simp
  | cons head tail ih_tail =>
      intro cs hcs
      rw [BTree.innerCutForest] at hcs
      rw [List.mem_flatMap] at hcs
      obtain ⟨c, hc, hin⟩ := hcs
      rw [List.mem_map] at hin
      obtain ⟨tail_cs, htail_cs, heq⟩ := hin
      rw [← heq]
      have h_head := innerCut_root_only_at_full_order α head c hc
      have h_tail := ih_tail tail_cs htail_cs
      have h_head_pos : 0 < head.order := BTree.order_pos head
      cases hopt : c.1 with
      | none =>
          left
          simp only [List.filterMap_cons, hopt, List.map_cons, List.sum_cons]
          rcases h_tail with ht | hcanon
          · omega
          · rw [hcanon, canon_filterMap]; omega
      | some t =>
          rcases h_head with hnone | ⟨t', ht'_eq, ht'_lt⟩ | hcanon
          · exfalso; rw [hopt] at hnone; cases hnone
          · rw [hopt] at ht'_eq
            obtain rfl : t' = t := by exact (Option.some.inj ht'_eq.symm)
            left
            simp only [List.filterMap_cons, hopt, List.map_cons, List.sum_cons]
            rcases h_tail with ht | hcanon
            · omega
            · rw [hcanon, canon_filterMap]; omega
          · have hc1 : c.1 = some head := by rw [hcanon]
            have _hc2 : c.2 = 1 := by rw [hcanon]
            rw [hc1] at hopt
            obtain rfl : t = head := by
              have := Option.some.inj hopt
              exact this.symm
            rcases h_tail with ht | hcanon_tail
            · left
              simp only [List.filterMap_cons, hc1, List.map_cons, List.sum_cons]
              omega
            · right
              rw [hcanon, hcanon_tail]
              simp [List.map_cons]

private theorem list_sum_indicator_eq_countP
    {γ : Type*} [DecidableEq γ] (L : List γ) (a : γ) :
    (L.map (fun x => if x = a then (1 : ℕ) else 0)).sum
      = L.countP (· = a) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : x = a
      · simp [hx, ih, Nat.add_comm]
      · simp [hx, ih]

private theorem list_sum_real_indicator_eq_countP_mul
    {γ : Type*} [DecidableEq γ] (L : List γ) (a : γ) (v : ℝ) :
    (L.map (fun x => if x = a then v else 0)).sum
      = (L.countP (· = a) : ℝ) * v := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : x = a
      · simp [hx, ih]
        ring
      · simp [hx, ih]

private def cutValue (β : BTree → ℝ) (c : Option BTree × ℝ) : ℝ :=
  match c.1 with
  | none => 0
  | some t => c.2 * β t

private def cutValueNonRoot (τ : BTree) (β : BTree → ℝ)
    (c : Option BTree × ℝ) : ℝ :=
  match c.1 with
  | none => 0
  | some t => if t.order < τ.order then c.2 * β t else 0

private theorem filterMap_cutValue_sum
    (β : BTree → ℝ) (L : List (Option BTree × ℝ)) :
    (L.filterMap fun c => c.1.map (fun t => c.2 * β t)).sum
      = (L.map (cutValue β)).sum := by
  induction L with
  | nil => simp
  | cons c cs ih =>
      rcases c with ⟨opt, w⟩
      cases opt <;> simp [cutValue, ih]

private theorem filterMap_cutValueNonRoot_sum
    (τ : BTree) (β : BTree → ℝ) (L : List (Option BTree × ℝ)) :
      (L.filterMap fun c =>
        c.1.map fun trunk =>
          if _h : trunk.order < τ.order then c.2 * β trunk else 0).sum
      = (L.map (cutValueNonRoot τ β)).sum := by
  induction L with
  | nil => simp
  | cons c cs ih =>
      rcases c with ⟨opt, w⟩
      cases opt with
      | none =>
          simpa [cutValueNonRoot] using ih
      | some t =>
          by_cases ht : t.order < τ.order
          · simp [cutValueNonRoot, ht]
            simpa using ih
          · simp [cutValueNonRoot, ht]
            simpa using ih

private theorem cutValue_eq_nonRoot_add_indicator
    (α β : BTree → ℝ) (τ : BTree) (c : Option BTree × ℝ)
    (hc : c ∈ τ.innerCut α) :
    cutValue β c
      = cutValueNonRoot τ β c
        + if c = ((some τ, (1 : ℝ)) : Option BTree × ℝ) then β τ else 0 := by
  by_cases hcanon : c = ((some τ, (1 : ℝ)) : Option BTree × ℝ)
  · subst c
    simp [cutValue, cutValueNonRoot]
  · rcases c with ⟨opt, w⟩
    cases opt with
    | none =>
        simp [cutValue, cutValueNonRoot, hcanon]
    | some t =>
        have hstruct :=
          innerCut_root_only_at_full_order α τ ((some t, w) : Option BTree × ℝ) hc
        rcases hstruct with hnone | hsmall | hcanon'
        · cases hnone
        · rcases hsmall with ⟨t', ht'_eq, ht'_lt⟩
          obtain rfl : t' = t := by exact (Option.some.inj ht'_eq.symm)
          simp [cutValue, cutValueNonRoot, ht'_lt, hcanon]
        · exact (hcanon hcanon').elim

mutual
  private theorem innerCut_canon_count
      (α : BTree → ℝ) (τ : BTree) :
      ((τ.innerCut α).countP
        (· = ((some τ, (1 : ℝ)) : Option BTree × ℝ))) = 1 := by
    cases τ with
    | leaf =>
        simp [BTree.innerCut]
    | node children =>
        rw [innerCut_node]
        simp
        have hpreimage :
            (BTree.innerCutForest children α).countP
                (((fun c : Option BTree × ℝ =>
                    decide (c = ((some (BTree.node children), (1 : ℝ)) :
                      Option BTree × ℝ))) ∘
                  fun cs : List (Option BTree × ℝ) =>
                    (some (BTree.node (cs.filterMap (fun c => c.1))),
                      cs.foldr (fun c acc => c.2 * acc) (1 : ℝ))))
              =
            (BTree.innerCutForest children α).countP
                (· = children.map
                  (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ))) := by
          apply List.countP_congr
          intro cs hcs
          constructor
          · intro hpair_bool
            have hpair :
                (some (BTree.node (cs.filterMap (fun c => c.1))),
                    cs.foldr (fun c acc => c.2 * acc) (1 : ℝ))
                  =
                ((some (BTree.node children), (1 : ℝ)) :
                  Option BTree × ℝ) := by
              simpa [Function.comp] using hpair_bool
            rcases innerCutForest_root_only_at_full_order α children cs hcs with hlt | hcanon
            · have hfst := congrArg Prod.fst hpair
              have hnode :
                  BTree.node (cs.filterMap (fun c => c.1)) =
                    BTree.node children := by
                exact Option.some.inj hfst
              have hfilter : cs.filterMap (fun c => c.1) = children := by
                simpa using BTree.node.inj hnode
              rw [hfilter] at hlt
              exact (Nat.lt_irrefl _ hlt).elim
            · simp [hcanon]
          · intro hcanon_bool
            have hcanon :
                cs = children.map
                  (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ)) := by
              simpa using hcanon_bool
            subst cs
            have hfilter := canon_filterMap children
            have hfold := canon_foldr children
            simp [hfilter, hfold]
        rw [hpreimage]
        exact innerCutForest_canon_count α children

  private theorem innerCutForest_canon_count
      (α : BTree → ℝ) (children : List BTree) :
      ((BTree.innerCutForest children α).countP
        (· = children.map (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ)))) = 1 := by
    cases children with
    | nil =>
        simp [BTree.innerCutForest]
    | cons head tail =>
        rw [BTree.innerCutForest, List.countP_flatMap]
        let headCanon : Option BTree × ℝ := (some head, (1 : ℝ))
        let tailCanon : List (Option BTree × ℝ) :=
          tail.map (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ))
        have hbranch :
            ∀ c ∈ head.innerCut α,
              ((BTree.innerCutForest tail α).map (fun cs => c :: cs)).countP
                  (· = headCanon :: tailCanon)
                = if c = headCanon then 1 else 0 := by
          intro c hc
          by_cases hcanon : c = headCanon
          · subst c
            rw [List.countP_map]
            have hcongr :
                (BTree.innerCutForest tail α).countP
                    (((fun x : List (Option BTree × ℝ) =>
                        decide (x = headCanon :: tailCanon)) ∘
                      fun cs => headCanon :: cs))
                  =
                (BTree.innerCutForest tail α).countP (· = tailCanon) := by
              apply List.countP_congr
              intro cs hcs
              simp [Function.comp]
            rw [hcongr]
            simpa [tailCanon] using innerCutForest_canon_count α tail
          · rw [List.countP_map]
            simp [Function.comp, hcanon]
        have hmap :
            (List.map
                (List.countP (fun x => decide (x = headCanon :: tailCanon)) ∘
                  fun c => (BTree.innerCutForest tail α).map (fun cs => c :: cs))
                (head.innerCut α))
              =
            (head.innerCut α).map (fun c => if c = headCanon then 1 else 0) := by
          apply List.map_congr_left
          intro c hc
          exact hbranch c hc
        change
          (List.map
              (List.countP (fun x => decide (x = headCanon :: tailCanon)) ∘
                fun c => (BTree.innerCutForest tail α).map (fun cs => c :: cs))
              (head.innerCut α)).sum = 1
        rw [hmap, list_sum_indicator_eq_countP]
        simpa [headCanon] using innerCut_canon_count α head
end

theorem bSeriesConv_eq_root_plus_nonRoot
    (α β : BTree → ℝ) (τ : BTree) :
    bSeriesConv α β τ
      = β τ + bSeriesConvNonRoot α τ (fun σ _ => β σ) := by
  unfold bSeriesConv bSeriesConvNonRoot
  rw [filterMap_cutValue_sum β,
    filterMap_cutValueNonRoot_sum τ β]
  let canon : Option BTree × ℝ := (some τ, (1 : ℝ))
  have hmap :
      (τ.innerCut α).map (cutValue β)
        =
      (τ.innerCut α).map
        (fun c => cutValueNonRoot τ β c
          + if c = canon then β τ else 0) := by
    apply List.map_congr_left
    intro c hc
    simpa [canon] using cutValue_eq_nonRoot_add_indicator α β τ c hc
  calc
    ((τ.innerCut α).map (cutValue β)).sum
        = ((τ.innerCut α).map
            (fun c => cutValueNonRoot τ β c
              + if c = canon then β τ else 0)).sum := by
          rw [hmap]
    _ = ((τ.innerCut α).map (cutValueNonRoot τ β)).sum
          + ((τ.innerCut α).map
              (fun c => if c = canon then β τ else 0)).sum := by
          rw [List.sum_map_add]
    _ = ((τ.innerCut α).map (cutValueNonRoot τ β)).sum
          + ((τ.innerCut α).countP (· = canon) : ℝ) * β τ := by
          rw [list_sum_real_indicator_eq_countP_mul]
    _ = ((τ.innerCut α).map (cutValueNonRoot τ β)).sum + β τ := by
          rw [innerCut_canon_count α τ]
          ring
    _ = β τ + ((τ.innerCut α).map (cutValueNonRoot τ β)).sum := by
          ring

end ButcherTableau
