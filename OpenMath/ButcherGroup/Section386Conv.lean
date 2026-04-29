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

end ButcherTableau
