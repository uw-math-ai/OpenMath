import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section384
import OpenMath.ButcherGroup.Section384Slices

/-! # §384 mixed-slice common helpers (cycle 564 split)

Foundational `elementaryWeight` and `bSeries` closed-form helpers for
nodes whose root children are replicated leaves, singleton-leaves,
double-leaves, or triple-leaves. Plus two powerset-binomial helpers
used across the mixed-slice families.

Originally part of the monolithic `Section384SlicesMixed.lean`. Cycle
564 split that file into family submodules; the helpers used by more
than one submodule live here. Helpers used only inside this file
remain `private`; helpers used by another sibling submodule are
non-`private` so they can be re-imported.
-/

open Finset

namespace ButcherTableau

variable {s : ℕ}

theorem elementaryWeight_node_replicate_leaf
    {s : ℕ} (tab : ButcherTableau s) (n : ℕ) (i : Fin s) :
    tab.elementaryWeight (BTree.node (List.replicate n BTree.leaf)) i
      = (∑ k : Fin s, tab.A i k) ^ n := by
  induction n with
  | zero => simp [ButcherTableau.elementaryWeight]
  | succ m ih =>
    rw [List.replicate_succ]
    have hfold :
        tab.elementaryWeight (BTree.node (BTree.leaf :: List.replicate m BTree.leaf)) i
          = tab.elementaryWeight (BTree.node (List.replicate m BTree.leaf)) i *
              (∑ k : Fin s, tab.A i k) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih, pow_succ]

theorem convAt_singleton_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.convAt t₂ coef (BTree.node [BTree.leaf]) i
      = coef BTree.leaf + ∑ j : Fin t, t₂.A i j := by
  rw [← ButcherProduct.rightAuxAtCoef_eq_convAt]
  rw [ButcherProduct.rightAuxAtCoef_node_singleton]
  simp [ButcherProduct.rightAuxAtCoef_leaf]

private theorem elementaryWeight_node_replicate_singleton_leaf
    {s : ℕ} (tab : ButcherTableau s) (n : ℕ) (i : Fin s) :
    tab.elementaryWeight (BTree.node (List.replicate n (BTree.node [BTree.leaf]))) i
      = (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ n := by
  induction n with
  | zero => simp [ButcherTableau.elementaryWeight]
  | succ m ih =>
    rw [List.replicate_succ]
    have hfold :
        tab.elementaryWeight
            (BTree.node (BTree.node [BTree.leaf] ::
              List.replicate m (BTree.node [BTree.leaf]))) i
          = tab.elementaryWeight
              (BTree.node (List.replicate m (BTree.node [BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j *
                tab.elementaryWeight (BTree.node [BTree.leaf]) j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih]
    have hchild :
        (∑ j : Fin s, tab.A i j * tab.elementaryWeight (BTree.node [BTree.leaf]) j)
          = ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ButcherTableau.elementaryWeight_singleton]
      simp
    rw [hchild, pow_succ]

private theorem elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf
    {s : ℕ} (tab : ButcherTableau s) (a b : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node (List.replicate a BTree.leaf ++
          List.replicate b (BTree.node [BTree.leaf]))) i
      = (∑ j : Fin s, tab.A i j) ^ a *
        (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b := by
  induction a with
  | zero => simp [elementaryWeight_node_replicate_singleton_leaf]
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    have hfold :
        tab.elementaryWeight
            (BTree.node (BTree.leaf ::
              (List.replicate m BTree.leaf ++
                List.replicate b (BTree.node [BTree.leaf])))) i
          = tab.elementaryWeight
              (BTree.node (List.replicate m BTree.leaf ++
                List.replicate b (BTree.node [BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih, pow_succ]
    ring

theorem bSeries_node_replicate_leaf_append_replicate_singleton_leaf
    {s : ℕ} (tab : ButcherTableau s) (a b : ℕ) :
    tab.bSeries
        (BTree.node (List.replicate a BTree.leaf ++
          List.replicate b (BTree.node [BTree.leaf])))
      = ∑ i : Fin s, tab.b i *
          ((∑ j : Fin s, tab.A i j) ^ a *
            (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b) := by
  unfold ButcherTableau.bSeries
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf]

/-- Helper: the elementary weight of a node whose children are `n`
double-leaf nodes collapses to the `n`-th power of the depth-2 squared-row
factor. -/
private theorem elementaryWeight_node_replicate_double_leaf
    {s : ℕ} (tab : ButcherTableau s) (n : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf]))) i
      = (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) ^ n := by
  induction n with
  | zero =>
    simp [ButcherTableau.elementaryWeight]
  | succ m ih =>
    rw [List.replicate_succ]
    have hfold :
        tab.elementaryWeight
            (BTree.node
              (BTree.node [BTree.leaf, BTree.leaf] ::
                List.replicate m (BTree.node [BTree.leaf, BTree.leaf]))) i
          = tab.elementaryWeight
              (BTree.node
                (List.replicate m (BTree.node [BTree.leaf, BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j *
                tab.elementaryWeight (BTree.node [BTree.leaf, BTree.leaf]) j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih]
    have hchild :
        (∑ j : Fin s, tab.A i j *
          tab.elementaryWeight (BTree.node [BTree.leaf, BTree.leaf]) j)
          = ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact congrArg (fun z => tab.A i j * z)
        (elementaryWeight_node_replicate_leaf tab 2 j)
    rw [hchild, pow_succ]

/-- Helper for mixed kept-side summands with singleton-leaf and double-leaf
children. -/
private theorem elementaryWeight_node_replicate_singleton_leaf_append_replicate_double_leaf
    {s : ℕ} (tab : ButcherTableau s) (b c : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node
          (List.replicate b (BTree.node [BTree.leaf]) ++
            List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))) i
      = (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b *
        (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) ^ c := by
  induction b with
  | zero =>
    simp [elementaryWeight_node_replicate_double_leaf]
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    have hfold :
        tab.elementaryWeight
            (BTree.node
              (BTree.node [BTree.leaf] ::
                (List.replicate m (BTree.node [BTree.leaf]) ++
                  List.replicate c (BTree.node [BTree.leaf, BTree.leaf])))) i
          = tab.elementaryWeight
              (BTree.node
                (List.replicate m (BTree.node [BTree.leaf]) ++
                  List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j *
                tab.elementaryWeight (BTree.node [BTree.leaf]) j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih]
    have hchild :
        (∑ j : Fin s, tab.A i j *
          tab.elementaryWeight (BTree.node [BTree.leaf]) j)
          = ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ButcherTableau.elementaryWeight_singleton]
      simp
    rw [hchild, pow_succ]
    ring

/-- Helper for mixed kept-side summands with leaf, singleton-leaf, and
double-leaf children. -/
private theorem
    elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf
    {s : ℕ} (tab : ButcherTableau s) (a b c : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))) i
      = (∑ j : Fin s, tab.A i j) ^ a *
        (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b *
        (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) ^ c := by
  induction a with
  | zero =>
    simp [elementaryWeight_node_replicate_singleton_leaf_append_replicate_double_leaf]
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append]
    have hfold :
        tab.elementaryWeight
            (BTree.node
              (BTree.leaf ::
                (List.replicate m BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf]) ++
                    List.replicate c (BTree.node [BTree.leaf, BTree.leaf])))) i
          = tab.elementaryWeight
              (BTree.node
                (List.replicate m BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf]) ++
                    List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih, pow_succ]
    ring

/-- `bSeries` form of the mixed leaf/singleton-leaf/double-leaf elementary
weight helper. -/
theorem
    bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf
    {s : ℕ} (tab : ButcherTableau s) (a b c : ℕ) :
    tab.bSeries
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf])))
      = ∑ i : Fin s, tab.b i *
          ((∑ j : Fin s, tab.A i j) ^ a *
            (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b *
            (∑ j : Fin s,
              tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) ^ c) := by
  unfold ButcherTableau.bSeries
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf]

/-- Helper: the elementary weight of a node whose children are `n`
triple-leaf nodes collapses to the `n`-th power of the depth-2 cubed-row
factor. -/
private theorem elementaryWeight_node_replicate_triple_leaf
    {s : ℕ} (tab : ButcherTableau s) (n : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node
          (List.replicate n (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i
      = (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 3) ^ n := by
  induction n with
  | zero =>
    simp [ButcherTableau.elementaryWeight]
  | succ m ih =>
    rw [List.replicate_succ]
    have hfold :
        tab.elementaryWeight
            (BTree.node
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf] ::
                List.replicate m
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i
          = tab.elementaryWeight
              (BTree.node
                (List.replicate m
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j *
                tab.elementaryWeight
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih]
    have hchild :
        (∑ j : Fin s, tab.A i j *
          tab.elementaryWeight
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) j)
          = ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 3 := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact congrArg (fun z => tab.A i j * z)
        (elementaryWeight_node_replicate_leaf tab 3 j)
    rw [hchild, pow_succ]

private theorem
    elementaryWeight_node_replicate_double_leaf_append_replicate_triple_leaf
    {s : ℕ} (tab : ButcherTableau s) (c d : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node
          (List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
            List.replicate d
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i
      = (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) ^ c *
        (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 3) ^ d := by
  induction c with
  | zero =>
    simp [elementaryWeight_node_replicate_triple_leaf]
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    have hfold :
        tab.elementaryWeight
            (BTree.node
              (BTree.node [BTree.leaf, BTree.leaf] ::
                (List.replicate m (BTree.node [BTree.leaf, BTree.leaf]) ++
                  List.replicate d
                    (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))) i
          = tab.elementaryWeight
              (BTree.node
                (List.replicate m (BTree.node [BTree.leaf, BTree.leaf]) ++
                  List.replicate d
                    (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j *
                tab.elementaryWeight (BTree.node [BTree.leaf, BTree.leaf]) j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih]
    have hchild :
        (∑ j : Fin s, tab.A i j *
          tab.elementaryWeight (BTree.node [BTree.leaf, BTree.leaf]) j)
          = ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact congrArg (fun z => tab.A i j * z)
        (elementaryWeight_node_replicate_leaf tab 2 j)
    rw [hchild, pow_succ]
    ring

private theorem
    elementaryWeight_node_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf
    {s : ℕ} (tab : ButcherTableau s) (b c d : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node
          (List.replicate b (BTree.node [BTree.leaf]) ++
            List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
              List.replicate d
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i
      = (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b *
        (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) ^ c *
        (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 3) ^ d := by
  induction b with
  | zero =>
    simp [elementaryWeight_node_replicate_double_leaf_append_replicate_triple_leaf]
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append]
    have hfold :
        tab.elementaryWeight
            (BTree.node
              (BTree.node [BTree.leaf] ::
                (List.replicate m (BTree.node [BTree.leaf]) ++
                  List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
                    List.replicate d
                      (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))) i
          = tab.elementaryWeight
              (BTree.node
                (List.replicate m (BTree.node [BTree.leaf]) ++
                  List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
                    List.replicate d
                      (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j *
                tab.elementaryWeight (BTree.node [BTree.leaf]) j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih]
    have hchild :
        (∑ j : Fin s, tab.A i j *
          tab.elementaryWeight (BTree.node [BTree.leaf]) j)
          = ∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ButcherTableau.elementaryWeight_singleton]
      simp
    rw [hchild, pow_succ]
    ring

private theorem
    elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf
    {s : ℕ} (tab : ButcherTableau s) (a b c d : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
                List.replicate d
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i
      = (∑ j : Fin s, tab.A i j) ^ a *
        (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b *
        (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) ^ c *
        (∑ j : Fin s,
          tab.A i j * (∑ k : Fin s, tab.A j k) ^ 3) ^ d := by
  induction a with
  | zero =>
    simpa [List.append_assoc] using
      (elementaryWeight_node_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf
        tab b c d i)
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append, List.cons_append]
    have hfold :
        tab.elementaryWeight
            (BTree.node
              (BTree.leaf ::
                (List.replicate m BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf]) ++
                    List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
                      List.replicate d
                        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))) i
          = tab.elementaryWeight
              (BTree.node
                (List.replicate m BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf]) ++
                    List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
                      List.replicate d
                        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih, pow_succ]
    ring

theorem
    bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf
    {s : ℕ} (tab : ButcherTableau s) (a b c d : ℕ) :
    tab.bSeries
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
                List.replicate d
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = ∑ i : Fin s, tab.b i *
          ((∑ j : Fin s, tab.A i j) ^ a *
            (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b *
            (∑ j : Fin s,
              tab.A i j * (∑ k : Fin s, tab.A j k) ^ 2) ^ c *
            (∑ j : Fin s,
              tab.A i j * (∑ k : Fin s, tab.A j k) ^ 3) ^ d) := by
  unfold ButcherTableau.bSeries
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf]

/-- Product-form binomial expansion over an arbitrary finite set. -/
theorem prod_const_add_eq_powerset {α : Type*} [DecidableEq α]
    (s : Finset α) (x y : ℝ) :
    (∏ _p ∈ s, (x + y))
      = ∑ T ∈ s.powerset, x ^ T.card * y ^ (s.card - T.card) := by
  classical
  rw [Finset.prod_add]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro T hT
  have hsub : T ⊆ s := Finset.mem_powerset.mp hT
  rw [Finset.prod_const, Finset.prod_const, Finset.card_sdiff_of_subset hsub]

/-- Powerset-indexed binomial expansion of `(x + y)^n`. -/
theorem pow_add_eq_powerset (x y : ℝ) (n : ℕ) :
    (x + y) ^ n
      = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
          x ^ T.card * y ^ (n - T.card) := by
  classical
  calc
    (x + y) ^ n = ∏ _p : Fin n, (x + y) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
          x ^ T.card * y ^ ((Finset.univ : Finset (Fin n)).card - T.card) := by
      rw [prod_const_add_eq_powerset]
    _ = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
          x ^ T.card * y ^ (n - T.card) := by
      simp [Fintype.card_fin]

end ButcherTableau
