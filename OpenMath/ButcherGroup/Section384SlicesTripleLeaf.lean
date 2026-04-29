import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section384
import OpenMath.ButcherGroup.Section384Slices
import OpenMath.ButcherGroup.Section384SlicesMixed

/-!
# §384 triple-leaf parametric closed-form bSeries product slices (cycle 558)

This module hosts the standalone triple-leaf node closed forms (cycle 557)
together with the parametric all-triple-leaf family
`BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))`.

Cycle 558 split this content out of `Section384SlicesMixed.lean` to keep
that file under the 3000-line cap and to host the cycle-558 parametric
family alongside its `Fin 4` per-kept-child machinery.
-/

open Finset

namespace ButcherTableau

variable {s : ℕ}

/-! ### §384 standalone triple-leaf node slice (cycle 557, moved)

Cycle 557 grouped the all-leaves `n = 3` powerset expansion into the four
binomial cut-count cases. This gives a reusable `Fin 4` symmetric choice
helper for future mixed slices involving the order-4 triple-leaf child. -/

/-- Number of kept leaf children in the triple-leaf grouped expansion.
The `Fin 4` index records the number of cut leaves, so the keep count is
`3, 2, 1, 0`. -/
def tripleLeafChoiceCount (k : Fin 4) : ℕ :=
  match k with
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 0

/-- Binomial coefficient package for the four cut-count cases in
`(X + R)^3`, where `X` is the cut leaf coefficient and `R` is the kept
row-sum factor. -/
noncomputable def tripleLeafChoiceCoef (k : Fin 4) (X R : ℝ) : ℝ :=
  match k with
  | ⟨0, _⟩ => R ^ 3
  | ⟨1, _⟩ => 3 * X * R ^ 2
  | ⟨2, _⟩ => 3 * X ^ 2 * R
  | ⟨3, _⟩ => X ^ 3

/-- Cut count plus keep count is the three leaf children. -/
theorem tripleLeafChoiceCount_sum (k : Fin 4) :
    k.1 + tripleLeafChoiceCount k = 3 := by
  fin_cases k <;> rfl

/-- Grouped binomial expansion for the three identical leaf children. -/
theorem triple_leaf_stage_polynomial_expand (X R : ℝ) :
    (X + R) ^ 3 = ∑ k : Fin 4, tripleLeafChoiceCoef k X R := by
  simp [Fin.sum_univ_four, tripleLeafChoiceCoef]
  ring

/-- Helper: `tripleLeafChoiceCoef k X R` factors as `tripleLeafChoiceCoef k X 1 * R^(3 - k.val)`. -/
private theorem tripleLeafChoiceCoef_factor (k : Fin 4) (X R : ℝ) :
    tripleLeafChoiceCoef k X R
      = tripleLeafChoiceCoef k X 1 * R ^ (tripleLeafChoiceCount k) := by
  fin_cases k <;>
    simp [tripleLeafChoiceCoef, tripleLeafChoiceCount] <;>
      ring

/-- Helper: the elementary weight of a node whose children are `n` leaves
collapses to the `n`-th power of the row sum `∑ k, A i k`. -/
private theorem elementaryWeight_node_replicate_leaf
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

/-- Per-stage `convAt` closed form on the standalone triple-leaf tree. -/
theorem ButcherProduct.convAt_node_triple_leaf_at_i_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.convAt t₂ coef
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) i
      = ∑ k : Fin 4,
          tripleLeafChoiceCoef k (coef BTree.leaf)
            (∑ j : Fin t, t₂.A i j) := by
  let row : ℝ := ∑ j : Fin t, t₂.A i j
  calc
    ButcherProduct.convAt t₂ coef
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) i
        = (coef BTree.leaf + row) ^ 3 := by
          have h :=
            convAt_node_mixed_leaf_singleton_leaf_at_i_eq
              t₂ coef 3 0 i
          simpa [row] using h
    _ = ∑ k : Fin 4, tripleLeafChoiceCoef k (coef BTree.leaf) row := by
          rw [triple_leaf_stage_polynomial_expand]

/-- The `b`-weighted second-tableau contribution on the standalone
triple-leaf tree, grouped by the four possible cut counts. -/
theorem ButcherProduct.bWeighted_convAt_node_triple_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) i)
      = ∑ k : Fin 4,
          tripleLeafChoiceCoef k (coef BTree.leaf) 1 *
            t₂.bSeries
              (BTree.node
                (List.replicate (tripleLeafChoiceCount k) BTree.leaf)) := by
  classical
  let X : ℝ := coef BTree.leaf
  let row : Fin t → ℝ := fun i => ∑ j : Fin t, t₂.A i j
  have hbSeries : ∀ k : Fin 4,
      t₂.bSeries
          (BTree.node (List.replicate (tripleLeafChoiceCount k) BTree.leaf))
        = ∑ i : Fin t, t₂.b i * row i ^ tripleLeafChoiceCount k := by
    intro k
    unfold ButcherTableau.bSeries
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [elementaryWeight_node_replicate_leaf]
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) i)
        = ∑ i : Fin t, t₂.b i *
            (∑ k : Fin 4, tripleLeafChoiceCoef k X (row i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          congr 1
          rw [ButcherProduct.convAt_node_triple_leaf_at_i_eq]
    _ = ∑ k : Fin 4,
          ∑ i : Fin t, t₂.b i * tripleLeafChoiceCoef k X (row i) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ k : Fin 4,
          tripleLeafChoiceCoef k X 1 *
            t₂.bSeries
              (BTree.node
                (List.replicate (tripleLeafChoiceCount k) BTree.leaf)) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hbSeries k]
          fin_cases k
          · simp [tripleLeafChoiceCoef, tripleLeafChoiceCount]
          · simp [tripleLeafChoiceCoef, tripleLeafChoiceCount]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
          · simp [tripleLeafChoiceCoef, tripleLeafChoiceCount]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
          · simp [tripleLeafChoiceCoef, tripleLeafChoiceCount]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring

/-- §384 honest convolution closed form on the standalone triple-leaf tree,
grouped by the four possible leaf cut counts. -/
theorem ButcherProduct.bConv_node_triple_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherProduct.bConv (t₁.bSeries) t₂
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
      = t₁.bSeries (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
        + ∑ k : Fin 4,
          tripleLeafChoiceCoef k (t₁.bSeries BTree.leaf) 1 *
            t₂.bSeries
              (BTree.node
                (List.replicate (tripleLeafChoiceCount k) BTree.leaf)) := by
  unfold ButcherProduct.bConv
  rw [ButcherProduct.bWeighted_convAt_node_triple_leaf_eq]

/-- Headline §384 product `bSeries` closed form on the standalone
triple-leaf tree. -/
theorem ButcherProduct.bSeries_node_triple_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
      = t₁.bSeries (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
        + ∑ k : Fin 4,
          tripleLeafChoiceCoef k (t₁.bSeries BTree.leaf) 1 *
            t₂.bSeries
              (BTree.node
                (List.replicate (tripleLeafChoiceCount k) BTree.leaf)) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_triple_leaf_eq]

/-! ### §384 all-triple-leaf parametric family (cycle 558)

The parametric family `BTree.node (List.replicate n (BTree.node [BTree.leaf,
BTree.leaf, BTree.leaf]))`. Each kept root child has a `Fin 4` per-child
choice indexing how many of its three internal leaves are cut. -/

/-- Number of kept root children that pick choice index `k : Fin 4` (so cut
`k` leaves and keep `3 - k`). -/
def tripleLeafChoiceFiber {n : ℕ} (χ : Fin n → Fin 4) (k : Fin 4) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun p => χ p = k).card

/-- The aggregate second-tableau tree produced by a per-kept-child choice
function. The four fibers contribute `node [leaf,leaf,leaf]`, `node
[leaf,leaf]`, `node [leaf]`, and `leaf` respectively. -/
def tripleLeafChoiceTree {n : ℕ} (χ : Fin n → Fin 4) : BTree :=
  BTree.node
    (List.replicate (tripleLeafChoiceFiber χ ⟨0, by decide⟩)
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) ++
      List.replicate (tripleLeafChoiceFiber χ ⟨1, by decide⟩)
        (BTree.node [BTree.leaf, BTree.leaf]) ++
      List.replicate (tripleLeafChoiceFiber χ ⟨2, by decide⟩)
        (BTree.node [BTree.leaf]) ++
      List.replicate (tripleLeafChoiceFiber χ ⟨3, by decide⟩) BTree.leaf)

/-- The product of per-kept-child scalar coefficients in the triple-leaf
parametric expansion. -/
noncomputable def tripleLeafChoiceProductCoef {n : ℕ} (X : ℝ)
    (χ : Fin n → Fin 4) : ℝ :=
  ∏ p : Fin n, tripleLeafChoiceCoef (χ p) X 1

/-- §384 honest convolution closed form on the all-triple-leaf parametric
family. Root cuts contribute `t₁.bSeries (node [leaf,leaf,leaf])` factors;
each kept root child carries a `Fin 4` cut-count choice over its three
internal leaves. -/
theorem ButcherProduct.bConv_node_replicate_triple_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    ButcherProduct.bConv (t₁.bSeries) t₂
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))
              ^ S.card *
              (∑ χ : Fin (n - S.card) → Fin 4,
                tripleLeafChoiceProductCoef (t₁.bSeries BTree.leaf) χ *
                  t₂.bSeries (tripleLeafChoiceTree χ)) := by
  sorry

/-- Headline §384 product `bSeries` closed form on the all-triple-leaf
parametric family. -/
theorem ButcherProduct.bSeries_node_replicate_triple_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))
              ^ S.card *
              (∑ χ : Fin (n - S.card) → Fin 4,
                tripleLeafChoiceProductCoef (t₁.bSeries BTree.leaf) χ *
                  t₂.bSeries (tripleLeafChoiceTree χ)) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_replicate_triple_leaf_eq]

end ButcherTableau
