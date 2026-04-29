import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section384
import OpenMath.ButcherGroup.Section384Slices
import OpenMath.ButcherGroup.Section384SlicesMixed
import OpenMath.ButcherGroup.Section384SlicesQuadMixed

/-!
# §384 QuotEquiv slice lifts

Cycle 566 split: this module collects the
`QuotEquiv.bSeriesHom_product_*` family extracted from the
3206-line `OpenMath/ButcherGroup.lean`. Each theorem is a thin
`Quotient.inductionOn₂` lift of a matching raw
`ButcherProduct.bSeries_*_eq` closed form from the
`Section384*Slices*` modules.
-/

open Finset

namespace ButcherTableau
namespace QuotEquiv

/-- The §384-facing elementary-weight map from a quotient class to its
tree-indexed Butcher-series coefficients. -/
noncomputable def bSeriesHom {s : ℕ} (q : QuotEquiv s) : BTree → ℝ :=
  fun τ => bSeries q τ

/-- §384 lift of the cycle 540 closed form on the second-order rooted
tree `BTree.node [BTree.leaf]` to the quotient layer. The product
`bSeriesHom` decomposes into a sum of three bSeries-only / weightsSum-only
summands. -/
theorem bSeriesHom_product_singleton_leaf
    {s t : ℕ} (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) :
    (q₁.product q₂).bSeriesHom (BTree.node [BTree.leaf])
      = q₁.bSeriesHom (BTree.node [BTree.leaf])
        + q₂.bSeriesHom (BTree.node [BTree.leaf])
        + q₂.weightsSum * q₁.bSeriesHom BTree.leaf := by
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product, weightsSum,
         ButcherTableau.bSeries, ButcherTableau.weightsSum] using
    ButcherProduct.bSeries_singleton_leaf_eq t₁ t₂

/-- §384 lift of the product closed form on `BTree.node []`. -/
theorem bSeriesHom_product_node_nil
    {s t : ℕ} (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) :
    (q₁.product q₂).bSeriesHom (BTree.node [])
      = q₁.weightsSum + q₂.weightsSum := by
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product, weightsSum,
         ButcherTableau.bSeries, ButcherTableau.weightsSum] using
    ButcherProduct.bSeries_node_nil_eq t₁ t₂

/-- §384 lift of the product closed form on `BTree.node [BTree.node []]`. -/
theorem bSeriesHom_product_node_node_nil
    {s t : ℕ} (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) :
    (q₁.product q₂).bSeriesHom (BTree.node [BTree.node []])
      = q₁.bSeriesHom (BTree.node [BTree.leaf])
        + q₂.bSeriesHom (BTree.node [BTree.leaf])
        + q₂.weightsSum * q₁.bSeriesHom (BTree.node []) := by
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product, weightsSum,
         ButcherTableau.bSeries, ButcherTableau.weightsSum] using
    ButcherProduct.bSeries_node_node_nil_eq t₁ t₂

/-- §384 lift of the cycle 542 all-leaves closed form to the quotient
layer. The product `bSeriesHom` on `BTree.node (List.replicate n BTree.leaf)`
decomposes into a powerset sum of bSeries-only summands. This is the first
parametric (in `n`) `G1.mul`-direction product closed form at the quotient
layer. -/
theorem bSeriesHom_product_node_replicate_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (n : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node (List.replicate n BTree.leaf))
      = q.bSeriesHom (BTree.node (List.replicate n BTree.leaf))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (q.bSeriesHom BTree.leaf) ^ S.card *
            r.bSeriesHom
              (BTree.node (List.replicate (n - S.card) BTree.leaf)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_replicate_leaf_eq t₁ t₂ n

/-- §384 lift of the standalone triple-leaf closed form to the quotient
layer, grouped by the four possible cut counts. -/
theorem bSeriesHom_product_node_triple_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) :
    (q.product r).bSeriesHom
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
      = q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
        + ∑ k : Fin 4,
          tripleLeafChoiceCoef k (q.bSeriesHom BTree.leaf) 1 *
            r.bSeriesHom
              (BTree.node
                (List.replicate (tripleLeafChoiceCount k) BTree.leaf)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_triple_leaf_eq t₁ t₂

/-- §384 lift of the standalone four-child mixed leaf/singleton-leaf closed
form to the quotient layer, grouped as `Fin 4 × Fin 3`. -/
theorem bSeriesHom_product_node_quadMixed
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) :
    (q.product r).bSeriesHom tQuadMixed
      = q.bSeriesHom tQuadMixed
        + ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k (q.bSeriesHom BTree.leaf) 1 *
            quadMixedSingletonChoiceCoef h (q.bSeriesHom BTree.leaf)
              (q.bSeriesHom (BTree.node [BTree.leaf])) *
            r.bSeriesHom (quadMixedChoiceTree k h) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_quadMixed_eq t₁ t₂

/-- §384 lift of the standalone (2-leaf, 2-singleton) four-children mixed
closed form to the quotient layer, grouped as `Fin 3 × Fin 3 × Fin 3`. -/
theorem bSeriesHom_product_node_quadMixedTwoTwo
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) :
    (q.product r).bSeriesHom tQuadMixedTwoTwo
      = q.bSeriesHom tQuadMixedTwoTwo
        + ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k (q.bSeriesHom BTree.leaf) 1 *
            (quadMixedTwoTwoSingletonChoiceCoef h₁ (q.bSeriesHom BTree.leaf)
                (q.bSeriesHom (BTree.node [BTree.leaf])) *
              quadMixedTwoTwoSingletonChoiceCoef h₂ (q.bSeriesHom BTree.leaf)
                (q.bSeriesHom (BTree.node [BTree.leaf]))) *
            r.bSeriesHom (quadMixedTwoTwoChoiceTree k h₁ h₂) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_quadMixedTwoTwo_eq t₁ t₂

/-- §384 lift of the standalone (1-leaf, 3-singleton) four-children mixed
closed form to the quotient layer, grouped as
`Fin 2 × Fin 3 × Fin 3 × Fin 3`. -/
theorem bSeriesHom_product_node_quadMixedOneThree
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) :
    (q.product r).bSeriesHom tQuadMixedOneThree
      = q.bSeriesHom tQuadMixedOneThree
        + ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k (q.bSeriesHom BTree.leaf) 1 *
            (quadMixedSingletonChoiceCoef h₁ (q.bSeriesHom BTree.leaf)
                (q.bSeriesHom (BTree.node [BTree.leaf])) *
              (quadMixedSingletonChoiceCoef h₂ (q.bSeriesHom BTree.leaf)
                  (q.bSeriesHom (BTree.node [BTree.leaf])) *
                quadMixedSingletonChoiceCoef h₃ (q.bSeriesHom BTree.leaf)
                  (q.bSeriesHom (BTree.node [BTree.leaf])))) *
            r.bSeriesHom (quadMixedOneThreeChoiceTree k h₁ h₂ h₃) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_quadMixedOneThree_eq t₁ t₂

/-- §384 lift of the cycle 544 dual all-empty-node closed form to the
quotient layer. The product `bSeriesHom` on `BTree.node (List.replicate
n (BTree.node []))` decomposes into a powerset sum of bSeries-only
summands. Mirror of `bSeriesHom_product_node_replicate_leaf`. -/
theorem bSeriesHom_product_node_replicate_node_nil
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (n : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node (List.replicate n (BTree.node [])))
      = q.bSeriesHom (BTree.node (List.replicate n (BTree.node [])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (q.bSeriesHom (BTree.node [])) ^ S.card *
            r.bSeriesHom
              (BTree.node
                (List.replicate (n - S.card) (BTree.node []))) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_replicate_node_nil_eq t₁ t₂ n

/-- §384 lift of the all-singleton-leaf-children closed form to the
quotient layer. The product `bSeriesHom` on
`BTree.node (List.replicate n (BTree.node [BTree.leaf]))` decomposes into a
root-cut powerset and an internal-cut powerset of bSeries-only summands. -/
theorem bSeriesHom_product_node_replicate_singleton_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (n : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
      = q.bSeriesHom
          (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (q.bSeriesHom (BTree.node [BTree.leaf])) ^ S.card *
            (∑ T ∈ Sᶜ.powerset,
              (q.bSeriesHom BTree.leaf) ^ T.card *
              r.bSeriesHom
                (BTree.node
                  (List.replicate T.card BTree.leaf ++
                    List.replicate ((Sᶜ).card - T.card)
                      (BTree.node [BTree.leaf])))) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_replicate_singleton_leaf_eq t₁ t₂ n

/-- §384 lift of the mixed leaf / singleton-leaf root closed form to the
quotient layer. The product `bSeriesHom` on
`BTree.node (List.replicate a BTree.leaf ++ List.replicate b
(BTree.node [BTree.leaf]))` decomposes into root-cut and internal-cut
powersets. -/
theorem bSeriesHom_product_node_mixed_leaf_singleton_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (a b : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf])))
      = q.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf])))
        + ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
              (q.bSeriesHom BTree.leaf) ^ S_leaf.card *
                (q.bSeriesHom (BTree.node [BTree.leaf])) ^ S_sl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  (q.bSeriesHom BTree.leaf) ^ T.card *
                  r.bSeriesHom
                    (BTree.node
                      (List.replicate (a - S_leaf.card + T.card) BTree.leaf ++
                        List.replicate ((S_slᶜ : Finset (Fin b)).card - T.card)
                          (BTree.node [BTree.leaf])))) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_mixed_leaf_singleton_leaf_eq t₁ t₂ a b

/-- §384 lift of the mixed leaf / double-leaf root closed form to the
quotient layer. The kept double-leaf branch is indexed by a `Fin 3` choice:
both internal leaves cut, one internal leaf cut, or both kept. -/
theorem bSeriesHom_product_node_mixed_leaf_double_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (a b : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
      = q.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
              (q.bSeriesHom BTree.leaf) ^ S_leaf.card *
                (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
                (∑ χ : Fin (b - S_dl.card) → Fin 3,
                  doubleLeafChoiceCoef (q.bSeriesHom BTree.leaf) χ *
                    r.bSeriesHom
                      (doubleLeafChoiceTree (a - S_leaf.card) χ)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_mixed_leaf_double_leaf_cut_eq t₁ t₂ a b

/-- §384 lift of the cycle 562 all-double-leaf parametric family
`BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf]))` to
the quotient layer. Each kept root child contributes a `Fin 3` cut/keep
choice via `doubleLeafChoiceCoef`. -/
theorem bSeriesHom_product_node_replicate_double_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (n : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf])))
      = q.bSeriesHom
          (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 3,
              doubleLeafChoiceCoef (q.bSeriesHom BTree.leaf) χ *
                r.bSeriesHom (doubleLeafChoiceTree 0 χ)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_replicate_double_leaf_eq t₁ t₂ n

/-- §384 lift of the all-triple-leaf parametric family
`BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf,
BTree.leaf]))` to the quotient layer. Each kept root child contributes a
`Fin 4` cut-count choice. -/
theorem bSeriesHom_product_node_replicate_triple_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (n : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = q.bSeriesHom
          (BTree.node
            (List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (q.bSeriesHom
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef (q.bSeriesHom BTree.leaf) χ *
                r.bSeriesHom (tripleLeafChoiceTree χ)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_replicate_triple_leaf_eq t₁ t₂ n

/-- §384 lift of the mixed leaf / triple-leaf parametric family to the
quotient layer. Each kept triple-leaf root child contributes a `Fin 4`
cut-count choice; kept root leaves contribute to the residual leaf count. -/
theorem bSeriesHom_product_node_replicate_mixed_leaf_triple_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (a b : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = q.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
        + ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_tl ∈ (Finset.univ : Finset (Fin b)).powerset,
              (q.bSeriesHom BTree.leaf) ^ S_leaf.card *
                (q.bSeriesHom
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S_tl.card *
                  (∑ χ : Fin (b - S_tl.card) → Fin 4,
                    tripleLeafChoiceFunctionCoef (q.bSeriesHom BTree.leaf) χ *
                      r.bSeriesHom
                        (mixedLeafTripleLeafChoiceTree
                          (a - S_leaf.card) χ)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_replicate_mixed_leaf_triple_leaf_eq
      t₁ t₂ a b

/-- §384 lift of the cycle 554 mixed singleton-leaf / double-leaf root
family.  Each kept singleton-leaf gives a `Fin 2` cut/keep choice for its
internal leaf; each kept double-leaf gives a `Fin 3` choice via
`doubleLeafChoiceCoef`. -/
theorem bSeriesHom_product_node_mixed_singleton_leaf_double_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (a b : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a (BTree.node [BTree.leaf]) ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
      = q.bSeriesHom
          (BTree.node
            (List.replicate a (BTree.node [BTree.leaf]) ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ S_sl ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
              (q.bSeriesHom (BTree.node [BTree.leaf])) ^ S_sl.card *
                (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
                  (q.bSeriesHom BTree.leaf) ^ T.card *
                    (∑ χ : Fin (b - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef (q.bSeriesHom BTree.leaf) χ *
                        r.bSeriesHom
                          (BTree.node
                            (List.replicate
                                (T.card +
                                  doubleLeafChoiceCount χ ⟨0, by decide⟩)
                                BTree.leaf ++
                              List.replicate
                                  (((S_slᶜ : Finset (Fin a)).card - T.card) +
                                    doubleLeafChoiceCount χ ⟨1, by decide⟩)
                                  (BTree.node [BTree.leaf]) ++
                                List.replicate
                                  (doubleLeafChoiceCount χ ⟨2, by decide⟩)
                                  (BTree.node [BTree.leaf, BTree.leaf]))))) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_mixed_singleton_leaf_double_leaf_cut_eq
      t₁ t₂ a b

/-- §384 lift of the three-way mixed closure on the root family
`replicate a leaf ++ replicate b (node [leaf]) ++ replicate c (node [leaf, leaf])`. -/
theorem bSeriesHom_product_node_mixed_leaf_singleton_leaf_double_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) (a b c : ℕ) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf])))
      = q.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf]) ++
                List.replicate c (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ S_l ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
              ∑ S_dl ∈ (Finset.univ : Finset (Fin c)).powerset,
                (q.bSeriesHom BTree.leaf) ^ S_l.card *
                  (q.bSeriesHom (BTree.node [BTree.leaf])) ^ S_sl.card *
                  (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
                  (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                    (q.bSeriesHom BTree.leaf) ^ T.card *
                      (∑ χ : Fin (c - S_dl.card) → Fin 3,
                        doubleLeafChoiceCoef (q.bSeriesHom BTree.leaf) χ *
                          r.bSeriesHom
                            (BTree.node
                              (List.replicate
                                  ((a - S_l.card) + T.card +
                                    doubleLeafChoiceCount χ ⟨0, by decide⟩)
                                  BTree.leaf ++
                                List.replicate
                                    (((S_slᶜ : Finset (Fin b)).card - T.card) +
                                      doubleLeafChoiceCount χ ⟨1, by decide⟩)
                                    (BTree.node [BTree.leaf]) ++
                                  List.replicate
                                    (doubleLeafChoiceCount χ ⟨2, by decide⟩)
                                    (BTree.node [BTree.leaf, BTree.leaf]))))) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_mixed_leaf_singleton_leaf_double_leaf_cut_eq
      t₁ t₂ a b c

/-- §384 lift of the finite mixed closure on
`BTree.node [BTree.leaf, BTree.node []]`. -/
theorem bSeriesHom_product_node_leaf_node_nil
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) :
    (q.product r).bSeriesHom
        (BTree.node [BTree.leaf, BTree.node []])
      = q.bSeriesHom (BTree.node [BTree.leaf, BTree.node []])
        + ∑ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
            (q.bSeriesHom BTree.leaf) ^ S.card *
            r.bSeriesHom
              (BTree.node (List.replicate (2 - S.card) BTree.leaf)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_leaf_node_nil_eq t₁ t₂

/-- §384 lift of the finite mixed closure on
`BTree.node [BTree.node [], BTree.leaf]`. -/
theorem bSeriesHom_product_node_node_nil_leaf
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) :
    (q.product r).bSeriesHom
        (BTree.node [BTree.node [], BTree.leaf])
      = q.bSeriesHom (BTree.node [BTree.node [], BTree.leaf])
        + ∑ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
            (q.bSeriesHom BTree.leaf) ^ S.card *
            r.bSeriesHom
              (BTree.node (List.replicate (2 - S.card) BTree.leaf)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_node_nil_leaf_eq t₁ t₂

/-- §384 lift of the finite mixed closure on
`BTree.node [BTree.leaf, BTree.leaf, BTree.node []]`. -/
theorem bSeriesHom_product_node_leaf_leaf_node_nil
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t) :
    (q.product r).bSeriesHom
        (BTree.node [BTree.leaf, BTree.leaf, BTree.node []])
      = q.bSeriesHom
          (BTree.node [BTree.leaf, BTree.leaf, BTree.node []])
        + ∑ S ∈ (Finset.univ : Finset (Fin 3)).powerset,
            (q.bSeriesHom BTree.leaf) ^ S.card *
            r.bSeriesHom
              (BTree.node (List.replicate (3 - S.card) BTree.leaf)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_leaf_leaf_node_nil_eq t₁ t₂

/-- §384 lift of the cycle 546 parametric trivial-children closed form
to the quotient layer. The product `bSeriesHom` on
`BTree.node children` (each child is `BTree.leaf` or `BTree.node []`)
decomposes into a powerset sum of bSeries-only summands. Subsumes the
cycle 540 / 542 / 544 / 545 single-shape and finite mixed-shape lifts
in one parametric statement. -/
theorem bSeriesHom_product_node_trivial_children
    {s t : ℕ} (q : QuotEquiv s) (r : QuotEquiv t)
    (children : List BTree)
    (hTriv : ∀ p : Fin children.length,
        children.get p = BTree.leaf ∨ children.get p = BTree.node []) :
    (q.product r).bSeriesHom (BTree.node children)
      = q.bSeriesHom (BTree.node children)
        + ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
            (q.bSeriesHom BTree.leaf) ^ S.card *
            r.bSeriesHom
              (BTree.node
                (List.replicate (children.length - S.card) BTree.leaf)) := by
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product,
         ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_trivial_children_eq t₁ t₂ children hTriv

end QuotEquiv
end ButcherTableau
