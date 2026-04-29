import OpenMath.ButcherGroup.Section384SlicesMixed.Common

/-! # §384 mixed-slice leaf families (cycle 564 split)

`IsG1Equiv` slices for root families whose children are mixtures of
`BTree.leaf` with one other shape:

* mixed leaf + singleton-leaf (cycles 543–549)
* mixed leaf + double-leaf (cycles 552–553)

The mixed singleton-leaf + double-leaf and three-way leaf + singleton-leaf
+ double-leaf families live in
`OpenMath/ButcherGroup/Section384SlicesMixed/Mixed3Way.lean`. The pure
parametric all-double-leaf and all-triple-leaf families plus the
standalone triple-leaf single tree live in
`OpenMath/ButcherGroup/Section384SlicesMixed/Replicate.lean`.
-/

open Finset

namespace ButcherTableau

variable {s : ℕ}

/-! ### §384 mixed leaf / singleton-leaf root-children parametric helper

Cycle 549 re-lands the cycle 548 per-stage closed form for root children
made of `BTree.leaf` and `BTree.node [BTree.leaf]`. -/

/-- Per-stage `convAt` value at the mixed root family
`replicate a leaf ++ replicate b (node [leaf])` is a product of two
powers: a leaf factor `(coef leaf + row i)^a` and a singleton-leaf
factor `(coef (node [leaf]) + coef leaf * row i + chain i)^b`. -/
-- Promoted from `private` (cycle 564 split): used by the standalone
-- triple-leaf and parametric all-triple-leaf slices in
-- `Section384SlicesMixed/Replicate.lean`.
theorem convAt_node_mixed_leaf_singleton_leaf_at_i_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (a b : ℕ)
    (i : Fin t) :
    ButcherProduct.convAt t₂ coef
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]))) i
      = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a *
        (coef (BTree.node [BTree.leaf]) +
          (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
            ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) ^ b := by
  classical
  rw [ButcherProduct.convAt_node]
  have hprod_add :
      (∑ S : Finset
          (Fin (List.replicate a BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf])).length),
          (∏ p ∈ S,
            coef ((List.replicate a BTree.leaf ++
                    List.replicate b (BTree.node [BTree.leaf])).get p)) *
            (∏ p ∈ Sᶜ,
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  ((List.replicate a BTree.leaf ++
                      List.replicate b (BTree.node [BTree.leaf])).get p) j))
        = ∏ p : Fin (List.replicate a BTree.leaf ++
                        List.replicate b (BTree.node [BTree.leaf])).length,
            (coef ((List.replicate a BTree.leaf ++
                      List.replicate b (BTree.node [BTree.leaf])).get p) +
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  ((List.replicate a BTree.leaf ++
                      List.replicate b (BTree.node [BTree.leaf])).get p) j) := by
    rw [Finset.prod_add (s := Finset.univ)
        (f := fun p =>
          coef ((List.replicate a BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf])).get p))
        (g := fun p =>
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef
              ((List.replicate a BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf])).get p) j)]
    rw [Finset.powerset_univ]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [(Finset.compl_eq_univ_sdiff S).symm]
  rw [hprod_add]
  have hlen : (List.replicate a BTree.leaf ++
                List.replicate b (BTree.node [BTree.leaf])).length = a + b := by
    simp [List.length_append, List.length_replicate]
  let e :
      Fin (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf])).length ≃
        Fin (a + b) :=
    { toFun := Fin.cast hlen
      invFun := Fin.cast hlen.symm
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }
  let F : Fin (a + b) → ℝ := fun p =>
    coef ((List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf])).get
            (Fin.cast hlen.symm p)) +
      ∑ j : Fin t, t₂.A i j *
        ButcherProduct.convAt t₂ coef
          ((List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf])).get
            (Fin.cast hlen.symm p)) j
  have hreindex :
      (∏ p : Fin (List.replicate a BTree.leaf ++
                    List.replicate b (BTree.node [BTree.leaf])).length,
          (coef ((List.replicate a BTree.leaf ++
                    List.replicate b (BTree.node [BTree.leaf])).get p) +
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef
                ((List.replicate a BTree.leaf ++
                    List.replicate b (BTree.node [BTree.leaf])).get p) j))
        = ∏ p : Fin (a + b), F p := by
    apply Fintype.prod_equiv e
    intro p
    simp [e, F]
  rw [hreindex]
  rw [Fin.prod_univ_add]
  have hleaf_factor : (∏ j : Fin a, F (Fin.castAdd b j))
      = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a := by
    have h : ∀ j : Fin a, F (Fin.castAdd b j)
            = coef BTree.leaf + ∑ j : Fin t, t₂.A i j := by
      intro j
      have hpos : ((Fin.cast hlen.symm (Fin.castAdd b j)) : ℕ) < a := by
        change ((Fin.castAdd b j) : ℕ) < a
        have : ((Fin.castAdd b j) : ℕ) = (j : ℕ) := rfl
        rw [this]
        exact j.isLt
      have hpos' :
          ((Fin.cast hlen.symm (Fin.castAdd b j)) : ℕ) <
            (List.replicate a BTree.leaf).length := by
        simp [List.length_replicate]
      have hget :
          (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf])).get
            (Fin.cast hlen.symm (Fin.castAdd b j)) = BTree.leaf := by
        simp [List.get_eq_getElem, List.getElem_append_left]
      show F (Fin.castAdd b j) = _
      simp [F, ButcherProduct.convAt_leaf]
    calc (∏ j : Fin a, F (Fin.castAdd b j))
        = ∏ _ : Fin a, (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) :=
            Finset.prod_congr rfl (fun j _ => h j)
      _ = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsl_factor : (∏ j : Fin b, F (Fin.natAdd a j))
      = (coef (BTree.node [BTree.leaf]) +
          (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
            ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) ^ b := by
    have h : ∀ j : Fin b, F (Fin.natAdd a j)
            = coef (BTree.node [BTree.leaf]) +
                (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                  ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) := by
      intro j
      have hge : a ≤ ((Fin.cast hlen.symm (Fin.natAdd a j)) : ℕ) := by
        change a ≤ ((Fin.natAdd a j) : ℕ)
        have : ((Fin.natAdd a j) : ℕ) = a + (j : ℕ) := rfl
        rw [this]
        exact Nat.le_add_right _ _
      have hge' :
          (List.replicate a BTree.leaf).length ≤
            ((Fin.cast hlen.symm (Fin.natAdd a j)) : ℕ) := by
        simp [List.length_replicate]
      have hget :
          (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf])).get
            (Fin.cast hlen.symm (Fin.natAdd a j)) = BTree.node [BTree.leaf] := by
        simp [List.get_eq_getElem, List.getElem_append_right]
      show F (Fin.natAdd a j) = _
      simp only [F, hget]
      simp only [convAt_singleton_leaf_eq]
      congr 1
      calc (∑ k : Fin t, t₂.A i k * (coef BTree.leaf + ∑ ℓ : Fin t, t₂.A k ℓ))
          = ∑ k : Fin t, (t₂.A i k * coef BTree.leaf +
                          t₂.A i k * ∑ ℓ : Fin t, t₂.A k ℓ) := by
              refine Finset.sum_congr rfl (fun k _ => by ring)
        _ = (∑ k : Fin t, t₂.A i k * coef BTree.leaf) +
              ∑ k : Fin t, t₂.A i k * ∑ ℓ : Fin t, t₂.A k ℓ := by
              rw [Finset.sum_add_distrib]
        _ = coef BTree.leaf * (∑ k : Fin t, t₂.A i k) +
              ∑ k : Fin t, t₂.A i k * ∑ ℓ : Fin t, t₂.A k ℓ := by
              congr 1
              rw [← Finset.sum_mul]; ring
    calc (∏ j : Fin b, F (Fin.natAdd a j))
        = ∏ _ : Fin b, (coef (BTree.node [BTree.leaf]) +
              (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) :=
            Finset.prod_congr rfl (fun j _ => h j)
      _ = (coef (BTree.node [BTree.leaf]) +
              (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) ^ b := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hleaf_factor, hsl_factor]

/-- Per-stage polynomial expansion for the mixed leaf/singleton-leaf
closed form. The outer subsets cut root leaves and root singleton-leaf
children; the inner subset cuts the leaf inside a kept singleton-leaf
child. -/
private theorem mixed_stage_polynomial_expand
    (X Y R C : ℝ) (a b : ℕ) :
    (X + R) ^ a * (Y + (X * R + C)) ^ b
      = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            X ^ S_leaf.card * Y ^ S_sl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                X ^ T.card *
                  (R ^ (a - S_leaf.card + T.card) *
                    C ^ ((S_slᶜ : Finset (Fin b)).card - T.card))) := by
  classical
  rw [pow_add_eq_powerset X R a]
  rw [pow_add_eq_powerset Y (X * R + C) b]
  rw [Finset.sum_mul]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_leaf hS_leaf
  rw [Finset.mul_sum]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_sl hS_sl
  have hS_sl_card :
      b - S_sl.card
        = (S_slᶜ : Finset (Fin b)).card := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin]
  have hinner :
      (X * R + C) ^ (b - S_sl.card)
        = ∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
            (X * R) ^ T.card *
              C ^ ((S_slᶜ : Finset (Fin b)).card - T.card) := by
    calc
      (X * R + C) ^ (b - S_sl.card)
          = ∏ _p ∈ (S_slᶜ : Finset (Fin b)), (X * R + C) := by
              rw [hS_sl_card, Finset.prod_const]
      _ = ∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
            (X * R) ^ T.card *
              C ^ ((S_slᶜ : Finset (Fin b)).card - T.card) := by
              rw [prod_const_add_eq_powerset]
  rw [hinner]
  calc
    X ^ S_leaf.card * R ^ (a - S_leaf.card) *
        (Y ^ S_sl.card *
          (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
            (X * R) ^ T.card *
              C ^ ((S_slᶜ : Finset (Fin b)).card - T.card)))
        = (X ^ S_leaf.card * R ^ (a - S_leaf.card) * Y ^ S_sl.card) *
            (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
              (X * R) ^ T.card *
                C ^ ((S_slᶜ : Finset (Fin b)).card - T.card)) := by
          ring
    _ = ∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
          (X ^ S_leaf.card * R ^ (a - S_leaf.card) * Y ^ S_sl.card) *
            ((X * R) ^ T.card *
              C ^ ((S_slᶜ : Finset (Fin b)).card - T.card)) := by
          rw [Finset.mul_sum]
    _ = ∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
          (X ^ S_leaf.card * Y ^ S_sl.card) *
            (X ^ T.card *
              (R ^ (a - S_leaf.card + T.card) *
                C ^ ((S_slᶜ : Finset (Fin b)).card - T.card))) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro T hT
          rw [mul_pow]
          calc
            (X ^ S_leaf.card * R ^ (a - S_leaf.card) * Y ^ S_sl.card) *
                (X ^ T.card * R ^ T.card *
                  C ^ ((S_slᶜ : Finset (Fin b)).card - T.card))
                = (X ^ S_leaf.card * Y ^ S_sl.card) *
                    (X ^ T.card *
                      ((R ^ (a - S_leaf.card) * R ^ T.card) *
                        C ^ ((S_slᶜ : Finset (Fin b)).card - T.card))) := by
                  ring
            _ = (X ^ S_leaf.card * Y ^ S_sl.card) *
                    (X ^ T.card *
                      (R ^ (a - S_leaf.card + T.card) *
                        C ^ ((S_slᶜ : Finset (Fin b)).card - T.card))) := by
                  rw [← pow_add]
    _ = X ^ S_leaf.card * Y ^ S_sl.card *
          (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
            X ^ T.card *
              (R ^ (a - S_leaf.card + T.card) *
                C ^ ((S_slᶜ : Finset (Fin b)).card - T.card))) := by
          rw [Finset.mul_sum]

/-- Reorder the stage-weighted mixed polynomial expansion so the tableau
stage sum is inside the three cut-set sums. -/
private theorem weighted_mixed_stage_sum_expand
    {t : ℕ} (w row chain : Fin t → ℝ) (X Y : ℝ) (a b : ℕ) :
    (∑ i : Fin t, w i *
      (∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
        ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
          X ^ S_leaf.card * Y ^ S_sl.card *
            (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
              X ^ T.card *
                (row i ^ (a - S_leaf.card + T.card) *
                  chain i ^ ((S_slᶜ : Finset (Fin b)).card - T.card)))))
      = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            X ^ S_leaf.card * Y ^ S_sl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                X ^ T.card *
                  (∑ i : Fin t, w i *
                    (row i ^ (a - S_leaf.card + T.card) *
                      chain i ^ ((S_slᶜ : Finset (Fin b)).card - T.card)))) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_leaf hS_leaf
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_sl hS_sl
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro T hT
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro i hi
  ring

/-- b-weighted `convAt` closed form for the mixed root family. -/
private theorem bWeighted_convAt_node_mixed_leaf_singleton_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (a b : ℕ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf]))) i)
      = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            (coef BTree.leaf) ^ S_leaf.card *
              (coef (BTree.node [BTree.leaf])) ^ S_sl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                (coef BTree.leaf) ^ T.card *
                  t₂.bSeries
                    (BTree.node
                      (List.replicate (a - S_leaf.card + T.card) BTree.leaf ++
                        List.replicate ((S_slᶜ : Finset (Fin b)).card - T.card)
                          (BTree.node [BTree.leaf])))) := by
  classical
  let X : ℝ := coef BTree.leaf
  let Y : ℝ := coef (BTree.node [BTree.leaf])
  let row : Fin t → ℝ := fun i => ∑ j : Fin t, t₂.A i j
  let chain : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  have hbSeries : ∀ m n : ℕ,
      t₂.bSeries
          (BTree.node
            (List.replicate m BTree.leaf ++
              List.replicate n (BTree.node [BTree.leaf])))
        = ∑ i : Fin t, t₂.b i * (row i ^ m * chain i ^ n) := by
    intro m n
    rw [bSeries_node_replicate_leaf_append_replicate_singleton_leaf]
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf]))) i)
        = ∑ i : Fin t, t₂.b i *
            ((X + row i) ^ a * (Y + (X * row i + chain i)) ^ b) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i hi
          rw [convAt_node_mixed_leaf_singleton_leaf_at_i_eq]
    _ = ∑ i : Fin t, t₂.b i *
          (∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
              X ^ S_leaf.card * Y ^ S_sl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  X ^ T.card *
                    (row i ^ (a - S_leaf.card + T.card) *
                      chain i ^ ((S_slᶜ : Finset (Fin b)).card - T.card)))) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i hi
          rw [mixed_stage_polynomial_expand]
    _ = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            X ^ S_leaf.card * Y ^ S_sl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                X ^ T.card *
                  (∑ i : Fin t, t₂.b i *
                    (row i ^ (a - S_leaf.card + T.card) *
                      chain i ^ ((S_slᶜ : Finset (Fin b)).card - T.card)))) := by
          rw [weighted_mixed_stage_sum_expand]
    _ = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            (coef BTree.leaf) ^ S_leaf.card *
              (coef (BTree.node [BTree.leaf])) ^ S_sl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                (coef BTree.leaf) ^ T.card *
                  t₂.bSeries
                    (BTree.node
                      (List.replicate (a - S_leaf.card + T.card) BTree.leaf ++
                        List.replicate ((S_slᶜ : Finset (Fin b)).card - T.card)
                          (BTree.node [BTree.leaf])))) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S_leaf hS_leaf
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S_sl hS_sl
          simp only [X, Y]
          congr 1
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro T hT
          congr 1
          rw [← hbSeries (a - S_leaf.card + T.card)
            ((S_slᶜ : Finset (Fin b)).card - T.card)]

/-- §384 honest convolution closed form on the mixed root family
`BTree.node (List.replicate a BTree.leaf ++ List.replicate b (BTree.node [BTree.leaf]))`.

Root leaves and root singleton-leaf children are cut independently; each
kept singleton-leaf child has one further internal leaf cut/keep choice. -/
theorem ButcherProduct.bConv_node_mixed_leaf_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (a b : ℕ) :
    ButcherProduct.bConv (t₁.bSeries) t₂
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf])))
        + ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
              (t₁.bSeries BTree.leaf) ^ S_leaf.card *
                (t₁.bSeries (BTree.node [BTree.leaf])) ^ S_sl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  (t₁.bSeries BTree.leaf) ^ T.card *
                  t₂.bSeries
                    (BTree.node
                      (List.replicate (a - S_leaf.card + T.card) BTree.leaf ++
                        List.replicate ((S_slᶜ : Finset (Fin b)).card - T.card)
                          (BTree.node [BTree.leaf])))) := by
  unfold ButcherProduct.bConv
  rw [bWeighted_convAt_node_mixed_leaf_singleton_leaf_eq]

/-- Headline §384 corollary on the mixed leaf / singleton-leaf root family:
the product `bSeries` decomposes into root-cut and internal-cut powersets. -/
theorem ButcherProduct.bSeries_node_mixed_leaf_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (a b : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf])))
        + ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
              (t₁.bSeries BTree.leaf) ^ S_leaf.card *
                (t₁.bSeries (BTree.node [BTree.leaf])) ^ S_sl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  (t₁.bSeries BTree.leaf) ^ T.card *
                  t₂.bSeries
                    (BTree.node
                      (List.replicate (a - S_leaf.card + T.card) BTree.leaf ++
                        List.replicate ((S_slᶜ : Finset (Fin b)).card - T.card)
                          (BTree.node [BTree.leaf])))) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_mixed_leaf_singleton_leaf_eq]

/-! ### §384 mixed leaf / double-leaf root-children parametric helper

Cycle 552 extends the cycle 549 parametric ladder to root children that
are `BTree.leaf` or `BTree.node [BTree.leaf, BTree.leaf]` (the order-3
two-leaf inner node). The strategy fallback path is taken: this slice
delivers the per-stage `convAt` closed form, the corresponding `bConv`
closed form, and the `bSeries` corollary at the per-stage level (no
explicit cut-decomposition powerset). The squared keep-factor on the
double-leaf side would require a five-level powerset expansion to mirror
cycle 549's three-level form; the quotient lift and `IsG1Equiv` slice
therefore defer to cycle 553. -/

/-- The `convAt` value at the order-3 double-leaf child
`BTree.node [BTree.leaf, BTree.leaf]` is the square of the cycle-549
leaf factor. -/
-- Promoted from `private` (cycle 564 split): used by the mixed
-- singleton-leaf + double-leaf and three-way mixed slices in
-- `Section384SlicesMixed/Mixed3Way.lean`.
theorem convAt_double_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.convAt t₂ coef (BTree.node [BTree.leaf, BTree.leaf]) i
      = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ 2 := by
  classical
  rw [ButcherProduct.convAt_node]
  have hprod_add :
      (∑ S : Finset (Fin [BTree.leaf, BTree.leaf].length),
        (∏ p ∈ S, coef (([BTree.leaf, BTree.leaf] : List BTree).get p)) *
          (∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef
              (([BTree.leaf, BTree.leaf] : List BTree).get p) j))
        = ∏ p : Fin [BTree.leaf, BTree.leaf].length,
            (coef (([BTree.leaf, BTree.leaf] : List BTree).get p) +
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  (([BTree.leaf, BTree.leaf] : List BTree).get p) j) := by
    rw [Finset.prod_add (s := Finset.univ)
        (f := fun p => coef (([BTree.leaf, BTree.leaf] : List BTree).get p))
        (g := fun p => ∑ j : Fin t, t₂.A i j *
          ButcherProduct.convAt t₂ coef
            (([BTree.leaf, BTree.leaf] : List BTree).get p) j)]
    rw [Finset.powerset_univ]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [(Finset.compl_eq_univ_sdiff S).symm]
  rw [hprod_add]
  have hsame :
      ∀ p : Fin [BTree.leaf, BTree.leaf].length,
        (coef (([BTree.leaf, BTree.leaf] : List BTree).get p) +
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef
              (([BTree.leaf, BTree.leaf] : List BTree).get p) j)
          = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) := by
    intro p
    fin_cases p <;> simp
  rw [Finset.prod_congr rfl (fun p _ => hsame p)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/-- The kept double-leaf summand expands into three elementary weights:
the internal double-leaf can cut both leaves, cut one leaf, or keep both. -/
-- Promoted from `private` (cycle 564 split): used by the mixed
-- singleton-leaf + double-leaf and three-way mixed slices in
-- `Section384SlicesMixed/Mixed3Way.lean`.
lemma bWeighted_kept_double_leaf_summand_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ∑ j : Fin t, t₂.A i j * (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2
      = (coef BTree.leaf) ^ 2 *
          t₂.elementaryWeight (BTree.node [BTree.leaf]) i
        + 2 * coef BTree.leaf *
          t₂.elementaryWeight (BTree.node [BTree.node [BTree.leaf]]) i
        + t₂.elementaryWeight
          (BTree.node [BTree.node [BTree.leaf, BTree.leaf]]) i := by
  let x : ℝ := coef BTree.leaf
  let row : Fin t → ℝ := fun j => ∑ k : Fin t, t₂.A j k
  have hleaf :
      t₂.elementaryWeight (BTree.node [BTree.leaf]) i
        = ∑ j : Fin t, t₂.A i j := by
    rw [ButcherTableau.elementaryWeight_singleton]
    simp
  have hchain :
      t₂.elementaryWeight (BTree.node [BTree.node [BTree.leaf]]) i
        = ∑ j : Fin t, t₂.A i j * row j := by
    rw [ButcherTableau.elementaryWeight_singleton]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherTableau.elementaryWeight_singleton]
    simp [row]
  have hdouble :
      t₂.elementaryWeight
          (BTree.node [BTree.node [BTree.leaf, BTree.leaf]]) i
        = ∑ j : Fin t, t₂.A i j * (row j) ^ 2 := by
    rw [ButcherTableau.elementaryWeight_singleton]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact congrArg (fun z => t₂.A i j * z)
      (elementaryWeight_node_replicate_leaf t₂ 2 j)
  rw [hleaf, hchain, hdouble]
  calc
    (∑ j : Fin t,
        t₂.A i j * (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2)
        = ∑ j : Fin t,
            ((coef BTree.leaf) ^ 2 * t₂.A i j
              + (2 * coef BTree.leaf) * (t₂.A i j * row j)
              + t₂.A i j * (row j) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simp [row]
          ring
    _ = (coef BTree.leaf) ^ 2 * (∑ j : Fin t, t₂.A i j)
        + 2 * coef BTree.leaf *
          (∑ j : Fin t, t₂.A i j * row j)
        + ∑ j : Fin t, t₂.A i j * (row j) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]

/-- Count how many kept double-leaf children choose one of the three
summands in the cycle-553 expansion. Index `0` cuts both internal leaves,
index `1` cuts one internal leaf, and index `2` keeps both. -/
def doubleLeafChoiceCount {n : ℕ} (χ : Fin n → Fin 3) (r : Fin 3) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun p => χ p = r).card

/-- The second-tableau tree produced by a choice function over the kept
double-leaf root children. -/
def doubleLeafChoiceTree {n : ℕ} (aKeep : ℕ) (χ : Fin n → Fin 3) :
    BTree :=
  BTree.node
    (List.replicate
        (aKeep + doubleLeafChoiceCount χ ⟨0, by decide⟩) BTree.leaf ++
      List.replicate
        (doubleLeafChoiceCount χ ⟨1, by decide⟩) (BTree.node [BTree.leaf]) ++
      List.replicate
        (doubleLeafChoiceCount χ ⟨2, by decide⟩)
          (BTree.node [BTree.leaf, BTree.leaf]))

/-- Scalar coefficient contributed by a choice function in the kept
double-leaf expansion. -/
def doubleLeafChoiceCoef {n : ℕ} (x : ℝ) (χ : Fin n → Fin 3) : ℝ :=
  ∏ p : Fin n,
    match χ p with
    | ⟨0, _⟩ => x ^ 2
    | ⟨1, _⟩ => 2 * x
    | ⟨2, _⟩ => 1

private theorem doubleLeafChoice_value_product_eq
    {n : ℕ} (row chain dbl : ℝ) (χ : Fin n → Fin 3) :
    (∏ p : Fin n,
      match χ p with
      | ⟨0, _⟩ => row
      | ⟨1, _⟩ => chain
      | ⟨2, _⟩ => dbl)
      = row ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
          chain ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
          dbl ^ doubleLeafChoiceCount χ ⟨2, by decide⟩ := by
  classical
  let f : Fin 3 → ℝ := fun r =>
    match r with
    | ⟨0, _⟩ => row
    | ⟨1, _⟩ => chain
    | ⟨2, _⟩ => dbl
  have hfiber :
      (∏ r : Fin 3,
          ∏ p ∈ (Finset.univ : Finset (Fin n)).filter (fun p => χ p = r),
            f r)
        = ∏ p : Fin n, f (χ p) := by
    simpa [f] using
      (Finset.prod_fiberwise_eq_prod_filter'
        (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (Fin 3))) (g := χ) (f := f))
  calc
    (∏ p : Fin n,
      match χ p with
      | ⟨0, _⟩ => row
      | ⟨1, _⟩ => chain
      | ⟨2, _⟩ => dbl)
        = ∏ p : Fin n, f (χ p) := by
          refine Finset.prod_congr rfl ?_
          intro p _
          simp [f]
    _ = ∏ r : Fin 3,
          ∏ p ∈ (Finset.univ : Finset (Fin n)).filter (fun p => χ p = r),
            f r := hfiber.symm
    _ = row ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
          chain ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
          dbl ^ doubleLeafChoiceCount χ ⟨2, by decide⟩ := by
          simp [Fin.prod_univ_three, doubleLeafChoiceCount, f]

private theorem doubleLeafChoice_product_eq
    {n : ℕ} (x row chain dbl : ℝ) (χ : Fin n → Fin 3) :
    (∏ p : Fin n,
      match χ p with
      | ⟨0, _⟩ => x ^ 2 * row
      | ⟨1, _⟩ => 2 * x * chain
      | ⟨2, _⟩ => dbl)
      = doubleLeafChoiceCoef x χ *
          (row ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
            chain ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
            dbl ^ doubleLeafChoiceCount χ ⟨2, by decide⟩) := by
  classical
  let coeff : Fin n → ℝ := fun p =>
    match χ p with
    | ⟨0, _⟩ => x ^ 2
    | ⟨1, _⟩ => 2 * x
    | ⟨2, _⟩ => 1
  let value : Fin n → ℝ := fun p =>
    match χ p with
    | ⟨0, _⟩ => row
    | ⟨1, _⟩ => chain
    | ⟨2, _⟩ => dbl
  calc
    (∏ p : Fin n,
      match χ p with
      | ⟨0, _⟩ => x ^ 2 * row
      | ⟨1, _⟩ => 2 * x * chain
      | ⟨2, _⟩ => dbl)
        = ∏ p : Fin n, coeff p * value p := by
          refine Finset.prod_congr rfl ?_
          intro p _
          rcases hχ : χ p with ⟨v, hv⟩
          interval_cases v <;> simp [hχ, coeff, value]
    _ = (∏ p : Fin n, coeff p) * (∏ p : Fin n, value p) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ p : Fin n, coeff p) *
          (row ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
            chain ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
            dbl ^ doubleLeafChoiceCount χ ⟨2, by decide⟩) := by
          congr 1
          rw [doubleLeafChoice_value_product_eq]
    _ = doubleLeafChoiceCoef x χ *
          (row ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
            chain ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
          dbl ^ doubleLeafChoiceCount χ ⟨2, by decide⟩) := by
          congr 1

-- Promoted from `private` (cycle 564 split): used by the mixed
-- singleton-leaf + double-leaf and three-way mixed slices in
-- `Section384SlicesMixed/Mixed3Way.lean`.
theorem double_leaf_kept_pow_expand
    (X R C D : ℝ) (m : ℕ) :
    (X ^ 2 * R + 2 * X * C + D) ^ m
      = ∑ χ : Fin m → Fin 3,
          doubleLeafChoiceCoef X χ *
            (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
              C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
              D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩) := by
  classical
  let f : Fin 3 → ℝ := fun r =>
    match r with
    | ⟨0, _⟩ => X ^ 2 * R
    | ⟨1, _⟩ => 2 * X * C
    | ⟨2, _⟩ => D
  have hsum : X ^ 2 * R + 2 * X * C + D = ∑ r : Fin 3, f r := by
    simp [Fin.sum_univ_three, f]
  rw [hsum, Fintype.sum_pow]
  refine Finset.sum_congr rfl ?_
  intro χ _
  rw [doubleLeafChoice_product_eq]

private theorem mixed_double_leaf_stage_polynomial_expand
    (X Y R C D : ℝ) (a b : ℕ) :
    (X + R) ^ a * (Y + (X ^ 2 * R + 2 * X * C + D)) ^ b
      = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            X ^ S_leaf.card * Y ^ S_dl.card *
              (∑ χ : Fin (b - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef X χ *
                  (R ^
                    (a - S_leaf.card +
                      doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                    C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                    D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) := by
  classical
  rw [pow_add_eq_powerset X R a]
  rw [pow_add_eq_powerset Y (X ^ 2 * R + 2 * X * C + D) b]
  rw [Finset.sum_mul]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_leaf hS_leaf
  rw [Finset.mul_sum]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_dl hS_dl
  have hinner :
      (X ^ 2 * R + 2 * X * C + D) ^ (b - S_dl.card)
        = ∑ χ : Fin (b - S_dl.card) → Fin 3,
            doubleLeafChoiceCoef X χ *
              (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩) := by
    rw [double_leaf_kept_pow_expand]
  rw [hinner]
  calc
    X ^ S_leaf.card * R ^ (a - S_leaf.card) *
        (Y ^ S_dl.card *
          (∑ χ : Fin (b - S_dl.card) → Fin 3,
            doubleLeafChoiceCoef X χ *
              (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))
        = (X ^ S_leaf.card * R ^ (a - S_leaf.card) * Y ^ S_dl.card) *
            (∑ χ : Fin (b - S_dl.card) → Fin 3,
              doubleLeafChoiceCoef X χ *
                (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                  C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                  D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) := by
          ring
    _ = ∑ χ : Fin (b - S_dl.card) → Fin 3,
          (X ^ S_leaf.card * R ^ (a - S_leaf.card) * Y ^ S_dl.card) *
            (doubleLeafChoiceCoef X χ *
              (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) := by
          rw [Finset.mul_sum]
    _ = ∑ χ : Fin (b - S_dl.card) → Fin 3,
          X ^ S_leaf.card * Y ^ S_dl.card *
            (doubleLeafChoiceCoef X χ *
              (R ^
                (a - S_leaf.card +
                  doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro χ _
          calc
            (X ^ S_leaf.card * R ^ (a - S_leaf.card) * Y ^ S_dl.card) *
                (doubleLeafChoiceCoef X χ *
                  (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                    C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                    D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))
                = X ^ S_leaf.card * Y ^ S_dl.card *
                    (doubleLeafChoiceCoef X χ *
                      ((R ^ (a - S_leaf.card) *
                          R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                        C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                        D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) := by
                  ring
            _ = X ^ S_leaf.card * Y ^ S_dl.card *
                    (doubleLeafChoiceCoef X χ *
                      (R ^
                        (a - S_leaf.card +
                          doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                        C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                        D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) := by
                  rw [← pow_add]
    _ = X ^ S_leaf.card * Y ^ S_dl.card *
          (∑ χ : Fin (b - S_dl.card) → Fin 3,
            doubleLeafChoiceCoef X χ *
              (R ^
                (a - S_leaf.card +
                  doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) := by
          rw [Finset.mul_sum]

private theorem weighted_mixed_double_leaf_stage_sum_expand
    {t : ℕ} (w row chain dbl : Fin t → ℝ) (X Y : ℝ) (a b : ℕ) :
    (∑ i : Fin t, w i *
      (∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
        ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
          X ^ S_leaf.card * Y ^ S_dl.card *
            (∑ χ : Fin (b - S_dl.card) → Fin 3,
              doubleLeafChoiceCoef X χ *
                (row i ^
                  (a - S_leaf.card +
                    doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                  chain i ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                  dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))))
      = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            X ^ S_leaf.card * Y ^ S_dl.card *
              (∑ χ : Fin (b - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef X χ *
                  (∑ i : Fin t, w i *
                    (row i ^
                      (a - S_leaf.card +
                        doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                      chain i ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                      dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_leaf hS_leaf
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_dl hS_dl
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro χ hχ
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro i hi
  ring

/-- Per-stage `convAt` value at the mixed root family
`replicate a leaf ++ replicate b (node [leaf, leaf])` is a product of two
factors: a leaf factor `(coef leaf + row i)^a` and a double-leaf factor
`(coef (node [leaf, leaf]) + ∑ j, A i j * (coef leaf + row j)^2)^b`. -/
private theorem convAt_node_mixed_leaf_double_leaf_at_i_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (a b : ℕ)
    (i : Fin t) :
    ButcherProduct.convAt t₂ coef
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) i
      = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a *
        (coef (BTree.node [BTree.leaf, BTree.leaf]) +
          ∑ j : Fin t, t₂.A i j *
            (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) ^ b := by
  classical
  rw [ButcherProduct.convAt_node]
  have hprod_add :
      (∑ S : Finset
          (Fin (List.replicate a BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).length),
          (∏ p ∈ S,
            coef ((List.replicate a BTree.leaf ++
                    List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get p)) *
            (∏ p ∈ Sᶜ,
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  ((List.replicate a BTree.leaf ++
                      List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get p) j))
        = ∏ p : Fin (List.replicate a BTree.leaf ++
                        List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).length,
            (coef ((List.replicate a BTree.leaf ++
                      List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get p) +
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  ((List.replicate a BTree.leaf ++
                      List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get p) j) := by
    rw [Finset.prod_add (s := Finset.univ)
        (f := fun p =>
          coef ((List.replicate a BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get p))
        (g := fun p =>
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef
              ((List.replicate a BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get p) j)]
    rw [Finset.powerset_univ]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [(Finset.compl_eq_univ_sdiff S).symm]
  rw [hprod_add]
  have hlen : (List.replicate a BTree.leaf ++
                List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).length = a + b := by
    simp [List.length_append, List.length_replicate]
  let e :
      Fin (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).length ≃
        Fin (a + b) :=
    { toFun := Fin.cast hlen
      invFun := Fin.cast hlen.symm
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }
  let F : Fin (a + b) → ℝ := fun p =>
    coef ((List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get
            (Fin.cast hlen.symm p)) +
      ∑ j : Fin t, t₂.A i j *
        ButcherProduct.convAt t₂ coef
          ((List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get
            (Fin.cast hlen.symm p)) j
  have hreindex :
      (∏ p : Fin (List.replicate a BTree.leaf ++
                    List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).length,
          (coef ((List.replicate a BTree.leaf ++
                    List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get p) +
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef
                ((List.replicate a BTree.leaf ++
                    List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get p) j))
        = ∏ p : Fin (a + b), F p := by
    apply Fintype.prod_equiv e
    intro p
    simp [e, F]
  rw [hreindex]
  rw [Fin.prod_univ_add]
  have hleaf_factor : (∏ j : Fin a, F (Fin.castAdd b j))
      = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a := by
    have h : ∀ j : Fin a, F (Fin.castAdd b j)
            = coef BTree.leaf + ∑ j : Fin t, t₂.A i j := by
      intro j
      have hpos : ((Fin.cast hlen.symm (Fin.castAdd b j)) : ℕ) < a := by
        change ((Fin.castAdd b j) : ℕ) < a
        have : ((Fin.castAdd b j) : ℕ) = (j : ℕ) := rfl
        rw [this]
        exact j.isLt
      have hpos' :
          ((Fin.cast hlen.symm (Fin.castAdd b j)) : ℕ) <
            (List.replicate a BTree.leaf).length := by
        simp [List.length_replicate]
      have hget :
          (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get
            (Fin.cast hlen.symm (Fin.castAdd b j)) = BTree.leaf := by
        simp [List.get_eq_getElem, List.getElem_append_left]
      show F (Fin.castAdd b j) = _
      simp [F, ButcherProduct.convAt_leaf]
    calc (∏ j : Fin a, F (Fin.castAdd b j))
        = ∏ _ : Fin a, (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) :=
            Finset.prod_congr rfl (fun j _ => h j)
      _ = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdl_factor : (∏ j : Fin b, F (Fin.natAdd a j))
      = (coef (BTree.node [BTree.leaf, BTree.leaf]) +
          ∑ j : Fin t, t₂.A i j *
            (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) ^ b := by
    have h : ∀ j : Fin b, F (Fin.natAdd a j)
            = coef (BTree.node [BTree.leaf, BTree.leaf]) +
                ∑ j : Fin t, t₂.A i j *
                  (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2 := by
      intro j
      have hge : a ≤ ((Fin.cast hlen.symm (Fin.natAdd a j)) : ℕ) := by
        change a ≤ ((Fin.natAdd a j) : ℕ)
        have : ((Fin.natAdd a j) : ℕ) = a + (j : ℕ) := rfl
        rw [this]
        exact Nat.le_add_right _ _
      have hge' :
          (List.replicate a BTree.leaf).length ≤
            ((Fin.cast hlen.symm (Fin.natAdd a j)) : ℕ) := by
        simp [List.length_replicate]
      have hget :
          (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get
            (Fin.cast hlen.symm (Fin.natAdd a j))
              = BTree.node [BTree.leaf, BTree.leaf] := by
        simp [List.get_eq_getElem, List.getElem_append_right]
      show F (Fin.natAdd a j) = _
      simp only [F, hget]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [convAt_double_leaf_eq]
    calc (∏ j : Fin b, F (Fin.natAdd a j))
        = ∏ _ : Fin b, (coef (BTree.node [BTree.leaf, BTree.leaf]) +
              ∑ j : Fin t, t₂.A i j *
                (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) :=
            Finset.prod_congr rfl (fun j _ => h j)
      _ = (coef (BTree.node [BTree.leaf, BTree.leaf]) +
              ∑ j : Fin t, t₂.A i j *
                (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) ^ b := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hleaf_factor, hdl_factor]

private theorem bWeighted_convAt_node_mixed_leaf_double_leaf_cut_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (a b : ℕ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) i)
      = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            (coef BTree.leaf) ^ S_leaf.card *
              (coef (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
              (∑ χ : Fin (b - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef (coef BTree.leaf) χ *
                  t₂.bSeries
                    (doubleLeafChoiceTree (a - S_leaf.card) χ)) := by
  classical
  let X : ℝ := coef BTree.leaf
  let Y : ℝ := coef (BTree.node [BTree.leaf, BTree.leaf])
  let row : Fin t → ℝ := fun i => ∑ j : Fin t, t₂.A i j
  let chain : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  let dbl : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) ^ 2
  have hrow : ∀ i : Fin t,
      t₂.elementaryWeight (BTree.node [BTree.leaf]) i = row i := by
    intro i
    rw [ButcherTableau.elementaryWeight_singleton]
    simp [row]
  have hchain : ∀ i : Fin t,
      t₂.elementaryWeight (BTree.node [BTree.node [BTree.leaf]]) i = chain i := by
    intro i
    rw [ButcherTableau.elementaryWeight_singleton]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherTableau.elementaryWeight_singleton]
    simp
  have hdbl : ∀ i : Fin t,
      t₂.elementaryWeight
        (BTree.node [BTree.node [BTree.leaf, BTree.leaf]]) i = dbl i := by
    intro i
    rw [ButcherTableau.elementaryWeight_singleton]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact congrArg (fun z => t₂.A i j * z)
      (elementaryWeight_node_replicate_leaf t₂ 2 j)
  have hbSeries : ∀ aKeep : ℕ, ∀ n : ℕ, ∀ χ : Fin n → Fin 3,
      t₂.bSeries (doubleLeafChoiceTree aKeep χ)
        = ∑ i : Fin t, t₂.b i *
            (row i ^
              (aKeep + doubleLeafChoiceCount χ ⟨0, by decide⟩) *
              chain i ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
              dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩) := by
    intro aKeep n χ
    simp only [doubleLeafChoiceTree]
    rw [bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf]
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) i)
        = ∑ i : Fin t, t₂.b i *
            ((X + row i) ^ a *
              (Y + (X ^ 2 * row i + 2 * X * chain i + dbl i)) ^ b) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i _
          rw [convAt_node_mixed_leaf_double_leaf_at_i_eq]
          congr 1
          have hleaf :
              coef BTree.leaf + ∑ j : Fin t, t₂.A i j = X + row i := by
            simp [X, row]
          have hkeep :
              (∑ j : Fin t, t₂.A i j *
                  (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2)
                = X ^ 2 * row i + 2 * X * chain i + dbl i := by
            rw [bWeighted_kept_double_leaf_summand_eq]
            rw [hrow i, hchain i, hdbl i]
          rw [hleaf, hkeep]
    _ = ∑ i : Fin t, t₂.b i *
          (∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
              X ^ S_leaf.card * Y ^ S_dl.card *
                (∑ χ : Fin (b - S_dl.card) → Fin 3,
                  doubleLeafChoiceCoef X χ *
                    (row i ^
                      (a - S_leaf.card +
                        doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                      chain i ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                      dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i _
          rw [mixed_double_leaf_stage_polynomial_expand]
    _ = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            X ^ S_leaf.card * Y ^ S_dl.card *
              (∑ χ : Fin (b - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef X χ *
                  (∑ i : Fin t, t₂.b i *
                    (row i ^
                      (a - S_leaf.card +
                        doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                      chain i ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                      dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))) := by
          rw [weighted_mixed_double_leaf_stage_sum_expand]
    _ = ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            (coef BTree.leaf) ^ S_leaf.card *
              (coef (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
              (∑ χ : Fin (b - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef (coef BTree.leaf) χ *
                  t₂.bSeries
                    (doubleLeafChoiceTree (a - S_leaf.card) χ)) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S_leaf hS_leaf
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S_dl hS_dl
          simp only [X, Y]
          congr 1
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro χ _
          congr 1
          rw [← hbSeries (a - S_leaf.card) (b - S_dl.card) χ]

/-- §384 honest convolution closed form on the mixed root family
`BTree.node (List.replicate a BTree.leaf ++ List.replicate b
(BTree.node [BTree.leaf, BTree.leaf]))` (cycle 552). The squared
keep-factor on the double-leaf side keeps the result at the per-stage
level: the `bConv` value is the first tableau's `bSeries` plus the
`b`-weighted `Fin t`-sum of the per-stage closed form. -/
theorem ButcherProduct.bConv_node_mixed_leaf_double_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (a b : ℕ) :
    ButcherProduct.bConv (t₁.bSeries) t₂
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ i : Fin t, t₂.b i *
            ((t₁.bSeries BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a *
              (t₁.bSeries (BTree.node [BTree.leaf, BTree.leaf]) +
                ∑ j : Fin t, t₂.A i j *
                  (t₁.bSeries BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) ^ b) := by
  unfold ButcherProduct.bConv
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [convAt_node_mixed_leaf_double_leaf_at_i_eq]

/-- Headline §384 corollary on the mixed leaf / double-leaf root family
(cycle 552, fallback path): the product `bSeries` decomposes into the
first tableau's `bSeries` plus a `b`-weighted `Fin t`-sum of the
per-stage closed form. Cycle 553 will deliver the explicit cut-form
powerset expansion. -/
theorem ButcherProduct.bSeries_node_mixed_leaf_double_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (a b : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ i : Fin t, t₂.b i *
            ((t₁.bSeries BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a *
              (t₁.bSeries (BTree.node [BTree.leaf, BTree.leaf]) +
                ∑ j : Fin t, t₂.A i j *
                  (t₁.bSeries BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) ^ b) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_mixed_leaf_double_leaf_eq]

/-- §384 honest convolution closed form on the mixed leaf / double-leaf
root family, with each kept double-leaf summand collapsed to a `Fin 3`
choice over second-tableau `bSeries` values. -/
theorem ButcherProduct.bSeries_node_mixed_leaf_double_leaf_cut_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (a b : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ S_leaf ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
              (t₁.bSeries BTree.leaf) ^ S_leaf.card *
                (t₁.bSeries (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
                (∑ χ : Fin (b - S_dl.card) → Fin 3,
                  doubleLeafChoiceCoef (t₁.bSeries BTree.leaf) χ *
                    t₂.bSeries
                      (doubleLeafChoiceTree (a - S_leaf.card) χ)) := by
  rw [ButcherProduct.bSeries_eq_bConv]
  unfold ButcherProduct.bConv
  rw [bWeighted_convAt_node_mixed_leaf_double_leaf_cut_eq]


end ButcherTableau
