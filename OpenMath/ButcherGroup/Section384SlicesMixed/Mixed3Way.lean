import OpenMath.ButcherGroup.Section384SlicesMixed.Common
import OpenMath.ButcherGroup.Section384SlicesMixed.LeafFamilies

/-! # §384 mixed-slice three-way families (cycle 564 split)

`IsG1Equiv` slices for root families with two and three distinct
non-leaf shapes:

* mixed singleton-leaf + double-leaf (cycle 554)
* three-way mixed leaf + singleton-leaf + double-leaf (cycle 556)

Both rely on the `doubleLeafChoiceCount` / `doubleLeafChoiceTree` /
`doubleLeafChoiceCoef` machinery defined in `LeafFamilies.lean`.
-/

open Finset

namespace ButcherTableau

variable {s : ℕ}

/-! ### §384 mixed singleton-leaf / double-leaf root-children parametric helper

Cycle 554 combines the cycle 549 singleton-leaf machinery with the cycle
552/553 double-leaf machinery: each root child is either a singleton-leaf
node or an order-3 double-leaf node. Each kept singleton-leaf factor
contributes a `Fin 2` inner cut/keep choice; each kept double-leaf factor
contributes the cycle 553 `Fin 3` inner choice via `doubleLeafChoiceCoef`. -/

/-- Per-stage `convAt` value at the mixed root family
`replicate a (node [leaf]) ++ replicate b (node [leaf, leaf])`. -/
private theorem convAt_node_mixed_singleton_leaf_double_leaf_at_i_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (a b : ℕ)
    (i : Fin t) :
    ButcherProduct.convAt t₂ coef
        (BTree.node
          (List.replicate a (BTree.node [BTree.leaf]) ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) i
      = (coef (BTree.node [BTree.leaf]) +
          (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
            ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) ^ a *
        (coef (BTree.node [BTree.leaf, BTree.leaf]) +
          ∑ j : Fin t, t₂.A i j *
            (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) ^ b := by
  classical
  rw [ButcherProduct.convAt_node]
  have hprod_add :
      (∑ S : Finset
          (Fin (List.replicate a (BTree.node [BTree.leaf]) ++
                  List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).length),
          (∏ p ∈ S,
            coef ((List.replicate a (BTree.node [BTree.leaf]) ++
                    List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get p)) *
            (∏ p ∈ Sᶜ,
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  ((List.replicate a (BTree.node [BTree.leaf]) ++
                      List.replicate b
                        (BTree.node [BTree.leaf, BTree.leaf])).get p) j))
        = ∏ p : Fin (List.replicate a (BTree.node [BTree.leaf]) ++
                        List.replicate b
                          (BTree.node [BTree.leaf, BTree.leaf])).length,
            (coef ((List.replicate a (BTree.node [BTree.leaf]) ++
                      List.replicate b
                        (BTree.node [BTree.leaf, BTree.leaf])).get p) +
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  ((List.replicate a (BTree.node [BTree.leaf]) ++
                      List.replicate b
                        (BTree.node [BTree.leaf, BTree.leaf])).get p) j) := by
    rw [Finset.prod_add (s := Finset.univ)
        (f := fun p =>
          coef ((List.replicate a (BTree.node [BTree.leaf]) ++
                  List.replicate b
                    (BTree.node [BTree.leaf, BTree.leaf])).get p))
        (g := fun p =>
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef
              ((List.replicate a (BTree.node [BTree.leaf]) ++
                  List.replicate b
                    (BTree.node [BTree.leaf, BTree.leaf])).get p) j)]
    rw [Finset.powerset_univ]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [(Finset.compl_eq_univ_sdiff S).symm]
  rw [hprod_add]
  have hlen :
      (List.replicate a (BTree.node [BTree.leaf]) ++
          List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).length
        = a + b := by
    simp [List.length_append, List.length_replicate]
  let e :
      Fin (List.replicate a (BTree.node [BTree.leaf]) ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).length ≃
        Fin (a + b) :=
    { toFun := Fin.cast hlen
      invFun := Fin.cast hlen.symm
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }
  let F : Fin (a + b) → ℝ := fun p =>
    coef ((List.replicate a (BTree.node [BTree.leaf]) ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get
            (Fin.cast hlen.symm p)) +
      ∑ j : Fin t, t₂.A i j *
        ButcherProduct.convAt t₂ coef
          ((List.replicate a (BTree.node [BTree.leaf]) ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get
            (Fin.cast hlen.symm p)) j
  have hreindex :
      (∏ p : Fin (List.replicate a (BTree.node [BTree.leaf]) ++
                    List.replicate b
                      (BTree.node [BTree.leaf, BTree.leaf])).length,
          (coef ((List.replicate a (BTree.node [BTree.leaf]) ++
                    List.replicate b
                      (BTree.node [BTree.leaf, BTree.leaf])).get p) +
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef
                ((List.replicate a (BTree.node [BTree.leaf]) ++
                    List.replicate b
                      (BTree.node [BTree.leaf, BTree.leaf])).get p) j))
        = ∏ p : Fin (a + b), F p := by
    apply Fintype.prod_equiv e
    intro p
    simp [e, F]
  rw [hreindex]
  rw [Fin.prod_univ_add]
  have hsl_factor : (∏ j : Fin a, F (Fin.castAdd b j))
      = (coef (BTree.node [BTree.leaf]) +
          (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
            ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) ^ a := by
    have h : ∀ j : Fin a, F (Fin.castAdd b j)
            = coef (BTree.node [BTree.leaf]) +
                (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                  ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) := by
      intro j
      have hpos : ((Fin.cast hlen.symm (Fin.castAdd b j)) : ℕ) < a := by
        change ((Fin.castAdd b j) : ℕ) < a
        have : ((Fin.castAdd b j) : ℕ) = (j : ℕ) := rfl
        rw [this]
        exact j.isLt
      have hpos' :
          ((Fin.cast hlen.symm (Fin.castAdd b j)) : ℕ) <
            (List.replicate a (BTree.node [BTree.leaf])).length := by
        simp [List.length_replicate]
      have hget :
          (List.replicate a (BTree.node [BTree.leaf]) ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])).get
            (Fin.cast hlen.symm (Fin.castAdd b j)) = BTree.node [BTree.leaf] := by
        simp [List.get_eq_getElem, List.getElem_append_left]
      show F (Fin.castAdd b j) = _
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
    calc (∏ j : Fin a, F (Fin.castAdd b j))
        = ∏ _ : Fin a, (coef (BTree.node [BTree.leaf]) +
              (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) :=
            Finset.prod_congr rfl (fun j _ => h j)
      _ = (coef (BTree.node [BTree.leaf]) +
              (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) ^ a := by
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
          (List.replicate a (BTree.node [BTree.leaf])).length ≤
            ((Fin.cast hlen.symm (Fin.natAdd a j)) : ℕ) := by
        simp [List.length_replicate]
      have hget :
          (List.replicate a (BTree.node [BTree.leaf]) ++
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
  rw [hsl_factor, hdl_factor]

/-- Per-stage polynomial expansion for the mixed singleton-leaf /
double-leaf closed form. -/
private theorem mixed_singleton_leaf_double_leaf_stage_polynomial_expand
    (X Y_sl Y_dl R C D : ℝ) (a b : ℕ) :
    (Y_sl + (X * R + C)) ^ a * (Y_dl + (X ^ 2 * R + 2 * X * C + D)) ^ b
      = ∑ S_sl ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
                X ^ T.card *
                  (∑ χ : Fin (b - S_dl.card) → Fin 3,
                    doubleLeafChoiceCoef X χ *
                      (R ^ (T.card +
                              doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                        C ^ (((S_slᶜ : Finset (Fin a)).card - T.card) +
                              doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                        D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))) := by
  classical
  rw [pow_add_eq_powerset Y_sl (X * R + C) a]
  rw [pow_add_eq_powerset Y_dl (X ^ 2 * R + 2 * X * C + D) b]
  rw [Finset.sum_mul]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_sl hS_sl
  rw [Finset.mul_sum]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_dl hS_dl
  have hS_sl_card :
      a - S_sl.card
        = (S_slᶜ : Finset (Fin a)).card := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin]
  -- inner singleton-leaf expansion: (X*R + C)^(a - S_sl.card)
  have hinner_sl :
      (X * R + C) ^ (a - S_sl.card)
        = ∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
            (X * R) ^ T.card *
              C ^ ((S_slᶜ : Finset (Fin a)).card - T.card) := by
    calc
      (X * R + C) ^ (a - S_sl.card)
          = ∏ _p ∈ (S_slᶜ : Finset (Fin a)), (X * R + C) := by
              rw [hS_sl_card, Finset.prod_const]
      _ = ∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
            (X * R) ^ T.card *
              C ^ ((S_slᶜ : Finset (Fin a)).card - T.card) := by
              rw [prod_const_add_eq_powerset]
  -- inner double-leaf expansion: (X^2*R + 2*X*C + D)^(b - S_dl.card)
  have hinner_dl :
      (X ^ 2 * R + 2 * X * C + D) ^ (b - S_dl.card)
        = ∑ χ : Fin (b - S_dl.card) → Fin 3,
            doubleLeafChoiceCoef X χ *
              (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩) := by
    rw [double_leaf_kept_pow_expand]
  rw [hinner_sl, hinner_dl]
  calc
    Y_sl ^ S_sl.card *
        (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
          (X * R) ^ T.card *
            C ^ ((S_slᶜ : Finset (Fin a)).card - T.card)) *
        (Y_dl ^ S_dl.card *
          (∑ χ : Fin (b - S_dl.card) → Fin 3,
            doubleLeafChoiceCoef X χ *
              (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))
        = Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
            ((∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
              (X * R) ^ T.card *
                C ^ ((S_slᶜ : Finset (Fin a)).card - T.card)) *
              (∑ χ : Fin (b - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef X χ *
                  (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                    C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                    D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))) := by ring
    _ = Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
          (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
            (X * R) ^ T.card *
              C ^ ((S_slᶜ : Finset (Fin a)).card - T.card) *
              (∑ χ : Fin (b - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef X χ *
                  (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                    C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                    D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))) := by
          rw [Finset.sum_mul]
    _ = Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
          (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
            X ^ T.card *
              (∑ χ : Fin (b - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef X χ *
                  (R ^ (T.card +
                          doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                    C ^ (((S_slᶜ : Finset (Fin a)).card - T.card) +
                          doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                    D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))) := by
          congr 1
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro T hT
          rw [mul_pow, Finset.mul_sum]
          rw [Finset.mul_sum]
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro χ _
          calc
            X ^ T.card * R ^ T.card *
                C ^ ((S_slᶜ : Finset (Fin a)).card - T.card) *
                (doubleLeafChoiceCoef X χ *
                  (R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩ *
                    C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩ *
                    D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))
                = X ^ T.card *
                    (doubleLeafChoiceCoef X χ *
                      ((R ^ T.card *
                          R ^ doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                        (C ^ ((S_slᶜ : Finset (Fin a)).card - T.card) *
                          C ^ doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                        D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) := by ring
              _ = X ^ T.card *
                    (doubleLeafChoiceCoef X χ *
                      (R ^ (T.card +
                              doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                        C ^ (((S_slᶜ : Finset (Fin a)).card - T.card) +
                              doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                        D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) := by
                    rw [← pow_add, ← pow_add]

/-- Reorder the stage-weighted mixed polynomial expansion so the tableau
stage sum is inside the four cut-set sums. -/
private theorem weighted_mixed_singleton_leaf_double_leaf_stage_sum_expand
    {t : ℕ} (w row chain dbl : Fin t → ℝ) (X Y_sl Y_dl : ℝ) (a b : ℕ) :
    (∑ i : Fin t, w i *
      (∑ S_sl ∈ (Finset.univ : Finset (Fin a)).powerset,
        ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
          Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
            (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
              X ^ T.card *
                (∑ χ : Fin (b - S_dl.card) → Fin 3,
                  doubleLeafChoiceCoef X χ *
                    (row i ^ (T.card +
                            doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                      chain i ^ (((S_slᶜ : Finset (Fin a)).card - T.card) +
                                  doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                      dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))))
      = ∑ S_sl ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
                X ^ T.card *
                  (∑ χ : Fin (b - S_dl.card) → Fin 3,
                    doubleLeafChoiceCoef X χ *
                      (∑ i : Fin t, w i *
                        (row i ^ (T.card +
                                doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                          chain i ^ (((S_slᶜ : Finset (Fin a)).card - T.card) +
                                      doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                          dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_sl hS_sl
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_dl hS_dl
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro T hT
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro χ hχ
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro i hi
  ring

/-- b-weighted `convAt` cut form on the mixed singleton-leaf / double-leaf
root family. -/
private theorem bWeighted_convAt_node_mixed_singleton_leaf_double_leaf_cut_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (a b : ℕ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate a (BTree.node [BTree.leaf]) ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) i)
      = ∑ S_sl ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            (coef (BTree.node [BTree.leaf])) ^ S_sl.card *
              (coef (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
                (coef BTree.leaf) ^ T.card *
                  (∑ χ : Fin (b - S_dl.card) → Fin 3,
                    doubleLeafChoiceCoef (coef BTree.leaf) χ *
                      t₂.bSeries
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
  classical
  let X : ℝ := coef BTree.leaf
  let Y_sl : ℝ := coef (BTree.node [BTree.leaf])
  let Y_dl : ℝ := coef (BTree.node [BTree.leaf, BTree.leaf])
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
  have hbSeries : ∀ m n p : ℕ,
      t₂.bSeries
          (BTree.node
            (List.replicate m BTree.leaf ++
              List.replicate n (BTree.node [BTree.leaf]) ++
              List.replicate p (BTree.node [BTree.leaf, BTree.leaf])))
        = ∑ i : Fin t, t₂.b i *
            (row i ^ m * chain i ^ n * dbl i ^ p) := by
    intro m n p
    rw [bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf]
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate a (BTree.node [BTree.leaf]) ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) i)
        = ∑ i : Fin t, t₂.b i *
            ((Y_sl + (X * row i + chain i)) ^ a *
              (Y_dl + (X ^ 2 * row i + 2 * X * chain i + dbl i)) ^ b) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i _
          rw [convAt_node_mixed_singleton_leaf_double_leaf_at_i_eq]
          congr 1
          have hsl :
              coef (BTree.node [BTree.leaf]) +
                  (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))
                = Y_sl + (X * row i + chain i) := by
            simp [Y_sl, X, row, chain]
          have hdl :
              coef (BTree.node [BTree.leaf, BTree.leaf]) +
                  ∑ j : Fin t, t₂.A i j *
                    (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2
                = Y_dl + (X ^ 2 * row i + 2 * X * chain i + dbl i) := by
            rw [bWeighted_kept_double_leaf_summand_eq]
            rw [hrow i, hchain i, hdbl i]
          rw [hsl, hdl]
    _ = ∑ i : Fin t, t₂.b i *
          (∑ S_sl ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
              Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
                  X ^ T.card *
                    (∑ χ : Fin (b - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef X χ *
                        (row i ^ (T.card +
                                doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                          chain i ^ (((S_slᶜ : Finset (Fin a)).card - T.card) +
                                      doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                          dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i _
          rw [mixed_singleton_leaf_double_leaf_stage_polynomial_expand]
    _ = ∑ S_sl ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
                X ^ T.card *
                  (∑ χ : Fin (b - S_dl.card) → Fin 3,
                    doubleLeafChoiceCoef X χ *
                      (∑ i : Fin t, t₂.b i *
                        (row i ^ (T.card +
                                doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                          chain i ^ (((S_slᶜ : Finset (Fin a)).card - T.card) +
                                      doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                          dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))) := by
          rw [weighted_mixed_singleton_leaf_double_leaf_stage_sum_expand]
    _ = ∑ S_sl ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
            (coef (BTree.node [BTree.leaf])) ^ S_sl.card *
              (coef (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
                (coef BTree.leaf) ^ T.card *
                  (∑ χ : Fin (b - S_dl.card) → Fin 3,
                    doubleLeafChoiceCoef (coef BTree.leaf) χ *
                      t₂.bSeries
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
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S_sl hS_sl
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S_dl hS_dl
          simp only [X, Y_sl, Y_dl]
          congr 1
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro T hT
          congr 1
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro χ _
          congr 1
          rw [← hbSeries
              (T.card + doubleLeafChoiceCount χ ⟨0, by decide⟩)
              (((S_slᶜ : Finset (Fin a)).card - T.card)
                + doubleLeafChoiceCount χ ⟨1, by decide⟩)
              (doubleLeafChoiceCount χ ⟨2, by decide⟩)]

/-- §384 honest convolution closed form on the mixed singleton-leaf /
double-leaf root family. Each kept singleton-leaf has a `Fin 2` inner
cut/keep choice for its leaf; each kept double-leaf has a `Fin 3` inner
choice via `doubleLeafChoiceCoef`. -/
theorem ButcherProduct.bSeries_node_mixed_singleton_leaf_double_leaf_cut_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (a b : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node
          (List.replicate a (BTree.node [BTree.leaf]) ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate a (BTree.node [BTree.leaf]) ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ S_sl ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin b)).powerset,
              (t₁.bSeries (BTree.node [BTree.leaf])) ^ S_sl.card *
                (t₁.bSeries (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin a)).powerset,
                  (t₁.bSeries BTree.leaf) ^ T.card *
                    (∑ χ : Fin (b - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef (t₁.bSeries BTree.leaf) χ *
                        t₂.bSeries
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
  rw [ButcherProduct.bSeries_eq_bConv]
  unfold ButcherProduct.bConv
  rw [bWeighted_convAt_node_mixed_singleton_leaf_double_leaf_cut_eq]

/-! ### §384 three-way mixed leaf / singleton-leaf / double-leaf root family

Cycle 556 unifies the three pairwise families (cycles 549, 552/553, 554)
into one closed form: each root child is a `BTree.leaf`, a singleton-leaf
`BTree.node [BTree.leaf]`, or a double-leaf
`BTree.node [BTree.leaf, BTree.leaf]`. -/

/-- Per-stage `convAt` value at the three-way mixed root family
`replicate a leaf ++ replicate b (node [leaf]) ++ replicate c (node [leaf, leaf])`. -/
private theorem convAt_node_mixed_leaf_singleton_leaf_double_leaf_at_i_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (a b c : ℕ)
    (i : Fin t) :
    ButcherProduct.convAt t₂ coef
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))) i
      = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a *
        (coef (BTree.node [BTree.leaf]) +
          (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
            ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) ^ b *
        (coef (BTree.node [BTree.leaf, BTree.leaf]) +
          ∑ j : Fin t, t₂.A i j *
            (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) ^ c := by
  classical
  set L : List BTree :=
      List.replicate a BTree.leaf ++
        List.replicate b (BTree.node [BTree.leaf]) ++
          List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) with hL
  rw [ButcherProduct.convAt_node]
  have hprod_add :
      (∑ S : Finset (Fin L.length),
        (∏ p ∈ S, coef (L.get p)) *
          (∏ p ∈ Sᶜ,
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef (L.get p) j))
        = ∏ p : Fin L.length,
            (coef (L.get p) +
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef (L.get p) j) := by
    rw [Finset.prod_add (s := Finset.univ)
        (f := fun p => coef (L.get p))
        (g := fun p =>
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef (L.get p) j)]
    rw [Finset.powerset_univ]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [(Finset.compl_eq_univ_sdiff S).symm]
  rw [hprod_add]
  have hlen : L.length = a + b + c := by
    simp only [hL, List.length_append, List.length_replicate]
  let e : Fin L.length ≃ Fin (a + b + c) :=
    { toFun := Fin.cast hlen
      invFun := Fin.cast hlen.symm
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }
  let F : Fin (a + b + c) → ℝ := fun p =>
    coef (L.get (Fin.cast hlen.symm p)) +
      ∑ j : Fin t, t₂.A i j *
        ButcherProduct.convAt t₂ coef (L.get (Fin.cast hlen.symm p)) j
  have hreindex :
      (∏ p : Fin L.length,
          (coef (L.get p) +
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef (L.get p) j))
        = ∏ p : Fin (a + b + c), F p := by
    apply Fintype.prod_equiv e
    intro p
    simp [e, F]
  rw [hreindex]
  rw [Fin.prod_univ_add (M := ℝ) (a := a + b) (b := c) (f := F)]
  rw [Fin.prod_univ_add (M := ℝ) (a := a) (b := b)
      (f := fun p => F (Fin.castAdd c p))]
  -- leaf factor
  have hleaf_factor :
      (∏ j : Fin a, F (Fin.castAdd c (Fin.castAdd b j)))
        = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a := by
    have h : ∀ j : Fin a, F (Fin.castAdd c (Fin.castAdd b j))
              = coef BTree.leaf + ∑ j : Fin t, t₂.A i j := by
      intro j
      have hget : L.get (Fin.cast hlen.symm
            (Fin.castAdd c (Fin.castAdd b j))) = BTree.leaf := by
        simp [hL, List.get_eq_getElem]
      show F (Fin.castAdd c (Fin.castAdd b j)) = _
      simp only [F, hget]
      simp [ButcherProduct.convAt_leaf]
    calc (∏ j : Fin a, F (Fin.castAdd c (Fin.castAdd b j)))
        = ∏ _ : Fin a, (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) :=
            Finset.prod_congr rfl (fun j _ => h j)
      _ = (coef BTree.leaf + ∑ j : Fin t, t₂.A i j) ^ a := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- singleton-leaf factor
  have hsl_factor :
      (∏ j : Fin b, F (Fin.castAdd c (Fin.natAdd a j)))
        = (coef (BTree.node [BTree.leaf]) +
            (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
              ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) ^ b := by
    have h : ∀ j : Fin b, F (Fin.castAdd c (Fin.natAdd a j))
              = coef (BTree.node [BTree.leaf]) +
                  (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) := by
      intro j
      have hget : L.get (Fin.cast hlen.symm
            (Fin.castAdd c (Fin.natAdd a j))) = BTree.node [BTree.leaf] := by
        simp [hL, List.get_eq_getElem]
      show F (Fin.castAdd c (Fin.natAdd a j)) = _
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
    calc (∏ j : Fin b, F (Fin.castAdd c (Fin.natAdd a j)))
        = ∏ _ : Fin b, (coef (BTree.node [BTree.leaf]) +
              (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) :=
            Finset.prod_congr rfl (fun j _ => h j)
      _ = (coef (BTree.node [BTree.leaf]) +
              (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) ^ b := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- double-leaf factor
  have hdl_factor :
      (∏ j : Fin c, F (Fin.natAdd (a + b) j))
        = (coef (BTree.node [BTree.leaf, BTree.leaf]) +
            ∑ j : Fin t, t₂.A i j *
              (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) ^ c := by
    have h : ∀ j : Fin c, F (Fin.natAdd (a + b) j)
              = coef (BTree.node [BTree.leaf, BTree.leaf]) +
                  ∑ j : Fin t, t₂.A i j *
                    (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2 := by
      intro j
      have hget : L.get (Fin.cast hlen.symm (Fin.natAdd (a + b) j))
            = BTree.node [BTree.leaf, BTree.leaf] := by
        simp [hL, List.get_eq_getElem, List.getElem_append, List.getElem_replicate,
              List.length_replicate]
        split_ifs with h1 h2 <;> [omega; omega; rfl]
      show F (Fin.natAdd (a + b) j) = _
      simp only [F, hget]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [convAt_double_leaf_eq]
    calc (∏ j : Fin c, F (Fin.natAdd (a + b) j))
        = ∏ _ : Fin c, (coef (BTree.node [BTree.leaf, BTree.leaf]) +
              ∑ j : Fin t, t₂.A i j *
                (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) :=
            Finset.prod_congr rfl (fun j _ => h j)
      _ = (coef (BTree.node [BTree.leaf, BTree.leaf]) +
              ∑ j : Fin t, t₂.A i j *
                (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2) ^ c := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hleaf_factor, hsl_factor, hdl_factor]

/-- Per-stage polynomial expansion for the three-way mixed
leaf / singleton-leaf / double-leaf closed form. -/
private theorem mixed_leaf_singleton_leaf_double_leaf_stage_polynomial_expand
    (X Y_sl Y_dl R C D : ℝ) (a b c : ℕ) :
    (X + R) ^ a *
        ((Y_sl + (X * R + C)) ^ b *
          (Y_dl + (X ^ 2 * R + 2 * X * C + D)) ^ c)
      = ∑ S_l ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin c)).powerset,
              X ^ S_l.card * Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  X ^ T.card *
                    (∑ χ : Fin (c - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef X χ *
                        (R ^ ((a - S_l.card) + T.card +
                                doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                          C ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                                doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                          D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))) := by
  classical
  rw [pow_add_eq_powerset X R a]
  rw [mixed_singleton_leaf_double_leaf_stage_polynomial_expand X Y_sl Y_dl R C D b c]
  rw [Finset.sum_mul]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_l hS_l
  rw [Finset.mul_sum]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_sl hS_sl
  rw [Finset.mul_sum]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_dl hS_dl
  calc
    X ^ S_l.card * R ^ (a - S_l.card) *
        (Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
          (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
            X ^ T.card *
              (∑ χ : Fin (c - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef X χ *
                  (R ^ (T.card +
                          doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                    C ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                          doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                    D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))))
        = X ^ S_l.card * Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
            (R ^ (a - S_l.card) *
              (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                X ^ T.card *
                  (∑ χ : Fin (c - S_dl.card) → Fin 3,
                    doubleLeafChoiceCoef X χ *
                      (R ^ (T.card +
                              doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                        C ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                              doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                        D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))) := by
            ring
    _ = X ^ S_l.card * Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
          (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
            X ^ T.card *
              (∑ χ : Fin (c - S_dl.card) → Fin 3,
                doubleLeafChoiceCoef X χ *
                  (R ^ ((a - S_l.card) + T.card +
                          doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                    C ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                          doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                    D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))) := by
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr (M := ℝ) rfl ?_
            intro T hT
            rw [show R ^ (a - S_l.card) *
                  (X ^ T.card *
                    ∑ χ : Fin (c - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef X χ *
                        (R ^ (T.card + doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                          C ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                                doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                          D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) =
                X ^ T.card *
                  (R ^ (a - S_l.card) *
                    ∑ χ : Fin (c - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef X χ *
                        (R ^ (T.card + doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                          C ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                                doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                          D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)) from by ring]
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr (M := ℝ) rfl ?_
            intro χ _
            calc
              R ^ (a - S_l.card) *
                  (doubleLeafChoiceCoef X χ *
                    (R ^ (T.card + doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                      C ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                            doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                      D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩))
                  = doubleLeafChoiceCoef X χ *
                      ((R ^ (a - S_l.card) *
                          R ^ (T.card + doubleLeafChoiceCount χ ⟨0, by decide⟩)) *
                        C ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                              doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                        D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩) := by ring
                _ = doubleLeafChoiceCoef X χ *
                      (R ^ ((a - S_l.card) + T.card +
                              doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                        C ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                              doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                        D ^ doubleLeafChoiceCount χ ⟨2, by decide⟩) := by
                    rw [← pow_add, ← Nat.add_assoc]

/-- Reorder the stage-weighted three-way mixed polynomial expansion so the
tableau stage sum is inside the four cut-set sums. -/
private theorem weighted_mixed_leaf_singleton_leaf_double_leaf_stage_sum_expand
    {t : ℕ} (w row chain dbl : Fin t → ℝ) (X Y_sl Y_dl : ℝ) (a b c : ℕ) :
    (∑ i : Fin t, w i *
      (∑ S_l ∈ (Finset.univ : Finset (Fin a)).powerset,
        ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
          ∑ S_dl ∈ (Finset.univ : Finset (Fin c)).powerset,
            X ^ S_l.card * Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
              (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                X ^ T.card *
                  (∑ χ : Fin (c - S_dl.card) → Fin 3,
                    doubleLeafChoiceCoef X χ *
                      (row i ^ ((a - S_l.card) + T.card +
                              doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                        chain i ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                                    doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                        dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))))
      = ∑ S_l ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin c)).powerset,
              X ^ S_l.card * Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  X ^ T.card *
                    (∑ χ : Fin (c - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef X χ *
                        (∑ i : Fin t, w i *
                          (row i ^ ((a - S_l.card) + T.card +
                                  doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                            chain i ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                                        doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                            dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_l hS_l
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_sl hS_sl
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S_dl hS_dl
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro T hT
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro χ hχ
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro i hi
  ring

/-- b-weighted `convAt` cut form on the three-way mixed
leaf / singleton-leaf / double-leaf root family. -/
private theorem bWeighted_convAt_node_mixed_leaf_singleton_leaf_double_leaf_cut_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (a b c : ℕ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf]) ++
                List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))) i)
      = ∑ S_l ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin c)).powerset,
              (coef BTree.leaf) ^ S_l.card *
                (coef (BTree.node [BTree.leaf])) ^ S_sl.card *
                (coef (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  (coef BTree.leaf) ^ T.card *
                    (∑ χ : Fin (c - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef (coef BTree.leaf) χ *
                        t₂.bSeries
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
  classical
  let X : ℝ := coef BTree.leaf
  let Y_sl : ℝ := coef (BTree.node [BTree.leaf])
  let Y_dl : ℝ := coef (BTree.node [BTree.leaf, BTree.leaf])
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
  have hbSeries : ∀ m n p : ℕ,
      t₂.bSeries
          (BTree.node
            (List.replicate m BTree.leaf ++
              List.replicate n (BTree.node [BTree.leaf]) ++
              List.replicate p (BTree.node [BTree.leaf, BTree.leaf])))
        = ∑ i : Fin t, t₂.b i *
            (row i ^ m * chain i ^ n * dbl i ^ p) := by
    intro m n p
    rw [bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf]
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf]) ++
                List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))) i)
        = ∑ i : Fin t, t₂.b i *
            ((X + row i) ^ a *
              ((Y_sl + (X * row i + chain i)) ^ b *
                (Y_dl + (X ^ 2 * row i + 2 * X * chain i + dbl i)) ^ c)) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i _
          rw [convAt_node_mixed_leaf_singleton_leaf_double_leaf_at_i_eq]
          have hleaf : coef BTree.leaf + ∑ j : Fin t, t₂.A i j = X + row i := by
            simp [X, row]
          have hsl :
              coef (BTree.node [BTree.leaf]) +
                  (coef BTree.leaf * (∑ j : Fin t, t₂.A i j) +
                    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))
                = Y_sl + (X * row i + chain i) := by
            simp [Y_sl, X, row, chain]
          have hdl :
              coef (BTree.node [BTree.leaf, BTree.leaf]) +
                  ∑ j : Fin t, t₂.A i j *
                    (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) ^ 2
                = Y_dl + (X ^ 2 * row i + 2 * X * chain i + dbl i) := by
            rw [bWeighted_kept_double_leaf_summand_eq]
            rw [hrow i, hchain i, hdbl i]
          rw [hleaf, hsl, hdl]
          ring
    _ = ∑ i : Fin t, t₂.b i *
          (∑ S_l ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
              ∑ S_dl ∈ (Finset.univ : Finset (Fin c)).powerset,
                X ^ S_l.card * Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
                  (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                    X ^ T.card *
                      (∑ χ : Fin (c - S_dl.card) → Fin 3,
                        doubleLeafChoiceCoef X χ *
                          (row i ^ ((a - S_l.card) + T.card +
                                  doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                            chain i ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                                        doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                            dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i _
          rw [mixed_leaf_singleton_leaf_double_leaf_stage_polynomial_expand]
    _ = ∑ S_l ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin c)).powerset,
              X ^ S_l.card * Y_sl ^ S_sl.card * Y_dl ^ S_dl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  X ^ T.card *
                    (∑ χ : Fin (c - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef X χ *
                        (∑ i : Fin t, t₂.b i *
                          (row i ^ ((a - S_l.card) + T.card +
                                  doubleLeafChoiceCount χ ⟨0, by decide⟩) *
                            chain i ^ (((S_slᶜ : Finset (Fin b)).card - T.card) +
                                        doubleLeafChoiceCount χ ⟨1, by decide⟩) *
                            dbl i ^ doubleLeafChoiceCount χ ⟨2, by decide⟩)))) := by
          rw [weighted_mixed_leaf_singleton_leaf_double_leaf_stage_sum_expand]
    _ = ∑ S_l ∈ (Finset.univ : Finset (Fin a)).powerset,
          ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
            ∑ S_dl ∈ (Finset.univ : Finset (Fin c)).powerset,
              (coef BTree.leaf) ^ S_l.card *
                (coef (BTree.node [BTree.leaf])) ^ S_sl.card *
                (coef (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
                (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                  (coef BTree.leaf) ^ T.card *
                    (∑ χ : Fin (c - S_dl.card) → Fin 3,
                      doubleLeafChoiceCoef (coef BTree.leaf) χ *
                        t₂.bSeries
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
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S_l hS_l
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S_sl hS_sl
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S_dl hS_dl
          simp only [X, Y_sl, Y_dl]
          congr 1
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro T hT
          congr 1
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro χ _
          congr 1
          rw [← hbSeries
              ((a - S_l.card) + T.card + doubleLeafChoiceCount χ ⟨0, by decide⟩)
              (((S_slᶜ : Finset (Fin b)).card - T.card)
                + doubleLeafChoiceCount χ ⟨1, by decide⟩)
              (doubleLeafChoiceCount χ ⟨2, by decide⟩)]

/-- §384 honest convolution closed form on the three-way mixed
leaf / singleton-leaf / double-leaf root family. Each kept leaf at the root
contributes only via cut/keep; each kept singleton-leaf has a `Fin 2` inner
cut/keep; each kept double-leaf has a `Fin 3` inner choice. -/
theorem ButcherProduct.bSeries_node_mixed_leaf_singleton_leaf_double_leaf_cut_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (a b c : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf]) ++
                List.replicate c (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ S_l ∈ (Finset.univ : Finset (Fin a)).powerset,
            ∑ S_sl ∈ (Finset.univ : Finset (Fin b)).powerset,
              ∑ S_dl ∈ (Finset.univ : Finset (Fin c)).powerset,
                (t₁.bSeries BTree.leaf) ^ S_l.card *
                  (t₁.bSeries (BTree.node [BTree.leaf])) ^ S_sl.card *
                  (t₁.bSeries (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card *
                  (∑ T ∈ (S_slᶜ : Finset (Fin b)).powerset,
                    (t₁.bSeries BTree.leaf) ^ T.card *
                      (∑ χ : Fin (c - S_dl.card) → Fin 3,
                        doubleLeafChoiceCoef (t₁.bSeries BTree.leaf) χ *
                          t₂.bSeries
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
  rw [ButcherProduct.bSeries_eq_bConv]
  unfold ButcherProduct.bConv
  rw [bWeighted_convAt_node_mixed_leaf_singleton_leaf_double_leaf_cut_eq]


end ButcherTableau
