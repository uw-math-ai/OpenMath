import OpenMath.ButcherGroup.Section384SlicesMixed.Common
import OpenMath.ButcherGroup.Section384SlicesMixed.LeafFamilies

/-! # §384 mixed-slice replicate / triple-leaf families (cycle 564 split)

Closed forms on root families with a single repeated child shape:

* standalone triple-leaf single tree (cycle 557) — defines the
  `tripleLeafChoiceCount` / `tripleLeafChoiceCoef` `Fin 4` case helper.
* parametric all-double-leaf family (cycle 562) — derived from the
  cycle 552/553 mixed leaf + double-leaf cut form by specializing
  `a = 0`.
* parametric all-triple-leaf family (cycle 563) — defines the
  `tripleLeafRootChoiceCount` / `tripleLeafChoiceFunctionCoef` /
  `tripleLeafChoiceTree` machinery shared with future mixed
  triple-leaf slices.
-/

open Finset

namespace ButcherTableau

variable {s : ℕ}

/-! ### §384 standalone triple-leaf node slice

Cycle 557 groups the all-leaves `n = 3` powerset expansion into the four
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

/-! ### §384 all-triple-leaf parametric family -/

/-- Count how many kept triple-leaf root children choose a given internal
cut-count case. Index `0` keeps three internal leaves, index `1` keeps two,
index `2` keeps one, and index `3` cuts all three. -/
def tripleLeafRootChoiceCount {n : ℕ} (χ : Fin n → Fin 4) (r : Fin 4) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun p => χ p = r).card

/-- Scalar coefficient contributed by a choice function in the kept
triple-leaf expansion. -/
noncomputable def tripleLeafChoiceFunctionCoef {n : ℕ}
    (x : ℝ) (χ : Fin n → Fin 4) : ℝ :=
  ∏ p : Fin n, tripleLeafChoiceCoef (χ p) x 1

/-- The second-tableau tree produced by a choice function over the kept
triple-leaf root children. The four groups are ordered by residual child
order: leaf, singleton-leaf, double-leaf, triple-leaf. -/
def tripleLeafChoiceTree {n : ℕ} (χ : Fin n → Fin 4) : BTree :=
  BTree.node
    (List.replicate
        (tripleLeafRootChoiceCount χ ⟨3, by decide⟩) BTree.leaf ++
      List.replicate
        (tripleLeafRootChoiceCount χ ⟨2, by decide⟩)
          (BTree.node [BTree.leaf]) ++
      List.replicate
        (tripleLeafRootChoiceCount χ ⟨1, by decide⟩)
          (BTree.node [BTree.leaf, BTree.leaf]) ++
      List.replicate
        (tripleLeafRootChoiceCount χ ⟨0, by decide⟩)
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))

private theorem tripleLeafChoice_value_product_eq
    {n : ℕ} (row chain dbl tri : ℝ) (χ : Fin n → Fin 4) :
    (∏ p : Fin n,
      match χ p with
      | ⟨0, _⟩ => tri
      | ⟨1, _⟩ => dbl
      | ⟨2, _⟩ => chain
      | ⟨3, _⟩ => row)
      = row ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
          chain ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
          dbl ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
          tri ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩ := by
  classical
  let f : Fin 4 → ℝ := fun r =>
    match r with
    | ⟨0, _⟩ => tri
    | ⟨1, _⟩ => dbl
    | ⟨2, _⟩ => chain
    | ⟨3, _⟩ => row
  have hfiber :
      (∏ r : Fin 4,
          ∏ p ∈ (Finset.univ : Finset (Fin n)).filter (fun p => χ p = r),
            f r)
        = ∏ p : Fin n, f (χ p) := by
    simpa [f] using
      (Finset.prod_fiberwise_eq_prod_filter'
        (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (Fin 4))) (g := χ) (f := f))
  calc
    (∏ p : Fin n,
      match χ p with
      | ⟨0, _⟩ => tri
      | ⟨1, _⟩ => dbl
      | ⟨2, _⟩ => chain
      | ⟨3, _⟩ => row)
        = ∏ p : Fin n, f (χ p) := by
          refine Finset.prod_congr rfl ?_
          intro p _
          simp [f]
    _ = ∏ r : Fin 4,
          ∏ p ∈ (Finset.univ : Finset (Fin n)).filter (fun p => χ p = r),
            f r := hfiber.symm
    _ = row ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
          chain ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
          dbl ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
          tri ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩ := by
          simp [Fin.prod_univ_four, tripleLeafRootChoiceCount, f]
          ring

private theorem tripleLeafChoice_product_eq
    {n : ℕ} (x row chain dbl tri : ℝ) (χ : Fin n → Fin 4) :
    (∏ p : Fin n,
      match χ p with
      | ⟨0, _⟩ => tri
      | ⟨1, _⟩ => 3 * x * dbl
      | ⟨2, _⟩ => 3 * x ^ 2 * chain
      | ⟨3, _⟩ => x ^ 3 * row)
      = tripleLeafChoiceFunctionCoef x χ *
          (row ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
            chain ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
            dbl ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
            tri ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩) := by
  classical
  let coeff : Fin n → ℝ := fun p => tripleLeafChoiceCoef (χ p) x 1
  let value : Fin n → ℝ := fun p =>
    match χ p with
    | ⟨0, _⟩ => tri
    | ⟨1, _⟩ => dbl
    | ⟨2, _⟩ => chain
    | ⟨3, _⟩ => row
  calc
    (∏ p : Fin n,
      match χ p with
      | ⟨0, _⟩ => tri
      | ⟨1, _⟩ => 3 * x * dbl
      | ⟨2, _⟩ => 3 * x ^ 2 * chain
      | ⟨3, _⟩ => x ^ 3 * row)
        = ∏ p : Fin n, coeff p * value p := by
          refine Finset.prod_congr rfl ?_
          intro p _
          rcases hχ : χ p with ⟨v, hv⟩
          interval_cases v <;> simp [hχ, coeff, value, tripleLeafChoiceCoef]
    _ = (∏ p : Fin n, coeff p) * (∏ p : Fin n, value p) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ p : Fin n, coeff p) *
          (row ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
            chain ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
            dbl ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
            tri ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩) := by
          congr 1
          rw [tripleLeafChoice_value_product_eq]
    _ = tripleLeafChoiceFunctionCoef x χ *
          (row ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
            chain ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
            dbl ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
            tri ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩) := by
          congr 1

private theorem triple_leaf_kept_pow_expand
    (X R C D E : ℝ) (m : ℕ) :
    (X ^ 3 * R + 3 * X ^ 2 * C + 3 * X * D + E) ^ m
      = ∑ χ : Fin m → Fin 4,
          tripleLeafChoiceFunctionCoef X χ *
            (R ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
              C ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
              D ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
              E ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩) := by
  classical
  let f : Fin 4 → ℝ := fun r =>
    match r with
    | ⟨0, _⟩ => E
    | ⟨1, _⟩ => 3 * X * D
    | ⟨2, _⟩ => 3 * X ^ 2 * C
    | ⟨3, _⟩ => X ^ 3 * R
  have hsum : X ^ 3 * R + 3 * X ^ 2 * C + 3 * X * D + E
      = ∑ r : Fin 4, f r := by
    simp [Fin.sum_univ_four, f]
    ring
  rw [hsum, Fintype.sum_pow]
  refine Finset.sum_congr rfl ?_
  intro χ _
  rw [tripleLeafChoice_product_eq]

private theorem triple_leaf_root_stage_polynomial_expand
    (X Y R C D E : ℝ) (n : ℕ) :
    (Y + (X ^ 3 * R + 3 * X ^ 2 * C + 3 * X * D + E)) ^ n
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          Y ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef X χ *
                (R ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
                  C ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
                  D ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
                  E ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩)) := by
  classical
  rw [pow_add_eq_powerset Y (X ^ 3 * R + 3 * X ^ 2 * C + 3 * X * D + E) n]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S hS
  rw [triple_leaf_kept_pow_expand]

private theorem weighted_triple_leaf_stage_sum_expand
    {t : ℕ} (w row chain dbl tri : Fin t → ℝ) (X Y : ℝ) (n : ℕ) :
    (∑ i : Fin t, w i *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        Y ^ S.card *
          (∑ χ : Fin (n - S.card) → Fin 4,
            tripleLeafChoiceFunctionCoef X χ *
              (row i ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
                chain i ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
                dbl i ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
                tri i ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩))))
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          Y ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef X χ *
                (∑ i : Fin t, w i *
                  (row i ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
                    chain i ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
                    dbl i ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
                    tri i ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩))) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro S hS
  rw [Finset.sum_comm]
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro χ hχ
  refine Finset.sum_congr (M := ℝ) rfl ?_
  intro i hi
  ring

/-- Per-stage `convAt` value for a root with `n` identical triple-leaf
children. -/
private theorem convAt_node_replicate_triple_leaf_at_i_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (n : ℕ)
    (i : Fin t) :
    ButcherProduct.convAt t₂ coef
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i
      = (coef (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) +
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) j) ^ n := by
  classical
  rw [ButcherProduct.convAt_node]
  have hprod_add :
      (∑ S : Finset
          (Fin (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).length),
          (∏ p ∈ S,
            coef ((List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).get p)) *
            (∏ p ∈ Sᶜ,
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  ((List.replicate n
                    (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).get p) j))
        = ∏ p : Fin (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).length,
            (coef ((List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).get p) +
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  ((List.replicate n
                    (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).get p) j) := by
    rw [Finset.prod_add (s := Finset.univ)
        (f := fun p =>
          coef ((List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).get p))
        (g := fun p =>
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef
              ((List.replicate n
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).get p) j)]
    rw [Finset.powerset_univ]
    refine Finset.sum_congr rfl ?_
    intro S _
    rw [(Finset.compl_eq_univ_sdiff S).symm]
  rw [hprod_add]
  have hsame :
      ∀ p : Fin (List.replicate n
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).length,
        (coef ((List.replicate n
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).get p) +
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef
              ((List.replicate n
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])).get p) j)
          = coef (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) +
              ∑ j : Fin t, t₂.A i j *
                ButcherProduct.convAt t₂ coef
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) j := by
    intro p
    simp
  rw [Finset.prod_congr rfl (fun p _ => hsame p)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp

private theorem bWeighted_kept_triple_leaf_summand_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    (∑ j : Fin t, t₂.A i j *
        ButcherProduct.convAt t₂ coef
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) j)
      =
        (coef BTree.leaf) ^ 3 * (∑ j : Fin t, t₂.A i j)
        + 3 * (coef BTree.leaf) ^ 2 *
            (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))
        + 3 * (coef BTree.leaf) *
            (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) ^ 2)
        + (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) ^ 3) := by
  let X : ℝ := coef BTree.leaf
  let row : Fin t → ℝ := fun j => ∑ k : Fin t, t₂.A j k
  calc
    (∑ j : Fin t, t₂.A i j *
        ButcherProduct.convAt t₂ coef
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) j)
        = ∑ j : Fin t, t₂.A i j * (X + row j) ^ 3 := by
          refine Finset.sum_congr rfl ?_
          intro j _
          congr 1
          have h :=
            convAt_node_mixed_leaf_singleton_leaf_at_i_eq
              t₂ coef 3 0 j
          simpa [X, row] using h
    _ = ∑ j : Fin t,
          ((X ^ 3 * t₂.A i j)
            + (3 * X ^ 2) * (t₂.A i j * row j)
            + (3 * X) * (t₂.A i j * row j ^ 2)
            + t₂.A i j * row j ^ 3) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
    _ = X ^ 3 * (∑ j : Fin t, t₂.A i j)
        + 3 * X ^ 2 * (∑ j : Fin t, t₂.A i j * row j)
        + 3 * X * (∑ j : Fin t, t₂.A i j * row j ^ 2)
        + ∑ j : Fin t, t₂.A i j * row j ^ 3 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum]

private theorem bWeighted_convAt_node_replicate_triple_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (n : ℕ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i)
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (coef (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef (coef BTree.leaf) χ *
                t₂.bSeries (tripleLeafChoiceTree χ)) := by
  classical
  let X : ℝ := coef BTree.leaf
  let Y : ℝ := coef (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
  let row : Fin t → ℝ := fun i => ∑ j : Fin t, t₂.A i j
  let chain : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  let dbl : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) ^ 2
  let tri : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) ^ 3
  have hbSeries : ∀ n : ℕ, ∀ χ : Fin n → Fin 4,
      t₂.bSeries (tripleLeafChoiceTree χ)
        = ∑ i : Fin t, t₂.b i *
            (row i ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
              chain i ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
              dbl i ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
              tri i ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩) := by
    intro m χ
    simp only [tripleLeafChoiceTree]
    rw [bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf]
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node
            (List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) i)
        = ∑ i : Fin t, t₂.b i *
            (Y + (X ^ 3 * row i + 3 * X ^ 2 * chain i +
              3 * X * dbl i + tri i)) ^ n := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i _
          rw [convAt_node_replicate_triple_leaf_at_i_eq]
          have hkeep := bWeighted_kept_triple_leaf_summand_eq t₂ coef i
          have hkeep' :
              (∑ j : Fin t, t₂.A i j *
                  ButcherProduct.convAt t₂ coef
                    (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) j)
                = X ^ 3 * row i + 3 * X ^ 2 * chain i +
                    3 * X * dbl i + tri i := by
            simpa [X, row, chain, dbl, tri] using hkeep
          rw [hkeep']
    _ = ∑ i : Fin t, t₂.b i *
          (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            Y ^ S.card *
              (∑ χ : Fin (n - S.card) → Fin 4,
                tripleLeafChoiceFunctionCoef X χ *
                  (row i ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
                    chain i ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
                    dbl i ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
                    tri i ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩))) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro i _
          rw [triple_leaf_root_stage_polynomial_expand]
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          Y ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef X χ *
                (∑ i : Fin t, t₂.b i *
                  (row i ^ tripleLeafRootChoiceCount χ ⟨3, by decide⟩ *
                    chain i ^ tripleLeafRootChoiceCount χ ⟨2, by decide⟩ *
                    dbl i ^ tripleLeafRootChoiceCount χ ⟨1, by decide⟩ *
                    tri i ^ tripleLeafRootChoiceCount χ ⟨0, by decide⟩))) := by
          rw [weighted_triple_leaf_stage_sum_expand]
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (coef (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef (coef BTree.leaf) χ *
                t₂.bSeries (tripleLeafChoiceTree χ)) := by
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro S hS
          simp only [X, Y]
          congr 1
          refine Finset.sum_congr (M := ℝ) rfl ?_
          intro χ _
          congr 1
          rw [← hbSeries (n - S.card) χ]

/-- §384 honest convolution closed form on the all-triple-leaf family
`BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf,
BTree.leaf]))`. -/
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
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef (t₁.bSeries BTree.leaf) χ *
                t₂.bSeries (tripleLeafChoiceTree χ)) := by
  unfold ButcherProduct.bConv
  rw [bWeighted_convAt_node_replicate_triple_leaf_eq]

/-- §384 `bSeries` closed form on the all-triple-leaf family. -/
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
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 4,
              tripleLeafChoiceFunctionCoef (t₁.bSeries BTree.leaf) χ *
                t₂.bSeries (tripleLeafChoiceTree χ)) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_replicate_triple_leaf_eq]

/-! ### §384 standalone all-double-leaf parametric family

Cycle 562 specializes the cycle 552/553 mixed leaf+double-leaf machinery
to the pure all-double-leaf family `BTree.node (List.replicate n
(BTree.node [BTree.leaf, BTree.leaf]))` (i.e. `a = 0`). Each kept root
child contributes a `Fin 3` cut/keep choice via `doubleLeafChoiceCoef`. -/

/-- §384 honest convolution closed form on the all-double-leaf family
`BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf]))`. -/
theorem ButcherProduct.bSeries_node_replicate_double_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries (BTree.node [BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 3,
              doubleLeafChoiceCoef (t₁.bSeries BTree.leaf) χ *
                t₂.bSeries (doubleLeafChoiceTree 0 χ)) := by
  have h := ButcherProduct.bSeries_node_mixed_leaf_double_leaf_cut_eq t₁ t₂ 0 n
  simp only [List.replicate_zero, List.nil_append] at h
  rw [h]
  congr 1
  -- The outer sum over `(Finset.univ : Finset (Fin 0)).powerset` has only
  -- one element `∅`, so it collapses to its single summand.
  have hpow_empty :
      ((Finset.univ : Finset (Fin 0)).powerset : Finset (Finset (Fin 0)))
        = {∅} := by
    rw [show (Finset.univ : Finset (Fin 0)) = ∅ from rfl]
    simp
  rw [hpow_empty, Finset.sum_singleton]
  simp [Finset.card_empty]

/-- §384 `bConv` closed form on the all-double-leaf family. -/
theorem ButcherProduct.bConv_node_replicate_double_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    ButcherProduct.bConv (t₁.bSeries) t₂
        (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf])))
      = t₁.bSeries
          (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries (BTree.node [BTree.leaf, BTree.leaf])) ^ S.card *
            (∑ χ : Fin (n - S.card) → Fin 3,
              doubleLeafChoiceCoef (t₁.bSeries BTree.leaf) χ *
                t₂.bSeries (doubleLeafChoiceTree 0 χ)) := by
  rw [← ButcherProduct.bSeries_eq_bConv]
  exact ButcherProduct.bSeries_node_replicate_double_leaf_eq t₁ t₂ n


end ButcherTableau
