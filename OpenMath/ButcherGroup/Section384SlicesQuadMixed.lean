import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section384
import OpenMath.ButcherGroup.Section384Slices
import OpenMath.ButcherGroup.Section384SlicesMixed

open Finset

namespace ButcherTableau

variable {s : ℕ}

/-! ### §384 standalone four-child mixed leaf/singleton-leaf slice

Cycle 559 handles the concrete tree with three leaf children and one
singleton-leaf child. The root-level leaf choices are grouped by the cycle
557 `Fin 4` triple-leaf cut count, and the singleton-leaf child contributes
one of three states: root cut, kept with inner cut, or kept with inner kept.
-/

/-- The standalone cycle 559 mixed tree:
three leaves and one singleton-leaf child. -/
def tQuadMixed : BTree :=
  BTree.node [BTree.leaf, BTree.leaf, BTree.leaf, BTree.node [BTree.leaf]]

/-- Extra kept leaf children contributed by the singleton-leaf choice. -/
def quadMixedSingletonLeafCount (h : Fin 3) : ℕ :=
  match h with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

/-- Extra kept singleton-leaf children contributed by the singleton choice. -/
def quadMixedSingletonNodeCount (h : Fin 3) : ℕ :=
  match h with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

/-- Coefficient side of the singleton-leaf child after the stage sum has
been folded into a `t₂.bSeries` value. -/
noncomputable def quadMixedSingletonChoiceCoef (h : Fin 3) (X Y : ℝ) : ℝ :=
  match h with
  | ⟨0, _⟩ => Y
  | ⟨1, _⟩ => X
  | ⟨2, _⟩ => 1

/-- Per-stage singleton-leaf contribution: root cut, kept with inner cut,
or kept with inner kept. -/
noncomputable def quadMixedSingletonStageChoiceCoef
    (h : Fin 3) (X Y R C : ℝ) : ℝ :=
  match h with
  | ⟨0, _⟩ => Y
  | ⟨1, _⟩ => X * R
  | ⟨2, _⟩ => C

/-- The `t₂` tree produced by a triple-leaf root cut-count and a
singleton-leaf root/internal choice. -/
def quadMixedChoiceTree (k : Fin 4) (h : Fin 3) : BTree :=
  BTree.node
    (List.replicate
        (tripleLeafChoiceCount k + quadMixedSingletonLeafCount h) BTree.leaf ++
      List.replicate (quadMixedSingletonNodeCount h)
        (BTree.node [BTree.leaf]))

/-- The three singleton-leaf states expand the singleton factor
`Y + X * R + C`. -/
theorem quad_mixed_singleton_stage_expand (X Y R C : ℝ) :
    Y + (X * R + C)
      = ∑ h : Fin 3, quadMixedSingletonStageChoiceCoef h X Y R C := by
  simp [Fin.sum_univ_three, quadMixedSingletonStageChoiceCoef]
  ring

/-- Grouped per-stage polynomial expansion for the four-child mixed tree. -/
theorem quad_mixed_stage_polynomial_expand (X Y R C : ℝ) :
    (X + R) ^ 3 * (Y + (X * R + C))
      = ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k X R *
            quadMixedSingletonStageChoiceCoef h X Y R C := by
  rw [triple_leaf_stage_polynomial_expand,
      quad_mixed_singleton_stage_expand]
  simp_rw [Finset.sum_mul, Finset.mul_sum]

/-- Per-stage `convAt` closed form on the standalone four-child mixed tree. -/
theorem ButcherProduct.convAt_node_quadMixed_at_i_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.convAt t₂ coef tQuadMixed i
      = ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k (coef BTree.leaf)
            (∑ j : Fin t, t₂.A i j) *
            quadMixedSingletonStageChoiceCoef h (coef BTree.leaf)
              (coef (BTree.node [BTree.leaf]))
              (∑ j : Fin t, t₂.A i j)
              (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) := by
  let X : ℝ := coef BTree.leaf
  let Y : ℝ := coef (BTree.node [BTree.leaf])
  let row : ℝ := ∑ j : Fin t, t₂.A i j
  let chain : ℝ := ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  calc
    ButcherProduct.convAt t₂ coef tQuadMixed i
        = (X + row) ^ 3 * (Y + (X * row + chain)) := by
          have h :=
            convAt_node_mixed_leaf_singleton_leaf_at_i_eq
              t₂ coef 3 1 i
          simpa [tQuadMixed, X, Y, row, chain] using h
    _ = ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k X row *
            quadMixedSingletonStageChoiceCoef h X Y row chain := by
          rw [quad_mixed_stage_polynomial_expand]
    _ = ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k (coef BTree.leaf)
            (∑ j : Fin t, t₂.A i j) *
            quadMixedSingletonStageChoiceCoef h (coef BTree.leaf)
              (coef (BTree.node [BTree.leaf]))
              (∑ j : Fin t, t₂.A i j)
              (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) := by
          simp [X, Y, row, chain]

/-- The `b`-weighted second-tableau contribution on the standalone
four-child mixed tree, grouped by the triple-leaf cut count and the three
singleton-leaf child states. -/
theorem ButcherProduct.bWeighted_convAt_node_quadMixed_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef tQuadMixed i)
      = ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k (coef BTree.leaf) 1 *
            quadMixedSingletonChoiceCoef h (coef BTree.leaf)
              (coef (BTree.node [BTree.leaf])) *
            t₂.bSeries (quadMixedChoiceTree k h) := by
  classical
  let X : ℝ := coef BTree.leaf
  let Y : ℝ := coef (BTree.node [BTree.leaf])
  let row : Fin t → ℝ := fun i => ∑ j : Fin t, t₂.A i j
  let chain : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  have hbSeries : ∀ k : Fin 4, ∀ h : Fin 3,
      t₂.bSeries (quadMixedChoiceTree k h)
        = ∑ i : Fin t, t₂.b i *
            (row i ^ (tripleLeafChoiceCount k + quadMixedSingletonLeafCount h) *
              chain i ^ quadMixedSingletonNodeCount h) := by
    intro k h
    rw [quadMixedChoiceTree,
      bSeries_node_replicate_leaf_append_replicate_singleton_leaf]
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef tQuadMixed i)
        = ∑ i : Fin t, t₂.b i *
            (∑ k : Fin 4, ∑ h : Fin 3,
              tripleLeafChoiceCoef k X (row i) *
                quadMixedSingletonStageChoiceCoef h X Y (row i) (chain i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          congr 1
          rw [ButcherProduct.convAt_node_quadMixed_at_i_eq]
    _ = ∑ k : Fin 4, ∑ h : Fin 3,
          ∑ i : Fin t, t₂.b i *
            (tripleLeafChoiceCoef k X (row i) *
              quadMixedSingletonStageChoiceCoef h X Y (row i) (chain i)) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.sum_comm]
    _ = ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k X 1 *
            quadMixedSingletonChoiceCoef h X Y *
            t₂.bSeries (quadMixedChoiceTree k h) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro h _
          rw [hbSeries k h]
          fin_cases k <;> fin_cases h <;>
            simp [tripleLeafChoiceCoef, tripleLeafChoiceCount,
              quadMixedSingletonChoiceCoef, quadMixedSingletonStageChoiceCoef,
              quadMixedSingletonLeafCount, quadMixedSingletonNodeCount]
          all_goals
            try rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
    _ = ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k (coef BTree.leaf) 1 *
            quadMixedSingletonChoiceCoef h (coef BTree.leaf)
              (coef (BTree.node [BTree.leaf])) *
            t₂.bSeries (quadMixedChoiceTree k h) := by
          simp [X, Y]

/-- §384 honest convolution closed form on the standalone four-child mixed
tree, grouped as `Fin 4 × Fin 3`. -/
theorem ButcherProduct.bConv_node_quadMixed_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherProduct.bConv (t₁.bSeries) t₂ tQuadMixed
      = t₁.bSeries tQuadMixed
        + ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k (t₁.bSeries BTree.leaf) 1 *
            quadMixedSingletonChoiceCoef h (t₁.bSeries BTree.leaf)
              (t₁.bSeries (BTree.node [BTree.leaf])) *
            t₂.bSeries (quadMixedChoiceTree k h) := by
  unfold ButcherProduct.bConv
  rw [ButcherProduct.bWeighted_convAt_node_quadMixed_eq]

/-- Headline §384 product `bSeries` closed form on the standalone
four-child mixed tree. -/
theorem ButcherProduct.bSeries_node_quadMixed_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries tQuadMixed
      = t₁.bSeries tQuadMixed
        + ∑ k : Fin 4, ∑ h : Fin 3,
          tripleLeafChoiceCoef k (t₁.bSeries BTree.leaf) 1 *
            quadMixedSingletonChoiceCoef h (t₁.bSeries BTree.leaf)
              (t₁.bSeries (BTree.node [BTree.leaf])) *
            t₂.bSeries (quadMixedChoiceTree k h) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_quadMixed_eq]

/-! ### §384 standalone four-child mixed (2-leaf, 2-singleton-leaf) slice

Cycle 560 successor of cycle 559. The root has two pure leaves and two
singleton-leaf children. The root-level leaf choices are grouped by a
`Fin 3` cut count (the binomial expansion of `(X + R)^2`); each
singleton-leaf contributes one of three states (root cut, kept inner cut,
kept inner kept), so the singleton-leaf side is indexed by
`Fin 3 × Fin 3`. -/

/-- The standalone cycle 560 mixed tree:
two leaves and two singleton-leaf children. -/
def tQuadMixedTwoTwo : BTree :=
  BTree.node
    [BTree.leaf, BTree.leaf, BTree.node [BTree.leaf], BTree.node [BTree.leaf]]

/-- Pair-leaf cut count in `Fin 3`. The index records how many leaves are
cut, so the keep count is `2, 1, 0`. -/
def quadMixedTwoTwoLeafChoiceCount (k : Fin 3) : ℕ :=
  match k with
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

/-- Binomial coefficient package for the three cut-count cases in
`(X + R)^2`. -/
noncomputable def quadMixedTwoTwoLeafChoiceCoef (k : Fin 3) (X R : ℝ) : ℝ :=
  match k with
  | ⟨0, _⟩ => R ^ 2
  | ⟨1, _⟩ => 2 * X * R
  | ⟨2, _⟩ => X ^ 2

/-- Cut count plus keep count is the two leaf children. -/
theorem quadMixedTwoTwoLeafChoiceCount_sum (k : Fin 3) :
    k.1 + quadMixedTwoTwoLeafChoiceCount k = 2 := by
  fin_cases k <;> rfl

/-- Grouped binomial expansion for the two identical leaf children. -/
theorem quad_mixed_two_two_leaf_stage_polynomial_expand (X R : ℝ) :
    (X + R) ^ 2 = ∑ k : Fin 3, quadMixedTwoTwoLeafChoiceCoef k X R := by
  simp [Fin.sum_univ_three, quadMixedTwoTwoLeafChoiceCoef]
  ring

/-- Coefficient side of the singleton-leaf child after the stage sum has
been folded into a `t₂.bSeries` value. Re-uses cycle 559's helper
shape. -/
noncomputable def quadMixedTwoTwoSingletonChoiceCoef
    (h : Fin 3) (X Y : ℝ) : ℝ :=
  quadMixedSingletonChoiceCoef h X Y

/-- Per-stage singleton-leaf contribution: root cut, kept with inner cut,
or kept with inner kept. Re-uses cycle 559's helper shape. -/
noncomputable def quadMixedTwoTwoSingletonStageChoiceCoef
    (h : Fin 3) (X Y R C : ℝ) : ℝ :=
  quadMixedSingletonStageChoiceCoef h X Y R C

/-- The `t₂` tree produced by a leaf cut-count and a pair of singleton-leaf
state choices. -/
def quadMixedTwoTwoChoiceTree (k : Fin 3) (h₁ h₂ : Fin 3) : BTree :=
  BTree.node
    (List.replicate
        (quadMixedTwoTwoLeafChoiceCount k +
          quadMixedSingletonLeafCount h₁ + quadMixedSingletonLeafCount h₂)
        BTree.leaf ++
      List.replicate
        (quadMixedSingletonNodeCount h₁ + quadMixedSingletonNodeCount h₂)
        (BTree.node [BTree.leaf]))

/-- The two singleton-leaf children expand the singleton factor squared
into a double sum. -/
theorem quad_mixed_two_two_singleton_stage_expand (X Y R C : ℝ) :
    (Y + (X * R + C)) ^ 2
      = ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoSingletonStageChoiceCoef h₁ X Y R C *
            quadMixedTwoTwoSingletonStageChoiceCoef h₂ X Y R C := by
  have h := quad_mixed_singleton_stage_expand X Y R C
  rw [show (Y + (X * R + C)) ^ 2
        = (Y + (X * R + C)) * (Y + (X * R + C)) from sq _]
  rw [h]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro h₁ _
  refine Finset.sum_congr rfl ?_
  intro h₂ _
  rfl

/-- Grouped per-stage polynomial expansion for the (2-leaf, 2-singleton)
mixed tree. -/
theorem quad_mixed_two_two_stage_polynomial_expand (X Y R C : ℝ) :
    (X + R) ^ 2 * (Y + (X * R + C)) ^ 2
      = ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k X R *
            (quadMixedTwoTwoSingletonStageChoiceCoef h₁ X Y R C *
              quadMixedTwoTwoSingletonStageChoiceCoef h₂ X Y R C) := by
  rw [quad_mixed_two_two_leaf_stage_polynomial_expand,
      quad_mixed_two_two_singleton_stage_expand]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro h₁ _
  rw [Finset.mul_sum]

/-- Per-stage `convAt` closed form on the standalone (2-leaf, 2-singleton)
mixed tree. -/
theorem ButcherProduct.convAt_node_quadMixedTwoTwo_at_i_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.convAt t₂ coef tQuadMixedTwoTwo i
      = ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k (coef BTree.leaf)
            (∑ j : Fin t, t₂.A i j) *
            (quadMixedTwoTwoSingletonStageChoiceCoef h₁ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf]))
                (∑ j : Fin t, t₂.A i j)
                (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) *
              quadMixedTwoTwoSingletonStageChoiceCoef h₂ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf]))
                (∑ j : Fin t, t₂.A i j)
                (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) := by
  let X : ℝ := coef BTree.leaf
  let Y : ℝ := coef (BTree.node [BTree.leaf])
  let row : ℝ := ∑ j : Fin t, t₂.A i j
  let chain : ℝ := ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  calc
    ButcherProduct.convAt t₂ coef tQuadMixedTwoTwo i
        = (X + row) ^ 2 * (Y + (X * row + chain)) ^ 2 := by
          have h :=
            convAt_node_mixed_leaf_singleton_leaf_at_i_eq
              t₂ coef 2 2 i
          simpa [tQuadMixedTwoTwo, X, Y, row, chain] using h
    _ = ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k X row *
            (quadMixedTwoTwoSingletonStageChoiceCoef h₁ X Y row chain *
              quadMixedTwoTwoSingletonStageChoiceCoef h₂ X Y row chain) := by
          rw [quad_mixed_two_two_stage_polynomial_expand]
    _ = ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k (coef BTree.leaf)
            (∑ j : Fin t, t₂.A i j) *
            (quadMixedTwoTwoSingletonStageChoiceCoef h₁ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf]))
                (∑ j : Fin t, t₂.A i j)
                (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) *
              quadMixedTwoTwoSingletonStageChoiceCoef h₂ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf]))
                (∑ j : Fin t, t₂.A i j)
                (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k))) := by
          simp [X, Y, row, chain]

/-- The `b`-weighted second-tableau contribution on the standalone
(2-leaf, 2-singleton) mixed tree, grouped by leaf cut count and the two
singleton-leaf state choices. -/
theorem ButcherProduct.bWeighted_convAt_node_quadMixedTwoTwo_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef tQuadMixedTwoTwo i)
      = ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k (coef BTree.leaf) 1 *
            (quadMixedTwoTwoSingletonChoiceCoef h₁ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf])) *
              quadMixedTwoTwoSingletonChoiceCoef h₂ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf]))) *
            t₂.bSeries (quadMixedTwoTwoChoiceTree k h₁ h₂) := by
  classical
  let X : ℝ := coef BTree.leaf
  let Y : ℝ := coef (BTree.node [BTree.leaf])
  let row : Fin t → ℝ := fun i => ∑ j : Fin t, t₂.A i j
  let chain : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  have hbSeries : ∀ k : Fin 3, ∀ h₁ h₂ : Fin 3,
      t₂.bSeries (quadMixedTwoTwoChoiceTree k h₁ h₂)
        = ∑ i : Fin t, t₂.b i *
            (row i ^ (quadMixedTwoTwoLeafChoiceCount k +
                quadMixedSingletonLeafCount h₁ +
                quadMixedSingletonLeafCount h₂) *
              chain i ^ (quadMixedSingletonNodeCount h₁ +
                quadMixedSingletonNodeCount h₂)) := by
    intro k h₁ h₂
    rw [quadMixedTwoTwoChoiceTree,
      bSeries_node_replicate_leaf_append_replicate_singleton_leaf]
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef tQuadMixedTwoTwo i)
        = ∑ i : Fin t, t₂.b i *
            (∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
              quadMixedTwoTwoLeafChoiceCoef k X (row i) *
                (quadMixedTwoTwoSingletonStageChoiceCoef h₁ X Y (row i) (chain i) *
                  quadMixedTwoTwoSingletonStageChoiceCoef h₂ X Y (row i) (chain i))) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          congr 1
          rw [ButcherProduct.convAt_node_quadMixedTwoTwo_at_i_eq]
    _ = ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          ∑ i : Fin t, t₂.b i *
            (quadMixedTwoTwoLeafChoiceCoef k X (row i) *
              (quadMixedTwoTwoSingletonStageChoiceCoef h₁ X Y (row i) (chain i) *
                quadMixedTwoTwoSingletonStageChoiceCoef h₂ X Y (row i) (chain i))) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro h₁ _
          rw [Finset.sum_comm]
    _ = ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k X 1 *
            (quadMixedTwoTwoSingletonChoiceCoef h₁ X Y *
              quadMixedTwoTwoSingletonChoiceCoef h₂ X Y) *
            t₂.bSeries (quadMixedTwoTwoChoiceTree k h₁ h₂) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro h₁ _
          refine Finset.sum_congr rfl ?_
          intro h₂ _
          rw [hbSeries k h₁ h₂]
          fin_cases k <;> fin_cases h₁ <;> fin_cases h₂ <;>
            simp [quadMixedTwoTwoLeafChoiceCoef,
              quadMixedTwoTwoLeafChoiceCount,
              quadMixedTwoTwoSingletonChoiceCoef,
              quadMixedTwoTwoSingletonStageChoiceCoef,
              quadMixedSingletonChoiceCoef,
              quadMixedSingletonStageChoiceCoef,
              quadMixedSingletonLeafCount,
              quadMixedSingletonNodeCount] <;>
          first
          | (rw [Finset.mul_sum]
             refine Finset.sum_congr rfl ?_
             intro i _
             ring)
          | (refine Finset.sum_congr rfl ?_
             intro i _
             ring)
    _ = ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k (coef BTree.leaf) 1 *
            (quadMixedTwoTwoSingletonChoiceCoef h₁ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf])) *
              quadMixedTwoTwoSingletonChoiceCoef h₂ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf]))) *
            t₂.bSeries (quadMixedTwoTwoChoiceTree k h₁ h₂) := by
          simp [X, Y]

/-- §384 honest convolution closed form on the standalone (2-leaf,
2-singleton) mixed tree, grouped as `Fin 3 × Fin 3 × Fin 3`. -/
theorem ButcherProduct.bConv_node_quadMixedTwoTwo_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherProduct.bConv (t₁.bSeries) t₂ tQuadMixedTwoTwo
      = t₁.bSeries tQuadMixedTwoTwo
        + ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k (t₁.bSeries BTree.leaf) 1 *
            (quadMixedTwoTwoSingletonChoiceCoef h₁ (t₁.bSeries BTree.leaf)
                (t₁.bSeries (BTree.node [BTree.leaf])) *
              quadMixedTwoTwoSingletonChoiceCoef h₂ (t₁.bSeries BTree.leaf)
                (t₁.bSeries (BTree.node [BTree.leaf]))) *
            t₂.bSeries (quadMixedTwoTwoChoiceTree k h₁ h₂) := by
  unfold ButcherProduct.bConv
  rw [ButcherProduct.bWeighted_convAt_node_quadMixedTwoTwo_eq]

/-- Headline §384 product `bSeries` closed form on the standalone
(2-leaf, 2-singleton) mixed tree. -/
theorem ButcherProduct.bSeries_node_quadMixedTwoTwo_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries tQuadMixedTwoTwo
      = t₁.bSeries tQuadMixedTwoTwo
        + ∑ k : Fin 3, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3,
          quadMixedTwoTwoLeafChoiceCoef k (t₁.bSeries BTree.leaf) 1 *
            (quadMixedTwoTwoSingletonChoiceCoef h₁ (t₁.bSeries BTree.leaf)
                (t₁.bSeries (BTree.node [BTree.leaf])) *
              quadMixedTwoTwoSingletonChoiceCoef h₂ (t₁.bSeries BTree.leaf)
                (t₁.bSeries (BTree.node [BTree.leaf]))) *
            t₂.bSeries (quadMixedTwoTwoChoiceTree k h₁ h₂) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_quadMixedTwoTwo_eq]

/-! ### §384 standalone four-child mixed (1-leaf, 3-singleton-leaf) slice

Cycle 561 successor of cycle 560. The root has one pure leaf and three
singleton-leaf children. The root-level leaf choice is grouped by the
`Fin 2` binomial expansion of `(X + R)`; each singleton-leaf child reuses
the cycle 559 three-state choice. -/

/-- The standalone cycle 561 mixed tree:
one leaf and three singleton-leaf children. -/
def tQuadMixedOneThree : BTree :=
  BTree.node
    [BTree.leaf, BTree.node [BTree.leaf], BTree.node [BTree.leaf],
      BTree.node [BTree.leaf]]

/-- Single-leaf keep count in `Fin 2`. The index records the root cut count,
so the keep count is `1, 0`. -/
def quadMixedOneThreeLeafChoiceCount (k : Fin 2) : ℕ :=
  match k with
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0

/-- Binomial coefficient package for the two cases in `(X + R)`. -/
noncomputable def quadMixedOneThreeLeafChoiceCoef
    (k : Fin 2) (X R : ℝ) : ℝ :=
  match k with
  | ⟨0, _⟩ => R
  | ⟨1, _⟩ => X

/-- Cut count plus keep count is the one leaf child. -/
theorem quadMixedOneThreeLeafChoiceCount_sum (k : Fin 2) :
    k.1 + quadMixedOneThreeLeafChoiceCount k = 1 := by
  fin_cases k <;> rfl

/-- Grouped binomial expansion for the single leaf child. -/
theorem quad_mixed_one_three_leaf_stage_polynomial_expand (X R : ℝ) :
    X + R = ∑ k : Fin 2, quadMixedOneThreeLeafChoiceCoef k X R := by
  simp [Fin.sum_univ_two, quadMixedOneThreeLeafChoiceCoef]
  ring

/-- The `t₂` tree produced by a leaf choice and three singleton-leaf state
choices. -/
def quadMixedOneThreeChoiceTree (k : Fin 2) (h₁ h₂ h₃ : Fin 3) : BTree :=
  BTree.node
    (List.replicate
        (quadMixedOneThreeLeafChoiceCount k +
          quadMixedSingletonLeafCount h₁ + quadMixedSingletonLeafCount h₂ +
            quadMixedSingletonLeafCount h₃)
        BTree.leaf ++
      List.replicate
        (quadMixedSingletonNodeCount h₁ + quadMixedSingletonNodeCount h₂ +
          quadMixedSingletonNodeCount h₃)
        (BTree.node [BTree.leaf]))

/-- The three singleton-leaf children expand the singleton factor cubed
into a triple sum. -/
theorem quad_mixed_one_three_singleton_stage_expand (X Y R C : ℝ) :
    (Y + (X * R + C)) ^ 3
      = ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedSingletonStageChoiceCoef h₁ X Y R C *
            (quadMixedSingletonStageChoiceCoef h₂ X Y R C *
              quadMixedSingletonStageChoiceCoef h₃ X Y R C) := by
  have h := quad_mixed_singleton_stage_expand X Y R C
  rw [show (Y + (X * R + C)) ^ 3
        = (Y + (X * R + C)) *
          ((Y + (X * R + C)) * (Y + (X * R + C))) by ring]
  rw [h]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro h₁ _
  rw [Finset.sum_mul_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro h₂ _
  rw [Finset.mul_sum]

/-- Grouped per-stage polynomial expansion for the (1-leaf, 3-singleton)
mixed tree. -/
theorem quad_mixed_one_three_stage_polynomial_expand (X Y R C : ℝ) :
    (X + R) * (Y + (X * R + C)) ^ 3
      = ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k X R *
            (quadMixedSingletonStageChoiceCoef h₁ X Y R C *
              (quadMixedSingletonStageChoiceCoef h₂ X Y R C *
                quadMixedSingletonStageChoiceCoef h₃ X Y R C)) := by
  rw [quad_mixed_one_three_leaf_stage_polynomial_expand,
      quad_mixed_one_three_singleton_stage_expand]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro h₁ _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro h₂ _
  rw [Finset.mul_sum]

/-- Per-stage `convAt` closed form on the standalone (1-leaf, 3-singleton)
mixed tree. -/
theorem ButcherProduct.convAt_node_quadMixedOneThree_at_i_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.convAt t₂ coef tQuadMixedOneThree i
      = ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k (coef BTree.leaf)
            (∑ j : Fin t, t₂.A i j) *
            (quadMixedSingletonStageChoiceCoef h₁ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf]))
                (∑ j : Fin t, t₂.A i j)
                (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) *
              (quadMixedSingletonStageChoiceCoef h₂ (coef BTree.leaf)
                  (coef (BTree.node [BTree.leaf]))
                  (∑ j : Fin t, t₂.A i j)
                  (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) *
                quadMixedSingletonStageChoiceCoef h₃ (coef BTree.leaf)
                  (coef (BTree.node [BTree.leaf]))
                  (∑ j : Fin t, t₂.A i j)
                  (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)))) := by
  let X : ℝ := coef BTree.leaf
  let Y : ℝ := coef (BTree.node [BTree.leaf])
  let row : ℝ := ∑ j : Fin t, t₂.A i j
  let chain : ℝ := ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  calc
    ButcherProduct.convAt t₂ coef tQuadMixedOneThree i
        = (X + row) * (Y + (X * row + chain)) ^ 3 := by
          have h :=
            convAt_node_mixed_leaf_singleton_leaf_at_i_eq
              t₂ coef 1 3 i
          simpa [tQuadMixedOneThree, X, Y, row, chain] using h
    _ = ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k X row *
            (quadMixedSingletonStageChoiceCoef h₁ X Y row chain *
              (quadMixedSingletonStageChoiceCoef h₂ X Y row chain *
                quadMixedSingletonStageChoiceCoef h₃ X Y row chain)) := by
          rw [quad_mixed_one_three_stage_polynomial_expand]
    _ = ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k (coef BTree.leaf)
            (∑ j : Fin t, t₂.A i j) *
            (quadMixedSingletonStageChoiceCoef h₁ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf]))
                (∑ j : Fin t, t₂.A i j)
                (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) *
              (quadMixedSingletonStageChoiceCoef h₂ (coef BTree.leaf)
                  (coef (BTree.node [BTree.leaf]))
                  (∑ j : Fin t, t₂.A i j)
                  (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)) *
                quadMixedSingletonStageChoiceCoef h₃ (coef BTree.leaf)
                  (coef (BTree.node [BTree.leaf]))
                  (∑ j : Fin t, t₂.A i j)
                  (∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)))) := by
          simp [X, Y, row, chain]

/-- The `b`-weighted second-tableau contribution on the standalone
(1-leaf, 3-singleton) mixed tree, grouped by the leaf choice and the three
singleton-leaf state choices. -/
theorem ButcherProduct.bWeighted_convAt_node_quadMixedOneThree_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef tQuadMixedOneThree i)
      = ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k (coef BTree.leaf) 1 *
            (quadMixedSingletonChoiceCoef h₁ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf])) *
              (quadMixedSingletonChoiceCoef h₂ (coef BTree.leaf)
                  (coef (BTree.node [BTree.leaf])) *
                quadMixedSingletonChoiceCoef h₃ (coef BTree.leaf)
                  (coef (BTree.node [BTree.leaf])))) *
            t₂.bSeries (quadMixedOneThreeChoiceTree k h₁ h₂ h₃) := by
  classical
  let X : ℝ := coef BTree.leaf
  let Y : ℝ := coef (BTree.node [BTree.leaf])
  let row : Fin t → ℝ := fun i => ∑ j : Fin t, t₂.A i j
  let chain : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  have hbSeries : ∀ k : Fin 2, ∀ h₁ h₂ h₃ : Fin 3,
      t₂.bSeries (quadMixedOneThreeChoiceTree k h₁ h₂ h₃)
        = ∑ i : Fin t, t₂.b i *
            (row i ^ (quadMixedOneThreeLeafChoiceCount k +
                quadMixedSingletonLeafCount h₁ +
                quadMixedSingletonLeafCount h₂ +
                quadMixedSingletonLeafCount h₃) *
              chain i ^ (quadMixedSingletonNodeCount h₁ +
                quadMixedSingletonNodeCount h₂ +
                quadMixedSingletonNodeCount h₃)) := by
    intro k h₁ h₂ h₃
    rw [quadMixedOneThreeChoiceTree,
      bSeries_node_replicate_leaf_append_replicate_singleton_leaf]
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef tQuadMixedOneThree i)
        = ∑ i : Fin t, t₂.b i *
            (∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
              quadMixedOneThreeLeafChoiceCoef k X (row i) *
                (quadMixedSingletonStageChoiceCoef h₁ X Y (row i) (chain i) *
                  (quadMixedSingletonStageChoiceCoef h₂ X Y (row i) (chain i) *
                    quadMixedSingletonStageChoiceCoef h₃ X Y (row i) (chain i)))) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          congr 1
          rw [ButcherProduct.convAt_node_quadMixedOneThree_at_i_eq]
    _ = ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          ∑ i : Fin t, t₂.b i *
            (quadMixedOneThreeLeafChoiceCoef k X (row i) *
              (quadMixedSingletonStageChoiceCoef h₁ X Y (row i) (chain i) *
                (quadMixedSingletonStageChoiceCoef h₂ X Y (row i) (chain i) *
                  quadMixedSingletonStageChoiceCoef h₃ X Y (row i) (chain i)))) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro h₁ _
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro h₂ _
          rw [Finset.sum_comm]
    _ = ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k X 1 *
            (quadMixedSingletonChoiceCoef h₁ X Y *
              (quadMixedSingletonChoiceCoef h₂ X Y *
                quadMixedSingletonChoiceCoef h₃ X Y)) *
            t₂.bSeries (quadMixedOneThreeChoiceTree k h₁ h₂ h₃) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro h₁ _
          refine Finset.sum_congr rfl ?_
          intro h₂ _
          refine Finset.sum_congr rfl ?_
          intro h₃ _
          rw [hbSeries k h₁ h₂ h₃]
          fin_cases k <;> fin_cases h₁ <;> fin_cases h₂ <;>
            fin_cases h₃ <;>
            simp [quadMixedOneThreeLeafChoiceCoef,
              quadMixedOneThreeLeafChoiceCount,
              quadMixedSingletonChoiceCoef,
              quadMixedSingletonStageChoiceCoef,
              quadMixedSingletonLeafCount,
              quadMixedSingletonNodeCount] <;>
          first
          | (rw [Finset.mul_sum]
             refine Finset.sum_congr rfl ?_
             intro i _
             ring)
          | (refine Finset.sum_congr rfl ?_
             intro i _
             ring)
    _ = ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k (coef BTree.leaf) 1 *
            (quadMixedSingletonChoiceCoef h₁ (coef BTree.leaf)
                (coef (BTree.node [BTree.leaf])) *
              (quadMixedSingletonChoiceCoef h₂ (coef BTree.leaf)
                  (coef (BTree.node [BTree.leaf])) *
                quadMixedSingletonChoiceCoef h₃ (coef BTree.leaf)
                  (coef (BTree.node [BTree.leaf])))) *
            t₂.bSeries (quadMixedOneThreeChoiceTree k h₁ h₂ h₃) := by
          simp [X, Y]

/-- §384 honest convolution closed form on the standalone (1-leaf,
3-singleton) mixed tree, grouped as `Fin 2 × Fin 3 × Fin 3 × Fin 3`. -/
theorem ButcherProduct.bConv_node_quadMixedOneThree_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherProduct.bConv (t₁.bSeries) t₂ tQuadMixedOneThree
      = t₁.bSeries tQuadMixedOneThree
        + ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k (t₁.bSeries BTree.leaf) 1 *
            (quadMixedSingletonChoiceCoef h₁ (t₁.bSeries BTree.leaf)
                (t₁.bSeries (BTree.node [BTree.leaf])) *
              (quadMixedSingletonChoiceCoef h₂ (t₁.bSeries BTree.leaf)
                  (t₁.bSeries (BTree.node [BTree.leaf])) *
                quadMixedSingletonChoiceCoef h₃ (t₁.bSeries BTree.leaf)
                  (t₁.bSeries (BTree.node [BTree.leaf])))) *
            t₂.bSeries (quadMixedOneThreeChoiceTree k h₁ h₂ h₃) := by
  unfold ButcherProduct.bConv
  rw [ButcherProduct.bWeighted_convAt_node_quadMixedOneThree_eq]

/-- Headline §384 product `bSeries` closed form on the standalone
(1-leaf, 3-singleton) mixed tree. -/
theorem ButcherProduct.bSeries_node_quadMixedOneThree_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries tQuadMixedOneThree
      = t₁.bSeries tQuadMixedOneThree
        + ∑ k : Fin 2, ∑ h₁ : Fin 3, ∑ h₂ : Fin 3, ∑ h₃ : Fin 3,
          quadMixedOneThreeLeafChoiceCoef k (t₁.bSeries BTree.leaf) 1 *
            (quadMixedSingletonChoiceCoef h₁ (t₁.bSeries BTree.leaf)
                (t₁.bSeries (BTree.node [BTree.leaf])) *
              (quadMixedSingletonChoiceCoef h₂ (t₁.bSeries BTree.leaf)
                  (t₁.bSeries (BTree.node [BTree.leaf])) *
                quadMixedSingletonChoiceCoef h₃ (t₁.bSeries BTree.leaf)
                  (t₁.bSeries (BTree.node [BTree.leaf])))) *
            t₂.bSeries (quadMixedOneThreeChoiceTree k h₁ h₂ h₃) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_quadMixedOneThree_eq]

end ButcherTableau
