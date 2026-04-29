import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section384

/-!
# §384 parametric closed-form bSeries product slices

Parametric closed-form `bConv` / `bSeries` decompositions of
`ButcherProduct` on specific tree shapes (all-leaves, all-node-nil,
mixed leaf+node-nil, all-singleton-leaf, mixed leaf+singleton-leaf,
trivial-children, etc.) used by the §38 `G1` slice well-definedness
theorems in `OpenMath/ButcherGroup.lean`.

Cycle 550 split this content out of `OpenMath/ButcherGroup/Section384.lean`
because the parent file crossed the 3000-line cap. The §384 honest
convolution layer (`bSeries`, `bConv`, `convAt`, `rightAuxAt`, the
`t₂`-permutation invariance lemmas) remains in `Section384.lean`. None
of the lemmas moved here is consumed by that core layer.
-/

open Finset

namespace ButcherTableau

variable {s : ℕ}

/-! ### §384 honest bSeries-only convolution: closed forms on the
b-weighted right block.

Cycle 538: the first concrete lemmas in the closed form
`∑ i, t₂.b i * convAt t₂ coef τ i` that mention `t₂` only through
`t₂.bSeries` values on subtrees of `τ`. -/

/-- Singleton-node closed form: the b-weighted right block at
`BTree.node [c]` splits into a `weightsSum`-scaled cut term on `coef c`
and a kept term that recurses one level into `convAt` at `c`. -/
theorem ButcherProduct.bWeighted_convAt_singleton_node_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (c : BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef (BTree.node [c]) i)
      = t₂.weightsSum * coef c
        + ∑ i : Fin t, t₂.b i *
            (∑ j : Fin t, t₂.A i j *
              ButcherProduct.convAt t₂ coef c j) := by
  have hLHS :
      (∑ i : Fin t, t₂.b i *
          ButcherProduct.convAt t₂ coef (BTree.node [c]) i)
        = ∑ i : Fin t, t₂.b i *
            ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [c]) i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  have hSing :
      (∑ i : Fin t, t₂.b i *
          ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [c]) i)
        = coef c * t₂.weightsSum +
          ∑ i : Fin t, t₂.b i *
            ∑ j : Fin t,
              t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef c j :=
    ButcherProduct.bWeighted_rightAuxAtCoef_node_singleton t₂ coef c
  have hKept :
      (∑ i : Fin t, t₂.b i *
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAtCoef t₂ coef c j)
        = ∑ i : Fin t, t₂.b i *
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef c j := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine congrArg _ ?_
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  rw [hLHS, hSing, hKept, mul_comm (coef c) t₂.weightsSum]

/-- Kept-leaf closed form: the inner kept term `∑ i, b i * (∑ j, A i j *
convAt t₂ coef leaf j)` collapses to `t₂.bSeries (node [leaf])`.
This is the smallest instance where the RHS mentions `t₂` only through
`t₂.bSeries` applied to a subtree built from leaves. -/
theorem ButcherProduct.bWeighted_convAt_kept_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        (∑ j : Fin t, t₂.A i j *
          ButcherProduct.convAt t₂ coef BTree.leaf j))
      = t₂.bSeries (BTree.node [BTree.leaf]) := by
  simp [ButcherTableau.bSeries, ButcherTableau.elementaryWeight_singleton,
        ButcherProduct.convAt_leaf]

/-- Helper: the elementary weight of a node whose children are `n` leaves
collapses to the `n`-th power of the row sum `∑ k, A i k`. -/
private theorem elementaryWeight_node_replicate_leaf
    {s : ℕ} (tab : ButcherTableau s) (n : ℕ) (i : Fin s) :
    tab.elementaryWeight (BTree.node (List.replicate n BTree.leaf)) i
      = (∑ k : Fin s, tab.A i k) ^ n := by
  induction n with
  | zero =>
    show tab.elementaryWeight (BTree.node []) i = _
    simp [ButcherTableau.elementaryWeight]
  | succ m ih =>
    rw [List.replicate_succ]
    have hfold :
        tab.elementaryWeight
            (BTree.node (BTree.leaf :: List.replicate m BTree.leaf)) i
          = tab.elementaryWeight (BTree.node (List.replicate m BTree.leaf)) i *
              (∑ k : Fin s, tab.A i k) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih, pow_succ]

/-- All-leaves trunk/cut closed form: when every child of the root is a
leaf, the b-weighted right block at `BTree.node children` decomposes
into a sum over cut subsets `S`, where each summand multiplies the cut
term `(∏ p ∈ S, coef BTree.leaf)` by the `bSeries` of a node of the
remaining leaves. The RHS mentions `t₂` only through `t₂.bSeries`
applied to leaf-only subtrees. -/
theorem ButcherProduct.bWeighted_convAt_node_all_leaves_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree)
    (hAll : ∀ c ∈ children, c = BTree.leaf) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ _p ∈ S, coef BTree.leaf) *
          t₂.bSeries
            (BTree.node
              (List.replicate (children.length - S.card) BTree.leaf)) := by
  classical
  have hLHS :
      (∑ i : Fin t, t₂.b i *
          ButcherProduct.convAt t₂ coef (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  rw [hLHS,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq
        t₂ t₂ coef children hAll]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  -- Goal: ∑ i, t₂.b i * ∏ _p ∈ Sᶜ, ∑ j, t₂.A i j
  --     = t₂.bSeries (node (replicate (children.length - S.card) leaf))
  have hcard : (Sᶜ : Finset (Fin children.length)).card
      = children.length - S.card := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin]
  have hbSeries :
      t₂.bSeries
          (BTree.node
            (List.replicate (children.length - S.card) BTree.leaf))
        = ∑ i : Fin t, t₂.b i *
            (∑ j : Fin t, t₂.A i j) ^ (children.length - S.card) := by
    unfold ButcherTableau.bSeries
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [elementaryWeight_node_replicate_leaf]
  rw [hbSeries]
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  rw [Finset.prod_const, hcard]

/-- Mixed kept-children closed form at the `convAt` level: in the
trunk-recursion expansion, cut children contribute `coef`, kept leaf
children contribute the row sum of `A`, and kept node children stay in the
recursive `convAt` form. This is the `convAt` analogue of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq` with the
node case left in the closed recursive auxiliary instead of re-expanding the
inner powerset. -/
theorem ButcherProduct.bWeighted_convAt_node_kept_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       ButcherProduct.convAt t₂ coef (BTree.node gc) j)) := by
  classical
  have hLHS :
      (∑ i : Fin t, t₂.b i *
          ButcherProduct.convAt t₂ coef (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  rw [hLHS, ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  refine Finset.prod_congr rfl ?_
  intro p _
  generalize children.get p = c
  cases c with
  | leaf =>
    simp [ButcherProduct.rightAuxAtCoef_leaf]
  | node gc =>
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]

/-- bSeries-form specialization of
`ButcherProduct.bWeighted_convAt_node_kept_eq`: the second-method
`b`-weighted stage sum of `ButcherProduct t₁ t₂` at a node is the mixed
kept-children trunk recursion with `coef := t₁.bSeries`. -/
theorem ButcherProduct.bSeries_natAdd_node_kept_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, t₁.bSeries (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       ButcherProduct.convAt t₂ (t₁.bSeries)
                         (BTree.node gc) j)) := by
  rw [ButcherProduct.bSeries_natAdd_eq_convAt,
      ButcherProduct.bWeighted_convAt_node_kept_eq]

/-- All-leaves-grandchildren kept-node summand collapse: after choosing a
cut subset among the grandchildren of a kept node, the remaining product of
row sums is exactly the elementary-weight contribution to the `bSeries` of a
singleton parent over a leaf-only node. This is the depth-2 analogue of the
cycle 538 all-leaves collapse, restricted to one summand so it can be reused
inside future mixed-child convolution formulas. -/
theorem ButcherProduct.bWeighted_kept_node_all_leaves_summand_eq
    {t n : ℕ} (t₂ : ButcherTableau t) (S : Finset (Fin n)) :
    (∑ i : Fin t, t₂.b i *
        (∑ j : Fin t, t₂.A i j *
          ∏ _p ∈ Sᶜ, ∑ k : Fin t, t₂.A j k))
      = t₂.bSeries
          (BTree.node
            [BTree.node (List.replicate (n - S.card) BTree.leaf)]) := by
  classical
  have hcard : (Sᶜ : Finset (Fin n)).card = n - S.card := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin]
  have hbSeries :
      t₂.bSeries
          (BTree.node
            [BTree.node (List.replicate (n - S.card) BTree.leaf)])
        = ∑ i : Fin t, t₂.b i *
            (∑ j : Fin t, t₂.A i j *
              (∑ k : Fin t, t₂.A j k) ^ (n - S.card)) := by
    unfold ButcherTableau.bSeries
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ButcherTableau.elementaryWeight_singleton]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [elementaryWeight_node_replicate_leaf]
  rw [hbSeries]
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _
  congr 1
  rw [Finset.prod_const, hcard]

/-! ### §384 first fully bSeries-only product closed form

Cycle 540: assemble the kept-leaf and singleton-node closed forms into the
first bSeries-only closed form for the product `bSeries` on a non-leaf
tree, namely the second-order rooted tree `BTree.node [BTree.leaf]`.
The right-hand side mentions `t₁` only through `t₁.bSeries` values and
mentions `t₂` only through `t₂.bSeries` values and `t₂.weightsSum`. -/

/-- §384 honest convolution closed form on the second-order rooted tree
`BTree.node [BTree.leaf]`: the bSeries-side convolution `bConv` evaluated
at this tree decomposes into three bSeries-only summands. The cut-side
contribution is `t₂.weightsSum * t₁.bSeries BTree.leaf`, and the kept-side
inner term collapses (via `bWeighted_convAt_kept_leaf_eq`) to
`t₂.bSeries (BTree.node [BTree.leaf])`. -/
theorem ButcherProduct.bConv_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherProduct.bConv (t₁.bSeries) t₂ (BTree.node [BTree.leaf])
      = t₁.bSeries (BTree.node [BTree.leaf])
        + t₂.bSeries (BTree.node [BTree.leaf])
        + t₂.weightsSum * t₁.bSeries BTree.leaf := by
  unfold ButcherProduct.bConv
  rw [ButcherProduct.bWeighted_convAt_singleton_node_eq t₂ t₁.bSeries BTree.leaf,
      ButcherProduct.bWeighted_convAt_kept_leaf_eq t₂ t₁.bSeries]
  ring

/-- Headline §384 corollary: the product `bSeries` on the second-order
rooted tree `BTree.node [BTree.leaf]` decomposes into a sum of three
bSeries-only summands. This is the first §384 closed-form result that
mentions both `t₁` and `t₂` only through `bSeries` and `weightsSum`. -/
theorem ButcherProduct.bSeries_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries (BTree.node [BTree.leaf])
      = t₁.bSeries (BTree.node [BTree.leaf])
        + t₂.bSeries (BTree.node [BTree.leaf])
        + t₂.weightsSum * t₁.bSeries BTree.leaf := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_singleton_leaf_eq]

/-- Product bSeries closed form on the empty-child node. -/
theorem ButcherProduct.bSeries_node_nil_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries (BTree.node [])
      = t₁.weightsSum + t₂.weightsSum := by
  rw [bSeries_node_nil]
  simp [weightsSum, butcherProduct_b_sum]

/-- Product bSeries closed form on the singleton `node []` child. -/
theorem ButcherProduct.bSeries_node_node_nil_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries (BTree.node [BTree.node []])
      = t₁.bSeries (BTree.node [BTree.leaf])
        + t₂.bSeries (BTree.node [BTree.leaf])
        + t₂.weightsSum * t₁.bSeries (BTree.node []) := by
  rw [bSeries_node_node_nil, ButcherProduct.bSeries_singleton_leaf_eq]
  have hleaf : t₁.bSeries BTree.leaf = t₁.bSeries (BTree.node []) := by
    rw [bSeries_leaf, bSeries_node_nil]
  rw [hleaf]

/-! ### §384 all-leaves parametric closed form (cycle 542)

Lifts the cycle 538 `bWeighted_convAt_node_all_leaves_eq` into a fully
bSeries-only product closed form on the parametric all-leaves family
`BTree.node (List.replicate n BTree.leaf)`. Unlike the cycle 540 / 541
single-shape theorems, this covers one shape per order parametrically in
`n`, so it is the first §384 product closed form that scales to every
order. -/

/-- §384 honest convolution closed form on the all-leaves family
`BTree.node (List.replicate n BTree.leaf)`: the bSeries-side convolution
`bConv` decomposes into a powerset sum where each summand multiplies
`t₁.bSeries BTree.leaf` raised to the cut-set cardinality by the
`t₂.bSeries` of a node of the remaining leaves. -/
theorem ButcherProduct.bConv_node_replicate_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    ButcherProduct.bConv (t₁.bSeries) t₂
        (BTree.node (List.replicate n BTree.leaf))
      = t₁.bSeries (BTree.node (List.replicate n BTree.leaf))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries BTree.leaf) ^ S.card *
            t₂.bSeries
              (BTree.node (List.replicate (n - S.card) BTree.leaf)) := by
  unfold ButcherProduct.bConv
  have hAll : ∀ c ∈ List.replicate n BTree.leaf, c = BTree.leaf := by
    intro c hc
    exact List.eq_of_mem_replicate hc
  rw [ButcherProduct.bWeighted_convAt_node_all_leaves_eq t₂ t₁.bSeries
        (List.replicate n BTree.leaf) hAll]
  have hlen : (List.replicate n BTree.leaf).length = n := List.length_replicate
  classical
  let e : Fin (List.replicate n BTree.leaf).length ≃ Fin n :=
    { toFun := Fin.cast hlen
      invFun := Fin.cast hlen.symm
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }
  -- Powerset Finset bijection induced by `e`.
  let φ : Finset (Fin (List.replicate n BTree.leaf).length) ≃ Finset (Fin n) :=
    Equiv.finsetCongr e
  congr 1
  refine Finset.sum_equiv φ ?_ ?_
  · intro S
    simp [φ, e]
  · intro S _
    have hcard : (φ S).card = S.card := by
      simp [φ]
    rw [Finset.prod_const, hcard]
    simp only [List.length_replicate]

/-- Headline §384 corollary on the all-leaves family: the product
`bSeries` on `BTree.node (List.replicate n BTree.leaf)` decomposes into a
sum that mentions both `t₁` and `t₂` only through `bSeries`. -/
theorem ButcherProduct.bSeries_node_replicate_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node (List.replicate n BTree.leaf))
      = t₁.bSeries (BTree.node (List.replicate n BTree.leaf))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries BTree.leaf) ^ S.card *
            t₂.bSeries
              (BTree.node (List.replicate (n - S.card) BTree.leaf)) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_replicate_leaf_eq]

/-! ### §384 dual all-empty-node parametric closed form (cycle 544)

Mirror of the cycle 542 all-leaves family with `BTree.leaf` replaced
throughout by `BTree.node []`. Both trees have the same `bSeries`-side
data (`tab.bSeries leaf = tab.bSeries (node []) = tab.weightsSum`) and
the same `convAt` value (= 1), so the cycle 542 closed form transports
to the dual all-empty-node family `BTree.node (List.replicate n
(BTree.node []))`. -/

/-- The `convAt` value at an empty-children node is 1: the only powerset
element of `Finset (Fin 0)` is `∅`, with empty product equal to 1. -/
@[simp] theorem ButcherProduct.convAt_node_nil
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.convAt t₂ coef (BTree.node []) i = 1 := by
  rw [ButcherProduct.convAt_node]
  classical
  rw [show (Finset.univ : Finset (Finset (Fin ([] : List BTree).length)))
        = {∅} from rfl]
  simp

/-- Empty-child nodes are stagewise units for `convAt`. -/
theorem ButcherProduct.IsConvAtUnit_node_nil
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    ButcherProduct.IsConvAtUnit t₂ coef (BTree.node []) := by
  intro j
  simp

/-- The `rightAuxAtCoef` value at an empty-children node is 1, by
`rightAuxAtCoef_eq_convAt` plus `convAt_node_nil`. -/
private theorem rightAuxAtCoef_node_nil
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node []) i = 1 := by
  rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  exact ButcherProduct.convAt_node_nil t₂ coef i

/-- Helper: the elementary weight of a node whose children are `n`
empty-children nodes collapses to the `n`-th power of the row sum
`∑ k, A i k`. Mirror of `elementaryWeight_node_replicate_leaf`. -/
private theorem elementaryWeight_node_replicate_node_nil
    {s : ℕ} (tab : ButcherTableau s) (n : ℕ) (i : Fin s) :
    tab.elementaryWeight (BTree.node (List.replicate n (BTree.node []))) i
      = (∑ k : Fin s, tab.A i k) ^ n := by
  induction n with
  | zero =>
    show tab.elementaryWeight (BTree.node []) i = _
    simp [ButcherTableau.elementaryWeight]
  | succ m ih =>
    rw [List.replicate_succ]
    have hfold :
        tab.elementaryWeight
            (BTree.node (BTree.node [] :: List.replicate m (BTree.node []))) i
          = tab.elementaryWeight
              (BTree.node (List.replicate m (BTree.node []))) i *
              (∑ k : Fin s, tab.A i k *
                tab.elementaryWeight (BTree.node []) k) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih]
    have hew : ∀ k : Fin s, tab.elementaryWeight (BTree.node []) k = 1 := by
      intro k
      simp [ButcherTableau.elementaryWeight]
    simp_rw [hew, mul_one]
    rw [pow_succ]

/-- All-`node []` trunk/cut closed form: when every child of the root is
`BTree.node []`, the b-weighted `convAt` at `BTree.node children`
decomposes into a sum over cut subsets `S`, where each summand multiplies
the cut term `(∏ p ∈ S, coef (BTree.node []))` by the `bSeries` of a
node of `(BTree.node [])`-only remaining children. Mirror of
`bWeighted_convAt_node_all_leaves_eq`. -/
theorem ButcherProduct.bWeighted_convAt_node_all_node_nil_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree)
    (hAll : ∀ c ∈ children, c = BTree.node []) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ _p ∈ S, coef (BTree.node [])) *
          t₂.bSeries
            (BTree.node
              (List.replicate (children.length - S.card)
                (BTree.node []))) := by
  classical
  have hchild : ∀ p : Fin children.length,
      children.get p = BTree.node [] := by
    intro p
    exact hAll (children.get p) (List.get_mem children p)
  have hLHS :
      (∑ i : Fin t, t₂.b i *
          ButcherProduct.convAt t₂ coef (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            ButcherProduct.rightAuxAtCoef t₂ coef
              (BTree.node children) i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ButcherProduct.rightAuxAtCoef_eq_convAt]
  rw [hLHS,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion]
  refine Finset.sum_congr rfl ?_
  intro S _
  have hfac1 : (∏ p ∈ S, coef (children.get p))
      = (∏ _p ∈ S, coef (BTree.node [])) := by
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [hchild p]
  rw [hfac1]
  congr 1
  have hcard : (Sᶜ : Finset (Fin children.length)).card
      = children.length - S.card := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin]
  have hbSeries :
      t₂.bSeries
          (BTree.node
            (List.replicate (children.length - S.card)
              (BTree.node [])))
        = ∑ i : Fin t, t₂.b i *
            (∑ j : Fin t, t₂.A i j) ^ (children.length - S.card) := by
    unfold ButcherTableau.bSeries
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [elementaryWeight_node_replicate_node_nil]
  rw [hbSeries]
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  have hfac2 : (∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                  ButcherProduct.rightAuxAtCoef t₂ coef
                    (children.get p) j)
      = (∏ _p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j) := by
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [hchild p]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [rightAuxAtCoef_node_nil, mul_one]
  rw [hfac2, Finset.prod_const, hcard]

/-- §384 honest convolution closed form on the all-empty-node family
`BTree.node (List.replicate n (BTree.node []))`: the bSeries-side
convolution `bConv` decomposes into a powerset sum where each summand
multiplies `t₁.bSeries (BTree.node [])` raised to the cut-set
cardinality by the `t₂.bSeries` of a node of the remaining empty-node
children. Dual of `bConv_node_replicate_leaf_eq`. -/
theorem ButcherProduct.bConv_node_replicate_node_nil_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    ButcherProduct.bConv (t₁.bSeries) t₂
        (BTree.node (List.replicate n (BTree.node [])))
      = t₁.bSeries (BTree.node (List.replicate n (BTree.node [])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries (BTree.node [])) ^ S.card *
            t₂.bSeries
              (BTree.node
                (List.replicate (n - S.card) (BTree.node []))) := by
  unfold ButcherProduct.bConv
  have hAll : ∀ c ∈ List.replicate n (BTree.node []),
      c = BTree.node [] := by
    intro c hc
    exact List.eq_of_mem_replicate hc
  rw [ButcherProduct.bWeighted_convAt_node_all_node_nil_eq t₂ t₁.bSeries
        (List.replicate n (BTree.node [])) hAll]
  have hlen : (List.replicate n (BTree.node [])).length = n :=
    List.length_replicate
  classical
  let e : Fin (List.replicate n (BTree.node [])).length ≃ Fin n :=
    { toFun := Fin.cast hlen
      invFun := Fin.cast hlen.symm
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }
  let φ : Finset (Fin (List.replicate n (BTree.node [])).length)
            ≃ Finset (Fin n) :=
    Equiv.finsetCongr e
  congr 1
  refine Finset.sum_equiv φ ?_ ?_
  · intro S
    simp [φ, e]
  · intro S _
    have hcard : (φ S).card = S.card := by
      simp [φ]
    rw [Finset.prod_const, hcard]
    simp only [List.length_replicate]

/-- Headline §384 corollary on the all-empty-node family: the product
`bSeries` on `BTree.node (List.replicate n (BTree.node []))` decomposes
into a sum that mentions both `t₁` and `t₂` only through `bSeries`. Dual
of `bSeries_node_replicate_leaf_eq`. -/
theorem ButcherProduct.bSeries_node_replicate_node_nil_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node (List.replicate n (BTree.node [])))
      = t₁.bSeries (BTree.node (List.replicate n (BTree.node [])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries (BTree.node [])) ^ S.card *
            t₂.bSeries
              (BTree.node
                (List.replicate (n - S.card) (BTree.node []))) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_replicate_node_nil_eq]

/-! ### §384 concrete mixed trivial-child fallback closures (cycle 545)

These finite mixed-shape formulas reuse the all-leaves parametric closure:
`BTree.leaf` and `BTree.node []` have the same elementary-weight value, so
the exact mixed root shape transports to the all-leaves family of the same
arity. They avoid the invalid weaker generalization from `convAt`-unit alone,
which does not imply the elementary-weight unit needed on the `t₂.bSeries`
kept side. -/

/-- §384 finite mixed closure on `BTree.node [BTree.leaf, BTree.node []]`. -/
theorem ButcherProduct.bSeries_node_leaf_node_nil_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node [BTree.leaf, BTree.node []])
      = t₁.bSeries (BTree.node [BTree.leaf, BTree.node []])
        + ∑ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
            (t₁.bSeries BTree.leaf) ^ S.card *
            t₂.bSeries
              (BTree.node (List.replicate (2 - S.card) BTree.leaf)) := by
  have hp : (ButcherProduct t₁ t₂).bSeries
        (BTree.node [BTree.leaf, BTree.node []])
      = (ButcherProduct t₁ t₂).bSeries
          (BTree.node (List.replicate 2 BTree.leaf)) := by
    simp [ButcherTableau.bSeries, ButcherTableau.elementaryWeight, List.foldr]
  rw [hp, ButcherProduct.bSeries_node_replicate_leaf_eq]
  simp [ButcherTableau.bSeries, ButcherTableau.elementaryWeight, List.foldr]

/-- §384 finite mixed closure on `BTree.node [BTree.node [], BTree.leaf]`. -/
theorem ButcherProduct.bSeries_node_node_nil_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node [BTree.node [], BTree.leaf])
      = t₁.bSeries (BTree.node [BTree.node [], BTree.leaf])
        + ∑ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
            (t₁.bSeries BTree.leaf) ^ S.card *
            t₂.bSeries
              (BTree.node (List.replicate (2 - S.card) BTree.leaf)) := by
  have hp : (ButcherProduct t₁ t₂).bSeries
        (BTree.node [BTree.node [], BTree.leaf])
      = (ButcherProduct t₁ t₂).bSeries
          (BTree.node (List.replicate 2 BTree.leaf)) := by
    simp [ButcherTableau.bSeries, ButcherTableau.elementaryWeight, List.foldr]
  rw [hp, ButcherProduct.bSeries_node_replicate_leaf_eq]
  simp [ButcherTableau.bSeries, ButcherTableau.elementaryWeight, List.foldr]

/-- §384 finite mixed closure on
`BTree.node [BTree.leaf, BTree.leaf, BTree.node []]`. -/
theorem ButcherProduct.bSeries_node_leaf_leaf_node_nil_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node [BTree.leaf, BTree.leaf, BTree.node []])
      = t₁.bSeries
          (BTree.node [BTree.leaf, BTree.leaf, BTree.node []])
        + ∑ S ∈ (Finset.univ : Finset (Fin 3)).powerset,
            (t₁.bSeries BTree.leaf) ^ S.card *
            t₂.bSeries
              (BTree.node (List.replicate (3 - S.card) BTree.leaf)) := by
  have hp : (ButcherProduct t₁ t₂).bSeries
        (BTree.node [BTree.leaf, BTree.leaf, BTree.node []])
      = (ButcherProduct t₁ t₂).bSeries
          (BTree.node (List.replicate 3 BTree.leaf)) := by
    simp [ButcherTableau.bSeries, ButcherTableau.elementaryWeight, List.foldr]
  rw [hp, ButcherProduct.bSeries_node_replicate_leaf_eq]
  simp [ButcherTableau.bSeries, ButcherTableau.elementaryWeight, List.foldr]

/-! ### §384 parametric trivial-children all-shapes closed form (cycle 546)

Generalizes cycles 540, 542, 544, 545: covers every node `BTree.node
children` whose children are each `BTree.leaf` or `BTree.node []` in one
parametric theorem. The two trivial child shapes share elementary weight
`1`, so a node with arbitrary trivial children agrees with the all-leaves
node of the same arity at every elementary-weight slot, and the closed
form transports from cycle 542's `bSeries_node_replicate_leaf_eq`. -/

/-- Helper: for any tableau, the elementary weight of a node whose every
child is `BTree.leaf` or `BTree.node []` agrees with the elementary
weight of an all-leaves node of the same arity. Both shapes have
elementary weight `1`, so each foldr factor `∑ k, A i k *
elementaryWeight c k` collapses to `∑ k, A i k`. -/
private theorem elementaryWeight_node_trivial_children_eq_replicate_leaf
    {s : ℕ} (tab : ButcherTableau s) (children : List BTree)
    (hTriv : ∀ c ∈ children, c = BTree.leaf ∨ c = BTree.node [])
    (i : Fin s) :
    tab.elementaryWeight (BTree.node children) i
      = tab.elementaryWeight
          (BTree.node (List.replicate children.length BTree.leaf)) i := by
  induction children with
  | nil => simp
  | cons c cs ih =>
    have hc : c = BTree.leaf ∨ c = BTree.node [] :=
      hTriv c (List.mem_cons_self)
    have hcs : ∀ x ∈ cs, x = BTree.leaf ∨ x = BTree.node [] := by
      intro x hx
      exact hTriv x (List.mem_cons_of_mem c hx)
    have ih' := ih hcs
    have hLHS :
        tab.elementaryWeight (BTree.node (c :: cs)) i
          = tab.elementaryWeight (BTree.node cs) i *
            (∑ k : Fin s, tab.A i k * tab.elementaryWeight c k) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    have hRHS :
        tab.elementaryWeight
            (BTree.node (List.replicate (c :: cs).length BTree.leaf)) i
          = tab.elementaryWeight
              (BTree.node (List.replicate cs.length BTree.leaf)) i *
            (∑ k : Fin s, tab.A i k) := by
      rw [List.length_cons, List.replicate_succ]
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hLHS, hRHS, ih']
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k _
    rcases hc with rfl | rfl
    · simp
    · simp [ButcherTableau.elementaryWeight]

/-- Helper: bSeries on a node with trivial children agrees with bSeries
on the all-leaves node of the same arity. -/
private theorem bSeries_node_trivial_children_eq_replicate_leaf
    {s : ℕ} (tab : ButcherTableau s) (children : List BTree)
    (hTriv : ∀ c ∈ children, c = BTree.leaf ∨ c = BTree.node []) :
    tab.bSeries (BTree.node children)
      = tab.bSeries
          (BTree.node (List.replicate children.length BTree.leaf)) := by
  unfold ButcherTableau.bSeries
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [elementaryWeight_node_trivial_children_eq_replicate_leaf tab children
        hTriv i]

/-- §384 honest convolution closed form on the all-trivial-children
family `BTree.node children` (each child is `BTree.leaf` or
`BTree.node []`): `bConv` decomposes into a powerset sum where each
summand multiplies `t₁.bSeries BTree.leaf` raised to the cut-set
cardinality by the `t₂.bSeries` of an all-leaves node of the remaining
arity. Generalizes `bConv_node_replicate_leaf_eq` (cycle 542) and
`bConv_node_replicate_node_nil_eq` (cycle 544) to arbitrary mixes. -/
theorem ButcherProduct.bConv_node_trivial_children_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree)
    (hTriv : ∀ p : Fin children.length,
        children.get p = BTree.leaf ∨ children.get p = BTree.node []) :
    ButcherProduct.bConv (t₁.bSeries) t₂ (BTree.node children)
      = t₁.bSeries (BTree.node children)
        + ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
            (t₁.bSeries BTree.leaf) ^ S.card *
            t₂.bSeries
              (BTree.node
                (List.replicate (children.length - S.card) BTree.leaf)) := by
  have hMem : ∀ c ∈ children, c = BTree.leaf ∨ c = BTree.node [] := by
    intro c hc
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hc
    rw [← hk]
    exact hTriv k
  rw [show ButcherProduct.bConv (t₁.bSeries) t₂ (BTree.node children)
        = (ButcherProduct t₁ t₂).bSeries (BTree.node children) from
        (ButcherProduct.bSeries_eq_bConv t₁ t₂ (BTree.node children)).symm,
      bSeries_node_trivial_children_eq_replicate_leaf
        (ButcherProduct t₁ t₂) children hMem,
      ButcherProduct.bSeries_node_replicate_leaf_eq,
      ← bSeries_node_trivial_children_eq_replicate_leaf t₁ children hMem]

/-- Headline §384 corollary on the all-trivial-children family: the
product `bSeries` on `BTree.node children` (each child is `BTree.leaf`
or `BTree.node []`) decomposes into a sum that mentions both `t₁` and
`t₂` only through `bSeries`. Parametric in `children`, this subsumes
the cycle 540 / 542 / 544 / 545 single-shape and finite mixed-shape
closed forms in one statement. -/
theorem ButcherProduct.bSeries_node_trivial_children_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree)
    (hTriv : ∀ p : Fin children.length,
        children.get p = BTree.leaf ∨ children.get p = BTree.node []) :
    (ButcherProduct t₁ t₂).bSeries (BTree.node children)
      = t₁.bSeries (BTree.node children)
        + ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
            (t₁.bSeries BTree.leaf) ^ S.card *
            t₂.bSeries
              (BTree.node
                (List.replicate (children.length - S.card) BTree.leaf)) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_trivial_children_eq t₁ t₂ children hTriv]

/-! ### §384 all-singleton-leaf-children parametric closed form (cycle 547)

Each root child is the order-2 tree `BTree.node [BTree.leaf]`. Unlike the
cycle 546 trivial-children family, the kept child is not elementary-weight
unit: its `convAt` value exposes an additional internal cut at the leaf.
The closed form therefore has an outer powerset over root children and, for
each kept-root subset, an inner powerset over the singleton leaves inside the
kept children. -/

/-- The `convAt` value at the singleton-leaf child is the cut coefficient
on the leaf plus the second tableau row sum. -/
private theorem convAt_singleton_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.convAt t₂ coef (BTree.node [BTree.leaf]) i
      = coef BTree.leaf + ∑ j : Fin t, t₂.A i j := by
  rw [← ButcherProduct.rightAuxAtCoef_eq_convAt]
  rw [ButcherProduct.rightAuxAtCoef_node_singleton]
  simp [ButcherProduct.rightAuxAtCoef_leaf]

/-- Helper: the elementary weight of a node whose children are `n`
singleton-leaf nodes collapses to the `n`-th power of the depth-2 row
factor `∑ j, A i j * (∑ k, A j k)`. -/
private theorem elementaryWeight_node_replicate_singleton_leaf
    {s : ℕ} (tab : ButcherTableau s) (n : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node (List.replicate n (BTree.node [BTree.leaf]))) i
      = (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ n := by
  induction n with
  | zero =>
    simp [ButcherTableau.elementaryWeight]
  | succ m ih =>
    rw [List.replicate_succ]
    have hfold :
        tab.elementaryWeight
            (BTree.node
              (BTree.node [BTree.leaf] ::
                List.replicate m (BTree.node [BTree.leaf]))) i
          = tab.elementaryWeight
              (BTree.node (List.replicate m (BTree.node [BTree.leaf]))) i *
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

/-- Helper for mixed kept-side summands: a node with `a` leaf children
followed by `b` singleton-leaf children has elementary weight equal to the
product of the corresponding leaf row factors and depth-2 row factors. -/
private theorem elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf
    {s : ℕ} (tab : ButcherTableau s) (a b : ℕ) (i : Fin s) :
    tab.elementaryWeight
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]))) i
      = (∑ j : Fin s, tab.A i j) ^ a *
        (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b := by
  induction a with
  | zero =>
    simp [elementaryWeight_node_replicate_singleton_leaf]
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    have hfold :
        tab.elementaryWeight
            (BTree.node
              (BTree.leaf ::
                (List.replicate m BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf])))) i
          = tab.elementaryWeight
              (BTree.node
                (List.replicate m BTree.leaf ++
                  List.replicate b (BTree.node [BTree.leaf]))) i *
              (∑ j : Fin s, tab.A i j) := by
      simp [ButcherTableau.elementaryWeight, List.foldr]
    rw [hfold, ih, pow_succ]
    ring

/-- `bSeries` form of
`elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf`. -/
private theorem bSeries_node_replicate_leaf_append_replicate_singleton_leaf
    {s : ℕ} (tab : ButcherTableau s) (a b : ℕ) :
    tab.bSeries
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf])))
      = ∑ i : Fin s, tab.b i *
          ((∑ j : Fin s, tab.A i j) ^ a *
            (∑ j : Fin s, tab.A i j * (∑ k : Fin s, tab.A j k)) ^ b) := by
  unfold ButcherTableau.bSeries
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf]

/-- A kept singleton-leaf child contributes the sum of an internal cut
factor and a depth-2 kept factor. -/
private theorem singleton_leaf_kept_factor_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    (∑ j : Fin t, t₂.A i j *
      ButcherProduct.convAt t₂ coef (BTree.node [BTree.leaf]) j)
      = coef BTree.leaf * (∑ j : Fin t, t₂.A i j)
        + ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) := by
  calc
    (∑ j : Fin t, t₂.A i j *
      ButcherProduct.convAt t₂ coef (BTree.node [BTree.leaf]) j)
        = ∑ j : Fin t, t₂.A i j *
            (coef BTree.leaf + ∑ k : Fin t, t₂.A j k) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [convAt_singleton_leaf_eq]
    _ = ∑ j : Fin t,
          (t₂.A i j * coef BTree.leaf
            + t₂.A i j * (∑ k : Fin t, t₂.A j k)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
    _ = (∑ j : Fin t, t₂.A i j * coef BTree.leaf)
        + ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) := by
          rw [Finset.sum_add_distrib]
    _ = coef BTree.leaf * (∑ j : Fin t, t₂.A i j)
        + ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k) := by
          congr 1
          rw [← Finset.sum_mul]
          ring

/-- Inner kept-side collapse for a fixed root cut set. Expanding the
singleton-leaf `convAt` factor over the kept root children yields an inner
powerset; each summand is the `bSeries` of a mixed node with leaf children
for internal cuts and singleton-leaf children for internal keeps. -/
private theorem bWeighted_kept_singleton_leaf_product_eq
    {t n : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (S : Finset (Fin n)) :
    (∑ i : Fin t, t₂.b i *
        ∏ _p ∈ Sᶜ,
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef (BTree.node [BTree.leaf]) j)
      = ∑ T ∈ Sᶜ.powerset,
          (coef BTree.leaf) ^ T.card *
          t₂.bSeries
            (BTree.node
              (List.replicate T.card BTree.leaf ++
                List.replicate ((Sᶜ).card - T.card)
                  (BTree.node [BTree.leaf]))) := by
  classical
  let row : Fin t → ℝ := fun i => ∑ j : Fin t, t₂.A i j
  let chain : Fin t → ℝ := fun i =>
    ∑ j : Fin t, t₂.A i j * (∑ k : Fin t, t₂.A j k)
  calc
    (∑ i : Fin t, t₂.b i *
        ∏ _p ∈ Sᶜ,
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.convAt t₂ coef (BTree.node [BTree.leaf]) j)
        = ∑ i : Fin t, t₂.b i *
            ∏ _p ∈ Sᶜ,
              (coef BTree.leaf * row i + chain i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          congr 1
          refine Finset.prod_congr rfl ?_
          intro p _
          simp [row, chain, singleton_leaf_kept_factor_eq]
    _ = ∑ i : Fin t, t₂.b i *
          (∑ T ∈ Sᶜ.powerset,
            (∏ _p ∈ T, coef BTree.leaf * row i) *
              ∏ _p ∈ Sᶜ \ T, chain i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          congr 1
          rw [Finset.prod_add]
    _ = ∑ i : Fin t,
          ∑ T ∈ Sᶜ.powerset,
            t₂.b i *
              ((coef BTree.leaf) ^ T.card *
                (row i) ^ T.card *
                (chain i) ^ ((Sᶜ).card - T.card)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro T hT
          rw [Finset.mul_sum]
          have hTsub : T ⊆ Sᶜ := Finset.mem_powerset.mp hT
          rw [Finset.prod_const, Finset.prod_const,
            Finset.card_sdiff_of_subset hTsub]
          rw [← Finset.mul_sum, mul_pow]
    _ = ∑ T ∈ Sᶜ.powerset,
          ∑ i : Fin t,
            t₂.b i *
              ((coef BTree.leaf) ^ T.card *
                (row i) ^ T.card *
                (chain i) ^ ((Sᶜ).card - T.card)) := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ Sᶜ.powerset,
          (coef BTree.leaf) ^ T.card *
          (∑ i : Fin t, t₂.b i *
            ((row i) ^ T.card *
              (chain i) ^ ((Sᶜ).card - T.card))) := by
          refine Finset.sum_congr rfl ?_
          intro T hT
          calc
            (∑ i : Fin t,
                t₂.b i *
                  ((coef BTree.leaf) ^ T.card *
                    (row i) ^ T.card *
                    (chain i) ^ ((Sᶜ).card - T.card)))
                = ∑ i : Fin t,
                    (coef BTree.leaf) ^ T.card *
                      (t₂.b i *
                        ((row i) ^ T.card *
                          (chain i) ^ ((Sᶜ).card - T.card))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  ring
            _ = (coef BTree.leaf) ^ T.card *
                  (∑ i : Fin t, t₂.b i *
                    ((row i) ^ T.card *
                      (chain i) ^ ((Sᶜ).card - T.card))) := by
                  rw [Finset.mul_sum]
    _ = ∑ T ∈ Sᶜ.powerset,
          (coef BTree.leaf) ^ T.card *
          t₂.bSeries
            (BTree.node
              (List.replicate T.card BTree.leaf ++
                List.replicate ((Sᶜ).card - T.card)
                  (BTree.node [BTree.leaf]))) := by
          refine Finset.sum_congr rfl ?_
          intro T hT
          congr 1
          rw [bSeries_node_replicate_leaf_append_replicate_singleton_leaf]

private theorem bWeighted_convAt_node_replicate_singleton_leaf_eq_length
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (n : ℕ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node (List.replicate n (BTree.node [BTree.leaf]))) i)
      = ∑ S ∈
          (Finset.univ :
            Finset (Fin (List.replicate n (BTree.node [BTree.leaf])).length)).powerset,
          (coef (BTree.node [BTree.leaf])) ^ S.card *
          (∑ T ∈ Sᶜ.powerset,
            (coef BTree.leaf) ^ T.card *
            t₂.bSeries
              (BTree.node
                (List.replicate T.card BTree.leaf ++
                  List.replicate ((Sᶜ).card - T.card)
                    (BTree.node [BTree.leaf])))) := by
  rw [ButcherProduct.bWeighted_convAt_node_kept_eq]
  rw [Finset.powerset_univ]
  refine Finset.sum_congr
    (M := ℝ)
    (s₁ := (Finset.univ :
      Finset (Finset (Fin (List.replicate n (BTree.node [BTree.leaf])).length))))
    (s₂ := (Finset.univ :
      Finset (Finset (Fin (List.replicate n (BTree.node [BTree.leaf])).length))))
    rfl ?_
  intro S _
  have hcut :
      (∏ p ∈ S,
          coef ((List.replicate n (BTree.node [BTree.leaf])).get p))
        = (coef (BTree.node [BTree.leaf])) ^ S.card := by
    calc
      (∏ p ∈ S,
          coef ((List.replicate n (BTree.node [BTree.leaf])).get p))
          = ∏ _p ∈ S, coef (BTree.node [BTree.leaf]) := by
            refine Finset.prod_congr (M := ℝ) rfl ?_
            intro p _
            simp
      _ = (coef (BTree.node [BTree.leaf])) ^ S.card := by
            rw [Finset.prod_const]
  rw [hcut]
  congr 1
  convert bWeighted_kept_singleton_leaf_product_eq t₂ coef S using 2
  congr 1
  refine Finset.prod_congr (M := ℝ) rfl ?_
  intro p _
  simp

private theorem bWeighted_convAt_node_replicate_singleton_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (n : ℕ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.convAt t₂ coef
          (BTree.node (List.replicate n (BTree.node [BTree.leaf]))) i)
      = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (coef (BTree.node [BTree.leaf])) ^ S.card *
          (∑ T ∈ Sᶜ.powerset,
            (coef BTree.leaf) ^ T.card *
            t₂.bSeries
              (BTree.node
                (List.replicate T.card BTree.leaf ++
                  List.replicate ((Sᶜ).card - T.card)
                    (BTree.node [BTree.leaf])))) := by
  classical
  have hlen : (List.replicate n (BTree.node [BTree.leaf])).length = n :=
    List.length_replicate
  let e : Fin (List.replicate n (BTree.node [BTree.leaf])).length ≃ Fin n :=
    { toFun := Fin.cast hlen
      invFun := Fin.cast hlen.symm
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }
  let φ :
      Finset (Fin (List.replicate n (BTree.node [BTree.leaf])).length) ≃
        Finset (Fin n) :=
    Equiv.finsetCongr e
  rw [bWeighted_convAt_node_replicate_singleton_leaf_eq_length]
  refine Finset.sum_equiv φ ?_ ?_
  · intro S
    simp [φ, e]
  · intro S hS
    have hcard : (φ S).card = S.card := by
      simp [φ]
    have hcompl :
        ((φ S)ᶜ : Finset (Fin n)).card = (Sᶜ).card := by
      rw [Finset.card_compl, Finset.card_compl, hcard]
      simp [Fintype.card_fin, hlen]
    rw [hcard]
    congr 1
    refine Finset.sum_equiv φ ?_ ?_
    · intro T
      simpa [φ, Finset.mem_powerset, Finset.subset_iff] using
        (show
          (∀ ⦃x :
              Fin (List.replicate n (BTree.node [BTree.leaf])).length⦄,
              x ∈ T → x ∉ S) ↔
            (∀ ⦃x : Fin n⦄, e.symm x ∈ T → e.symm x ∉ S) from
          ⟨fun h {x} hx => h hx,
           fun h {x} hx => by
            have hnot : e.symm (e x) ∉ S := h (by simpa using hx)
            simpa using hnot⟩)
    · intro T hT
      have hTcard : (φ T).card = T.card := by
        simp [φ]
      rw [hTcard, hcompl]

/-- §384 honest convolution closed form on the all-singleton-leaf family
`BTree.node (List.replicate n (BTree.node [BTree.leaf]))`. Root cuts
contribute `t₁.bSeries (node [leaf])`; each kept root child contributes an
inner cut/keep choice at its leaf, producing mixed leaf/singleton-leaf
`t₂.bSeries` summands. -/
theorem ButcherProduct.bConv_node_replicate_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    ButcherProduct.bConv (t₁.bSeries) t₂
        (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
      = t₁.bSeries
          (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries (BTree.node [BTree.leaf])) ^ S.card *
            (∑ T ∈ Sᶜ.powerset,
              (t₁.bSeries BTree.leaf) ^ T.card *
              t₂.bSeries
                (BTree.node
                  (List.replicate T.card BTree.leaf ++
                    List.replicate ((Sᶜ).card - T.card)
                      (BTree.node [BTree.leaf])))) := by
  unfold ButcherProduct.bConv
  rw [bWeighted_convAt_node_replicate_singleton_leaf_eq]

/-- Headline §384 corollary on the all-singleton-leaf family: the product
`bSeries` decomposes into a root-cut powerset and an internal-cut powerset
of bSeries-only summands. -/
theorem ButcherProduct.bSeries_node_replicate_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (n : ℕ) :
    (ButcherProduct t₁ t₂).bSeries
        (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
      = t₁.bSeries
          (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
        + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
            (t₁.bSeries (BTree.node [BTree.leaf])) ^ S.card *
            (∑ T ∈ Sᶜ.powerset,
              (t₁.bSeries BTree.leaf) ^ T.card *
              t₂.bSeries
                (BTree.node
                  (List.replicate T.card BTree.leaf ++
                    List.replicate ((Sᶜ).card - T.card)
                      (BTree.node [BTree.leaf])))) := by
  rw [ButcherProduct.bSeries_eq_bConv,
      ButcherProduct.bConv_node_replicate_singleton_leaf_eq]

/-! ### §384 mixed leaf / singleton-leaf root-children parametric helper

Cycle 549 re-lands the cycle 548 per-stage closed form for root children
made of `BTree.leaf` and `BTree.node [BTree.leaf]`. -/

/-- Per-stage `convAt` value at the mixed root family
`replicate a leaf ++ replicate b (node [leaf])` is a product of two
powers: a leaf factor `(coef leaf + row i)^a` and a singleton-leaf
factor `(coef (node [leaf]) + coef leaf * row i + chain i)^b`. -/
private theorem convAt_node_mixed_leaf_singleton_leaf_at_i_eq
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

/-- Product-form binomial expansion over an arbitrary finite set. -/
private theorem prod_const_add_eq_powerset {α : Type*} [DecidableEq α]
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
private theorem pow_add_eq_powerset (x y : ℝ) (n : ℕ) :
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
private theorem convAt_double_leaf_eq
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


end ButcherTableau
