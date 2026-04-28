import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section384

/-!
# Butcher §38 — algebraic Runge–Kutta properties (umbrella)

Cycle 535 split this file because it crossed the 3000-line cap. The
§381 / §382 / §384-prep core is now in `OpenMath.ButcherGroup.Core`,
and the §384 right-block convolution chain is in
`OpenMath.ButcherGroup.Section384`. This umbrella imports both and
contains the §387 power chain, `IsRKEquivalentExt`, `IsG1Equiv`, and
`G1`.

Downstream callers should continue to `import OpenMath.ButcherGroup`;
this module re-exposes both sub-modules transitively.
-/

open Finset

namespace ButcherTableau

variable {s : ℕ}

namespace QuotEquiv

/-- Butcher-series associativity on relabel-equivalence classes. The
`bSeries` lifted to `QuotEquiv` is associative under `product`, even though
the raw `ButcherProduct` is not on-the-nose associative. -/
theorem product_bSeries_assoc {s t u : ℕ}
    (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) (q₃ : QuotEquiv u) (τ : BTree) :
    bSeries (product (product q₁ q₂) q₃) τ =
      bSeries (product q₁ (product q₂ q₃)) τ := by
  refine Quotient.inductionOn₃ q₁ q₂ q₃ ?_
  intro t₁ t₂ t₃
  simpa [product, bSeries] using
    ButcherProduct.bSeries_assoc t₁ t₂ t₃ τ

/-- The lifted weights-sum `weightsSum` is associative under `product`. -/
theorem product_weightsSum_assoc {s t u : ℕ}
    (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) (q₃ : QuotEquiv u) :
    (product (product q₁ q₂) q₃).weightsSum =
      (product q₁ (product q₂ q₃)).weightsSum := by
  rw [product_weightsSum, product_weightsSum, product_weightsSum,
      product_weightsSum, add_assoc]

/-- Order-condition associativity: `(q₁ * q₂) * q₃` satisfies the tree
condition for `τ` iff `q₁ * (q₂ * q₃)` does. This is the §384-facing
consequence of `bSeries` associativity. -/
theorem product_satisfiesTreeCondition_assoc {s t u : ℕ}
    (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) (q₃ : QuotEquiv u) (τ : BTree) :
    satisfiesTreeCondition (product (product q₁ q₂) q₃) τ ↔
      satisfiesTreeCondition (product q₁ (product q₂ q₃)) τ := by
  rw [satisfiesTreeCondition_iff_bSeries,
      satisfiesTreeCondition_iff_bSeries,
      product_bSeries_assoc]

/-- The quotient product by the zero-stage tableau on the left preserves the
Butcher-series coefficient. -/
theorem product_bSeries_one_left {t : ℕ} (q : QuotEquiv t) (τ : BTree) :
    bSeries (product (Quotient.mk _ trivialTableau) q) τ = bSeries q τ := by
  refine Quotient.inductionOn q ?_
  intro t₂
  simpa [product, bSeries] using ButcherProduct.bSeries_one_left t₂ τ

/-- The quotient product by the zero-stage tableau on the right preserves the
Butcher-series coefficient. -/
theorem product_bSeries_one_right {s : ℕ} (q : QuotEquiv s) (τ : BTree) :
    bSeries (product q (Quotient.mk _ trivialTableau)) τ = bSeries q τ := by
  refine Quotient.inductionOn q ?_
  intro t₁
  simpa [product, bSeries] using ButcherProduct.bSeries_one_right t₁ τ

/-- The §384-facing elementary-weight map from a quotient class to its
tree-indexed Butcher-series coefficients. -/
noncomputable def bSeriesHom {s : ℕ} (q : QuotEquiv s) : BTree → ℝ :=
  fun τ => bSeries q τ

/-- The zero-stage tableau has vanishing positive-tree Butcher-series
coefficients. The current `BTree` type has no separate empty tree. -/
theorem bSeriesHom_one (τ : BTree) :
    bSeriesHom (Quotient.mk _ trivialTableau) τ = 0 := by
  simp [bSeriesHom, bSeries]

/-- §384-shaped alias of the already-landed bSeries associativity law. -/
theorem bSeriesHom_assoc {s t u : ℕ}
    (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) (q₃ : QuotEquiv u) (τ : BTree) :
    bSeriesHom (product (product q₁ q₂) q₃) τ =
      bSeriesHom (product q₁ (product q₂ q₃)) τ := by
  simpa [bSeriesHom] using product_bSeries_assoc q₁ q₂ q₃ τ

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

end QuotEquiv

/-! ### §387 raw and quotient powers

The raw power keeps the right-associated shape `(t^n) * t`, matching the
orientation of the one-sided identity lemmas above. The stage count is written
recursively instead of as multiplication so that the tableau type follows the
same nested `ButcherProduct` shape by definitional reduction. -/

/-- Stage count of the right-associated raw `n`th power of an `s`-stage
tableau. -/
def ButcherProduct.npowStages (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => s + ButcherProduct.npowStages s n

@[simp] theorem ButcherProduct.npowStages_zero (s : ℕ) :
    ButcherProduct.npowStages s 0 = 0 := rfl

@[simp] theorem ButcherProduct.npowStages_succ (s n : ℕ) :
    ButcherProduct.npowStages s (n + 1) =
      s + ButcherProduct.npowStages s n := rfl

/-- Closed form for `npowStages`: it is just `n * s`. -/
theorem ButcherProduct.npowStages_eq (s n : ℕ) :
    ButcherProduct.npowStages s n = n * s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ButcherProduct.npowStages_succ, ih, Nat.succ_mul, Nat.add_comm]

/-- Stage counts of powers are additive in the exponent. -/
theorem ButcherProduct.npowStages_add (s m n : ℕ) :
    ButcherProduct.npowStages s (m + n) =
      ButcherProduct.npowStages s m + ButcherProduct.npowStages s n := by
  simp [ButcherProduct.npowStages_eq, Nat.add_mul]

/-- Right-associated raw powers of a Butcher tableau under `ButcherProduct`. -/
def ButcherProduct.npow {s : ℕ} (t : ButcherTableau s) :
    ∀ n : ℕ, ButcherTableau (ButcherProduct.npowStages s n)
  | 0 => trivialTableau
  | n + 1 => ButcherProduct t (ButcherProduct.npow t n)

@[simp] theorem ButcherProduct.npow_zero {s : ℕ} (t : ButcherTableau s) :
    ButcherProduct.npow t 0 = trivialTableau := rfl

@[simp] theorem ButcherProduct.npow_succ {s : ℕ}
    (t : ButcherTableau s) (n : ℕ) :
    ButcherProduct.npow t (n + 1) =
      ButcherProduct t (ButcherProduct.npow t n) := rfl

@[simp] theorem ButcherProduct.npow_one {s : ℕ} (t : ButcherTableau s) :
    ButcherProduct.npow t 1 =
      ButcherProduct t trivialTableau := rfl

namespace QuotEquiv

/-- Right-associated powers lifted to relabel-equivalence classes. -/
noncomputable def npow {s : ℕ} (q : QuotEquiv s) :
    ∀ n : ℕ, QuotEquiv (ButcherProduct.npowStages s n)
  | 0 => Quotient.mk _ trivialTableau
  | n + 1 => QuotEquiv.product q (QuotEquiv.npow q n)

@[simp] theorem npow_zero {s : ℕ} (q : QuotEquiv s) :
    npow q 0 = Quotient.mk _ trivialTableau := rfl

@[simp] theorem npow_succ {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    npow q (n + 1) = product q (npow q n) := rfl

@[simp] theorem npow_mk {s : ℕ} (t : ButcherTableau s) (n : ℕ) :
    npow (Quotient.mk _ t) n =
      Quotient.mk _ (ButcherProduct.npow t n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change product (Quotient.mk _ t) (npow (Quotient.mk _ t) n) =
        Quotient.mk _ (ButcherProduct t (ButcherProduct.npow t n))
      rw [ih]
      rfl

theorem bSeriesHom_npow_zero {s : ℕ} (q : QuotEquiv s) :
    bSeriesHom (npow q 0) =
      bSeriesHom (Quotient.mk _ trivialTableau) := rfl

theorem weightsSum_npow_zero {s : ℕ} (q : QuotEquiv s) :
    weightsSum (npow q 0) = 0 := by
  simp [npow, weightsSum, trivialTableau]

/-- Successor step for the raw weights-sum power chain. -/
theorem _root_.ButcherProduct.npow_succ_weightsSum {s : ℕ}
    (t : ButcherTableau s) (n : ℕ) :
    (∑ i, (ButcherProduct.npow t n.succ).b i) =
      (∑ i, (ButcherProduct.npow t n).b i) + (∑ i, t.b i) := by
  rw [ButcherProduct.npow_succ]
  change (∑ i, (ButcherProduct t (ButcherProduct.npow t n)).b i) =
    (∑ i, (ButcherProduct.npow t n).b i) + (∑ i, t.b i)
  rw [butcherProduct_b_sum, add_comm]

/-- Successor step for the quotient weights-sum power chain. -/
theorem weightsSum_npow_succ {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    (npow q n.succ).weightsSum =
      (npow q n).weightsSum + q.weightsSum := by
  rw [npow_succ, product_weightsSum, add_comm]

/-- Closed form: `n`-th quotient power weights-sum is `n` times the base. -/
theorem weightsSum_npow {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    (npow q n).weightsSum = (n : ℝ) * q.weightsSum := by
  induction n with
  | zero =>
      rw [weightsSum_npow_zero, Nat.cast_zero, zero_mul]
  | succ n ih =>
      rw [weightsSum_npow_succ, ih]
      push_cast
      ring

/-- Unit-power identity for the quotient Butcher-series homomorphism. -/
theorem bSeriesHom_npow_one {s : ℕ} (q : QuotEquiv s) :
    (npow q 1).bSeriesHom = q.bSeriesHom := by
  funext τ
  change bSeries (product q (Quotient.mk _ trivialTableau)) τ = bSeries q τ
  exact product_bSeries_one_right q τ

/-- Zero-power node-sum vanishes for the quotient Butcher product. -/
theorem cSum_npow_zero {s : ℕ} (q : QuotEquiv s) :
    cSum (npow q 0) = 0 := by
  simp [npow, cSum, trivialTableau]

end QuotEquiv

theorem butcherProduct_c_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ∑ i : Fin (s + t), (ButcherProduct t₁ t₂).c i
      = (∑ i : Fin s, t₁.c i) + (t : ℝ) + (∑ i : Fin t, t₂.c i) := by
  rw [Fin.sum_univ_add]
  simp [ButcherProduct, Finset.sum_add_distrib, Finset.sum_const, add_assoc]

namespace QuotEquiv

theorem product_cSum {s t : ℕ} (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) :
    (q₁.product q₂).cSum = q₁.cSum + (t : ℝ) + q₂.cSum := by
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro t₁ t₂
  simp [product, butcherProduct_c_sum]

theorem cSum_npow_succ {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    (q.npow n.succ).cSum =
      q.cSum + (ButcherProduct.npowStages s n : ℝ) + (q.npow n).cSum := by
  rw [npow_succ, product_cSum]

@[simp]
theorem weightsSum_npow_one {s : ℕ} (q : QuotEquiv s) :
    (q.npow 1).weightsSum = q.weightsSum := by
  simpa using weightsSum_npow q 1

@[simp]
theorem cSum_npow_one {s : ℕ} (q : QuotEquiv s) :
    (q.npow 1).cSum = q.cSum := by
  rw [cSum_npow_succ]
  simp

/-- Closed form for the `n`-th power node-sum: `n * cSum + s * n*(n-1)/2`. -/
theorem cSum_npow {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    (q.npow n).cSum =
      (n : ℝ) * q.cSum + (s : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
  induction n with
  | zero =>
      rw [cSum_npow_zero]
      push_cast
      ring
  | succ n ih =>
      rw [cSum_npow_succ, ih, ButcherProduct.npowStages_eq]
      push_cast
      ring

/-- Alternate form of the weights-sum successor step in the right-associated
    orientation. -/
theorem weightsSum_npow_succ' {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    (q.npow (n + 1)).weightsSum =
      q.weightsSum + (q.npow n).weightsSum := by
  rw [weightsSum_npow_succ, add_comm]

/-- `n = 2` instance of the closed-form `weightsSum_npow`. -/
theorem weightsSum_npow_two {s : ℕ} (q : QuotEquiv s) :
    (q.npow 2).weightsSum = 2 * q.weightsSum := by
  simpa using weightsSum_npow q 2

/-- `n = 2` instance of the closed-form `cSum_npow`. -/
theorem cSum_npow_two {s : ℕ} (q : QuotEquiv s) :
    (q.npow 2).cSum = 2 * q.cSum + (s : ℝ) := by
  have h := cSum_npow q 2
  push_cast at h
  linarith

/-- Weights-sums of powers are additive in the exponent. -/
theorem weightsSum_npow_add {s : ℕ} (q : QuotEquiv s) (m n : ℕ) :
    (q.npow (m + n)).weightsSum =
      (q.npow m).weightsSum + (q.npow n).weightsSum := by
  have hmn := weightsSum_npow q (m + n)
  have hm := weightsSum_npow q m
  have hn := weightsSum_npow q n
  push_cast at hmn hm hn
  linarith

/-- Node-sums of powers are additive up to the cross block contribution. -/
theorem cSum_npow_add {s : ℕ} (q : QuotEquiv s) (m n : ℕ) :
    (q.npow (m + n)).cSum =
      (q.npow m).cSum + (q.npow n).cSum + (s : ℝ) * m * n := by
  have hmn := cSum_npow q (m + n)
  have hm := cSum_npow q m
  have hn := cSum_npow q n
  push_cast at hmn hm hn
  nlinarith [hmn, hm, hn]

/-- `n = 3` instance of the closed-form `weightsSum_npow`. -/
theorem weightsSum_npow_three {s : ℕ} (q : QuotEquiv s) :
    (q.npow 3).weightsSum = 3 * q.weightsSum := by
  simpa using weightsSum_npow q 3

/-- `n = 3` instance of the closed-form `cSum_npow`. -/
theorem cSum_npow_three {s : ℕ} (q : QuotEquiv s) :
    (q.npow 3).cSum = 3 * q.cSum + 3 * (s : ℝ) := by
  have h := cSum_npow q 3
  push_cast at h
  linarith

/-- `n = 4` instance of the closed-form `weightsSum_npow`. -/
theorem weightsSum_npow_four {s : ℕ} (q : QuotEquiv s) :
    (q.npow 4).weightsSum = 4 * q.weightsSum := by
  simpa using weightsSum_npow q 4

/-- `n = 4` instance of the closed-form `cSum_npow`. -/
theorem cSum_npow_four {s : ℕ} (q : QuotEquiv s) :
    (q.npow 4).cSum = 4 * q.cSum + 6 * (s : ℝ) := by
  have h := cSum_npow q 4
  push_cast at h
  linarith

/-- Closed form for the stage count of an `(n * m)`-th right-associated power. -/
theorem npowStages_npow_eq_npowStages_mul (s n m : ℕ) :
    ButcherProduct.npowStages s (n * m) = n * m * s := by
  rw [ButcherProduct.npowStages_eq]

end QuotEquiv

/-! ### §381 stage padding

Right-pad a tableau with `n` zero stages. This is the building block for
cross-stage equivalence in §381: two tableaux of different stage counts
will become comparable by padding both to a common stage count and then
applying the existing `IsRKEquivalent` relation.

The stage count grows additively (`s + n`); the new rows/columns are zero
in `A`, `b`, and `c`. -/

/-- Right-pad a `ButcherTableau s` with `n` zero stages to obtain a
`ButcherTableau (s + n)`. The original `s × s` block is preserved; new
rows/columns are zero. -/
def padRight (t : ButcherTableau s) (n : ℕ) : ButcherTableau (s + n) where
  A := fun i j =>
    Fin.addCases
      (fun i₁ =>
        Fin.addCases
          (fun j₁ => t.A i₁ j₁)
          (fun _ => 0)
          j)
      (fun _ => 0)
      i
  b := fun i =>
    Fin.addCases (fun i₁ => t.b i₁) (fun _ => 0) i
  c := fun i =>
    Fin.addCases (fun i₁ => t.c i₁) (fun _ => 0) i

@[simp] theorem padRight_b_castAdd (t : ButcherTableau s) (n : ℕ) (i : Fin s) :
    (t.padRight n).b (Fin.castAdd n i) = t.b i := by
  simp [padRight]

@[simp] theorem padRight_b_natAdd (t : ButcherTableau s) (n : ℕ) (i : Fin n) :
    (t.padRight n).b (Fin.natAdd s i) = 0 := by
  simp [padRight]

@[simp] theorem padRight_c_castAdd (t : ButcherTableau s) (n : ℕ) (i : Fin s) :
    (t.padRight n).c (Fin.castAdd n i) = t.c i := by
  simp [padRight]

@[simp] theorem padRight_c_natAdd (t : ButcherTableau s) (n : ℕ) (i : Fin n) :
    (t.padRight n).c (Fin.natAdd s i) = 0 := by
  simp [padRight]

@[simp] theorem padRight_A_natAdd (t : ButcherTableau s) (n : ℕ)
    (i : Fin n) (j : Fin (s + n)) :
    (t.padRight n).A (Fin.natAdd s i) j = 0 := by
  simp [padRight]

@[simp] theorem padRight_A_castAdd_castAdd (t : ButcherTableau s) (n : ℕ)
    (i : Fin s) (j : Fin s) :
    (t.padRight n).A (Fin.castAdd n i) (Fin.castAdd n j) = t.A i j := by
  simp [padRight]

@[simp] theorem padRight_A_castAdd_natAdd (t : ButcherTableau s) (n : ℕ)
    (i : Fin s) (j : Fin n) :
    (t.padRight n).A (Fin.castAdd n i) (Fin.natAdd s j) = 0 := by
  simp [padRight]

theorem padRight_weightsSum (t : ButcherTableau s) (n : ℕ) :
    (∑ i, (t.padRight n).b i) = ∑ i, t.b i := by
  rw [Fin.sum_univ_add]
  simp

theorem padRight_cSum (t : ButcherTableau s) (n : ℕ) :
    (∑ i, (t.padRight n).c i) = ∑ i, t.c i := by
  rw [Fin.sum_univ_add]
  simp

/-- Padding preserves elementary weights at original stages. The pad rows
have all-zero `A`-entries, so the recursive node sum reduces to the
original `s`-block sum. -/
theorem padRight_elementaryWeight_castAdd
    (t : ButcherTableau s) (n : ℕ) (τ : BTree) (i : Fin s) :
    (t.padRight n).elementaryWeight τ (Fin.castAdd n i)
      = t.elementaryWeight τ i := by
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin s,
      (t.padRight n).elementaryWeight τ (Fin.castAdd n i)
        = t.elementaryWeight τ i)
    (motive_2 := fun children => ∀ i : Fin s,
      children.foldr
        (fun r acc => acc * (∑ k : Fin (s + n),
          (t.padRight n).A (Fin.castAdd n i) k *
            (t.padRight n).elementaryWeight r k)) 1 =
      children.foldr
        (fun r acc => acc * (∑ k : Fin s,
          t.A i k * t.elementaryWeight r k)) 1)
    ?leaf ?node ?nil ?cons τ
  · intro i; simp
  · intro children hchildren i
    simpa [ButcherTableau.elementaryWeight] using hchildren i
  · intro i; simp
  · intro head tail ih_head ih_tail i
    simp only [List.foldr]
    have hsum :
        (∑ k : Fin (s + n),
          (t.padRight n).A (Fin.castAdd n i) k *
            (t.padRight n).elementaryWeight head k) =
          ∑ k : Fin s, t.A i k * t.elementaryWeight head k := by
      rw [Fin.sum_univ_add]
      have hzero :
          (∑ k : Fin n,
            (t.padRight n).A (Fin.castAdd n i) (Fin.natAdd s k) *
              (t.padRight n).elementaryWeight head (Fin.natAdd s k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        simp
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [padRight_A_castAdd_castAdd, ih_head k]
    rw [ih_tail i, hsum]

/-- A nonempty node has zero elementary weight on a right-padded stage. The
degenerate `BTree.node []` has elementary weight `1`, so the nonemptiness
hypothesis is essential. -/
theorem padRight_elementaryWeight_natAdd_node_of_ne_nil
    (t : ButcherTableau s) (n : ℕ) {children : List BTree}
    (hchildren : children ≠ []) (i : Fin n) :
    (t.padRight n).elementaryWeight (BTree.node children) (Fin.natAdd s i) = 0 := by
  cases children with
  | nil => contradiction
  | cons head tail =>
      simp [ButcherTableau.elementaryWeight]

/-- Stretch lemma: padding preserves the b-weighted elementary-weight
sum. The pad block contributes zero because both `b` and the `A` rows are
zero there. -/
theorem padRight_bSeries (t : ButcherTableau s) (n : ℕ) (τ : BTree) :
    (∑ i : Fin (s + n),
      (t.padRight n).b i * (t.padRight n).elementaryWeight τ i)
      = ∑ i : Fin s, t.b i * t.elementaryWeight τ i := by
  rw [Fin.sum_univ_add]
  have hzero :
      (∑ i : Fin n,
        (t.padRight n).b (Fin.natAdd s i) *
          (t.padRight n).elementaryWeight τ (Fin.natAdd s i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [padRight_b_castAdd, padRight_elementaryWeight_castAdd]

/-! ### §381 cross-stage equivalence -/

/-- Right-padding respects same-stage relabel equivalence. The original
permutation acts on the preserved block, and the pad block is fixed. -/
theorem IsRKEquivalent.padRight {t₁ t₂ : ButcherTableau s}
    (h : IsRKEquivalent t₁ t₂) (n : ℕ) :
    IsRKEquivalent (t₁.padRight n) (t₂.padRight n) := by
  obtain ⟨σ₀, hA, hb, hc⟩ := h
  let σ : Equiv.Perm (Fin (s + n)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr σ₀ (Equiv.refl (Fin n))).trans finSumFinEquiv)
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i₁
      refine Fin.addCases ?_ ?_ j
      · intro j₁
        simp [σ, hA]
      · intro j₂
        simp [σ]
    · intro i₂
      simp [σ]
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i₁
      simp [σ, hb]
    · intro i₂
      simp [σ]
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i₁
      simp [σ, hc]
    · intro i₂
      simp [σ]

namespace QuotEquiv

/-- Constructor alias for quotient classes of relabel-equivalent tableaux. -/
def mk {s : ℕ} (t : ButcherTableau s) : QuotEquiv s :=
  Quotient.mk _ t

@[simp] theorem bSeriesHom_mk {s : ℕ} (t : ButcherTableau s) (τ : BTree) :
    (mk t).bSeriesHom τ = ∑ i, t.b i * t.elementaryWeight τ i := by
  rfl

/-- Right-padding lifted to relabel-equivalence classes. -/
def padRight {s : ℕ} (q : QuotEquiv s) (n : ℕ) : QuotEquiv (s + n) :=
  Quotient.lift (fun t : ButcherTableau s => mk (t.padRight n))
    (fun _ _ h => Quotient.sound (IsRKEquivalent.padRight h n)) q

@[simp] theorem padRight_mk {s : ℕ} (t : ButcherTableau s) (n : ℕ) :
    (mk t).padRight n = mk (t.padRight n) := rfl

/-- Padding does not change the lifted total weight. -/
theorem padRight_weightsSum {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    (q.padRight n).weightsSum = q.weightsSum := by
  refine Quotient.inductionOn q ?_
  intro t
  simp [padRight, mk, weightsSum, ButcherTableau.padRight_weightsSum]

/-- Padding does not change the lifted total node sum. -/
theorem padRight_cSum {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    (q.padRight n).cSum = q.cSum := by
  refine Quotient.inductionOn q ?_
  intro t
  simp [padRight, mk, cSum, ButcherTableau.padRight_cSum]

/-- Padding does not change any lifted Butcher-series coefficient. -/
theorem padRight_bSeries {s : ℕ} (q : QuotEquiv s) (n : ℕ) (τ : BTree) :
    (q.padRight n).bSeries τ = q.bSeries τ := by
  refine Quotient.inductionOn q ?_
  intro t
  simp [padRight, mk, bSeries, ButcherTableau.padRight_bSeries]

/-- Padding does not change the tree-indexed Butcher-series map. -/
theorem padRight_bSeriesHom {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    (q.padRight n).bSeriesHom = q.bSeriesHom := by
  funext τ
  exact padRight_bSeries q n τ

end QuotEquiv

/-- One directed padding step on staged quotient classes. -/
def IsRKEquivalentExtStep : Sigma QuotEquiv → Sigma QuotEquiv → Prop
  | ⟨s, q⟩, y => ∃ n : ℕ, y = ⟨s + n, q.padRight n⟩

/-- Cross-stage-count equivalence for quotient RK methods: the equivalence
closure generated by adding zero stages on the right. This packages the
common-padding idea without committing to a brittle normal form for stage-count
casts. -/
def IsRKEquivalentExt {s u : ℕ} (q₁ : QuotEquiv s) (q₂ : QuotEquiv u) : Prop :=
  Relation.EqvGen IsRKEquivalentExtStep ⟨s, q₁⟩ ⟨u, q₂⟩

namespace IsRKEquivalentExt

theorem refl {s : ℕ} (q : QuotEquiv s) : IsRKEquivalentExt q q := by
  exact Relation.EqvGen.refl _

theorem symm {s u : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsRKEquivalentExt q₁ q₂) : IsRKEquivalentExt q₂ q₁ := by
  exact Relation.EqvGen.symm _ _ h

theorem trans {s u v : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    {q₃ : QuotEquiv v}
    (h₁₂ : IsRKEquivalentExt q₁ q₂) (h₂₃ : IsRKEquivalentExt q₂ q₃) :
    IsRKEquivalentExt q₁ q₃ := by
  exact Relation.EqvGen.trans _ _ _ h₁₂ h₂₃

/-- Introduction from the common-padding witness shape: if two quotient
classes become heterogeneously equal after right-padding to the same stage
count, then they are related by `IsRKEquivalentExt`. -/
theorem of_common_pad {s u : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    {n m : ℕ} (heq : s + n = u + m)
    (hq : HEq (q₁.padRight n) (q₂.padRight m)) :
    IsRKEquivalentExt q₁ q₂ := by
  let x₁ : Sigma QuotEquiv := ⟨s, q₁⟩
  let x₂ : Sigma QuotEquiv := ⟨u, q₂⟩
  let y₁ : Sigma QuotEquiv := ⟨s + n, q₁.padRight n⟩
  let y₂ : Sigma QuotEquiv := ⟨u + m, q₂.padRight m⟩
  have hstep₁ : Relation.EqvGen IsRKEquivalentExtStep x₁ y₁ :=
    Relation.EqvGen.rel _ _ ⟨n, rfl⟩
  have hstep₂ : Relation.EqvGen IsRKEquivalentExtStep x₂ y₂ :=
    Relation.EqvGen.rel _ _ ⟨m, rfl⟩
  have hy : y₁ = y₂ := Sigma.ext heq hq
  exact Relation.EqvGen.trans _ _ _
    (by simpa [x₁, y₁] using hstep₁)
    (by simpa [x₂, y₁, y₂, hy] using Relation.EqvGen.symm _ _ hstep₂)

private theorem sigma_weightsSum_eq {x y : Sigma QuotEquiv}
    (h : Relation.EqvGen IsRKEquivalentExtStep x y) :
    x.2.weightsSum = y.2.weightsSum := by
  induction h with
  | rel x y hxy =>
      obtain ⟨n, rfl⟩ := hxy
      exact (QuotEquiv.padRight_weightsSum x.2 n).symm
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

private theorem sigma_cSum_eq {x y : Sigma QuotEquiv}
    (h : Relation.EqvGen IsRKEquivalentExtStep x y) :
    x.2.cSum = y.2.cSum := by
  induction h with
  | rel x y hxy =>
      obtain ⟨n, rfl⟩ := hxy
      exact (QuotEquiv.padRight_cSum x.2 n).symm
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

private theorem sigma_bSeriesHom_eq {x y : Sigma QuotEquiv}
    (h : Relation.EqvGen IsRKEquivalentExtStep x y) :
    x.2.bSeriesHom = y.2.bSeriesHom := by
  induction h with
  | rel x y hxy =>
      obtain ⟨n, rfl⟩ := hxy
      exact (QuotEquiv.padRight_bSeriesHom x.2 n).symm
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

theorem weightsSum_eq {s u : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsRKEquivalentExt q₁ q₂) :
    q₁.weightsSum = q₂.weightsSum := by
  exact sigma_weightsSum_eq h

theorem cSum_eq {s u : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsRKEquivalentExt q₁ q₂) :
    q₁.cSum = q₂.cSum := by
  exact sigma_cSum_eq h

theorem bSeriesHom_eq {s u : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsRKEquivalentExt q₁ q₂) :
    q₁.bSeriesHom = q₂.bSeriesHom := by
  exact sigma_bSeriesHom_eq h

/-- Cross-stage equivalence preserves every lifted tree condition. -/
theorem satisfiesTreeCondition_iff {s u : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsRKEquivalentExt q₁ q₂) (τ : BTree) :
    q₁.satisfiesTreeCondition τ ↔ q₂.satisfiesTreeCondition τ := by
  have hτ : q₁.bSeries τ = q₂.bSeries τ := by
    simpa [QuotEquiv.bSeriesHom] using congr_fun (bSeriesHom_eq h) τ
  rw [QuotEquiv.satisfiesTreeCondition_iff_bSeries,
      QuotEquiv.satisfiesTreeCondition_iff_bSeries, hτ]

private theorem hasTreeOrder_iff_forall {s : ℕ} (q : QuotEquiv s) (p : ℕ) :
    q.hasTreeOrder p ↔ ∀ τ : BTree, τ.order ≤ p → q.satisfiesTreeCondition τ := by
  refine Quotient.inductionOn q ?_
  intro t
  simp [QuotEquiv.hasTreeOrder, ButcherTableau.hasTreeOrder,
    QuotEquiv.satisfiesTreeCondition]

/-- Cross-stage equivalence preserves tree order up to any order `p`. -/
theorem hasTreeOrder_iff {s u : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsRKEquivalentExt q₁ q₂) (p : ℕ) :
    q₁.hasTreeOrder p ↔ q₂.hasTreeOrder p := by
  rw [hasTreeOrder_iff_forall q₁ p, hasTreeOrder_iff_forall q₂ p]
  exact forall_congr' fun τ =>
    imp_congr_right fun _ => satisfiesTreeCondition_iff h τ

end IsRKEquivalentExt

/-! ### §383 G₁ order-p equivalence -/

/-- `IsG1Equiv p q₁ q₂`: two quotient RK methods agree on the Butcher-series
map for every rooted tree of order ≤ `p`. This is the relation whose quotient
is Butcher's `G₁(p)` group of order-`p` methods. -/
def IsG1Equiv (p : ℕ) {s u : ℕ} (q₁ : QuotEquiv s) (q₂ : QuotEquiv u) : Prop :=
  ∀ τ : BTree, τ.order ≤ p → q₁.bSeriesHom τ = q₂.bSeriesHom τ

namespace IsG1Equiv

/-- `IsG1Equiv` is reflexive at every order. -/
theorem refl {s p : ℕ} (q : QuotEquiv s) : IsG1Equiv p q q := by
  intro _ _; rfl

/-- `IsG1Equiv` is symmetric. -/
theorem symm {s u p : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsG1Equiv p q₁ q₂) : IsG1Equiv p q₂ q₁ := by
  intro τ hτ; exact (h τ hτ).symm

/-- `IsG1Equiv` is transitive. -/
theorem trans {s u v p : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u} {q₃ : QuotEquiv v}
    (h₁ : IsG1Equiv p q₁ q₂) (h₂ : IsG1Equiv p q₂ q₃) :
    IsG1Equiv p q₁ q₃ := by
  intro τ hτ; exact (h₁ τ hτ).trans (h₂ τ hτ)

theorem bSeriesHom_eq {s u p : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsG1Equiv p q₁ q₂) {τ : BTree} (hτ : τ.order ≤ p) :
    q₁.bSeriesHom τ = q₂.bSeriesHom τ := by
  exact h τ hτ

/-- `IsG1Equiv` is monotone in the order parameter: agreement up to a larger
order implies agreement up to a smaller one. -/
theorem mono {s u p q : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (hpq : p ≤ q) (h : IsG1Equiv q q₁ q₂) : IsG1Equiv p q₁ q₂ := by
  intro τ hτ; exact h τ (hτ.trans hpq)

/-- Every two quotient methods are `G₁`-equivalent at order `0`, vacuously:
no rooted tree has order ≤ 0 since trees always have at least one vertex. -/
theorem zero {s u : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u} :
    IsG1Equiv 0 q₁ q₂ := by
  intro τ hτ
  have hpos := BTree.order_pos τ
  omega

end IsG1Equiv

/-- Cross-stage equivalence implies `G₁` equivalence at every order: equal
Butcher-series maps agree pointwise on every tree, so in particular on every
tree of order ≤ p. -/
theorem IsRKEquivalentExt.toG1Equiv {s u : ℕ} {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsRKEquivalentExt q₁ q₂) (p : ℕ) : IsG1Equiv p q₁ q₂ := by
  intro τ _
  exact congr_fun (IsRKEquivalentExt.bSeriesHom_eq h) τ

namespace IsG1Equiv

/-- For a single tree `τ` with `τ.order ≤ p`, `G₁` equivalence preserves the
lifted tree order condition. -/
theorem satisfiesTreeCondition_apply {s u p : ℕ}
    {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsG1Equiv p q₁ q₂) {τ : BTree} (hτ : τ.order ≤ p) :
    q₁.satisfiesTreeCondition τ ↔ q₂.satisfiesTreeCondition τ := by
  have hb : q₁.bSeries τ = q₂.bSeries τ := by
    simpa [QuotEquiv.bSeriesHom] using h τ hτ
  rw [QuotEquiv.satisfiesTreeCondition_iff_bSeries,
      QuotEquiv.satisfiesTreeCondition_iff_bSeries, hb]

/-- `G₁` equivalence preserves the lifted tree-order predicate at level `p`. -/
theorem hasTreeOrder_iff {s u p : ℕ}
    {q₁ : QuotEquiv s} {q₂ : QuotEquiv u}
    (h : IsG1Equiv p q₁ q₂) :
    q₁.hasTreeOrder p ↔ q₂.hasTreeOrder p := by
  rw [IsRKEquivalentExt.hasTreeOrder_iff_forall q₁ p,
      IsRKEquivalentExt.hasTreeOrder_iff_forall q₂ p]
  exact forall_congr' fun τ =>
    imp_congr_right fun hτ => satisfiesTreeCondition_apply h hτ

end IsG1Equiv

/-! ### §383 quotient `G₁(p)` layer -/

/-- Setoid on staged quotient classes identifying methods with the same
Butcher-series coefficients through order `p`. -/
def g1Setoid (p : ℕ) : Setoid (Σ s : ℕ, QuotEquiv s) where
  r x y := IsG1Equiv p x.2 y.2
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact IsG1Equiv.refl x.2
    · intro x y hxy
      exact IsG1Equiv.symm hxy
    · intro x y z hxy hyz
      exact IsG1Equiv.trans hxy hyz

/-- Butcher's `G₁(p)` quotient: RK methods modulo agreement of rooted-tree
coefficients through order `p`. -/
def G1 (p : ℕ) : Type :=
  Quotient (g1Setoid p)

namespace G1

/-- Projection from a staged quotient class to `G₁(p)`. -/
def mk {p s : ℕ} (q : QuotEquiv s) : G1 p :=
  Quotient.mk (g1Setoid p) ⟨s, q⟩

/-- The rooted-tree coefficient at a fixed tree of order at most `p`,
descended to `G₁(p)`. -/
noncomputable def bSeriesHomAt (p : ℕ) (τ : BTree) (hτ : τ.order ≤ p) :
    G1 p → ℝ :=
  Quotient.lift (fun x : Σ s : ℕ, QuotEquiv s => x.2.bSeriesHom τ) (by
    intro x y hxy
    exact hxy τ hτ)

/-- The order-`p` tree condition descended to `G₁(p)`. Above order `p` this
predicate is vacuous, since representatives are only identified through order
`p`. -/
noncomputable def satisfiesTreeCondition {p : ℕ} (g : G1 p) (τ : BTree) : Prop :=
  Quotient.lift
    (fun x : Σ s : ℕ, QuotEquiv s => τ.order ≤ p → x.2.satisfiesTreeCondition τ)
    (by
      intro x y hxy
      apply propext
      constructor
      · intro hx hτ
        exact (IsG1Equiv.satisfiesTreeCondition_apply hxy hτ).1 (hx hτ)
      · intro hy hτ
        exact (IsG1Equiv.satisfiesTreeCondition_apply hxy hτ).2 (hy hτ)) g

/-- The order-`p` predicate descended to `G₁(p)`. -/
noncomputable def hasTreeOrder {p : ℕ} : G1 p → Prop :=
  Quotient.lift (fun x : Σ s : ℕ, QuotEquiv s => x.2.hasTreeOrder p) (by
    intro x y hxy
    exact propext (IsG1Equiv.hasTreeOrder_iff hxy))

@[simp] theorem bSeriesHomAt_mk {p s : ℕ} (q : QuotEquiv s)
    (τ : BTree) (hτ : τ.order ≤ p) :
    bSeriesHomAt p τ hτ (mk (p := p) q) = q.bSeriesHom τ := by
  rfl

@[simp] theorem bSeriesHomAt_mk_apply {p s : ℕ}
    (q : QuotEquiv s) (τ : BTree) (hτ : τ.order ≤ p) :
    bSeriesHomAt p τ hτ (mk (p := p) q) = q.bSeriesHom τ := by
  rfl

@[simp] theorem satisfiesTreeCondition_mk {p s : ℕ} (q : QuotEquiv s)
    (τ : BTree) :
    satisfiesTreeCondition (mk (p := p) q) τ =
      (τ.order ≤ p → q.satisfiesTreeCondition τ) := by
  rfl

@[simp] theorem hasTreeOrder_mk {p s : ℕ} (q : QuotEquiv s) :
    hasTreeOrder (mk (p := p) q) = q.hasTreeOrder p := by
  rfl

/-- The identity element of `G₁(p)`: the class of the zero-stage tableau.
This is the §387 group identity for the (still-pending) `G1.mul` lift. -/
noncomputable def one (p : ℕ) : G1 p :=
  mk (p := p) (Quotient.mk _ trivialTableau)

/-- The Butcher-series coefficient of the `G₁(p)` identity vanishes on every
tree, in particular on every tree of order ≤ `p`. -/
@[simp] theorem bSeriesHomAt_one {p : ℕ} (τ : BTree) (hτ : τ.order ≤ p) :
    bSeriesHomAt p τ hτ (G1.one p) = 0 := by
  unfold one
  rw [bSeriesHomAt_mk]
  exact QuotEquiv.bSeriesHom_one τ

/-- Extensionality for `G₁(p)`: two classes coincide as soon as their lifted
rooted-tree coefficients agree at every tree of order ≤ `p`. This is the
quotient-level restatement of `IsG1Equiv` and is the main tool for proving
quotient equalities without unfolding the underlying `Quotient.mk`. -/
theorem ext {p : ℕ} {g₁ g₂ : G1 p}
    (h : ∀ τ : BTree, ∀ hτ : τ.order ≤ p,
        bSeriesHomAt p τ hτ g₁ = bSeriesHomAt p τ hτ g₂) :
    g₁ = g₂ := by
  induction g₁ using Quotient.inductionOn with
  | _ x =>
    induction g₂ using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      intro τ hτ
      simpa [bSeriesHomAt, mk] using h τ hτ

/-- The order-restricted bSeries map on `G₁(p)` is faithful: classes are
equal iff they agree on every tree of order at most `p`. -/
theorem eq_iff_forall_bSeriesHomAt {p : ℕ} (g₁ g₂ : G1 p) :
    g₁ = g₂ ↔
      ∀ τ : BTree, ∀ hτ : τ.order ≤ p,
        bSeriesHomAt p τ hτ g₁ = bSeriesHomAt p τ hτ g₂ := by
  refine ⟨fun h _ _ => by rw [h], ?_⟩
  intro h
  exact ext h

/-- Bridging characterization: two quotient classes have equal `G₁(p)` images
iff they are `IsG1Equiv`. -/
theorem mk_eq_mk_iff_isG1Equiv {p s s' : ℕ}
    (q : QuotEquiv s) (q' : QuotEquiv s') :
    (mk (p := p) q = mk (p := p) q') ↔ IsG1Equiv p q q' := by
  constructor
  · intro h
    have := Quotient.exact h
    exact this
  · intro h
    exact Quotient.sound h

/-- The `hasTreeOrder` predicate on `G₁(p)` is equivalent to satisfying every
tree condition up to order `p`, mirroring the same-stage characterization for
`QuotEquiv`. -/
theorem hasTreeOrder_iff_forall {p : ℕ} (g : G1 p) :
    g.hasTreeOrder ↔ ∀ τ : BTree, τ.order ≤ p → g.satisfiesTreeCondition τ := by
  induction g using Quotient.inductionOn with
  | _ x =>
    show x.2.hasTreeOrder p ↔
      ∀ τ : BTree, τ.order ≤ p →
        (τ.order ≤ p → x.2.satisfiesTreeCondition τ)
    rw [IsRKEquivalentExt.hasTreeOrder_iff_forall x.2 p]
    refine forall_congr' fun τ => ?_
    refine imp_congr_right fun hτ => ?_
    exact ⟨fun h _ => h, fun h => h hτ⟩

theorem hasTreeOrder_one_iff (p : ℕ) :
    hasTreeOrder (one p) ↔
      ∀ τ : BTree, τ.order ≤ p → (0 : ℝ) = 1 / (τ.density : ℝ) := by
  rw [hasTreeOrder_iff_forall]
  simp [one, QuotEquiv.satisfiesTreeCondition_iff_bSeries, QuotEquiv.bSeries]

theorem hasTreeOrder_zero_one : hasTreeOrder (one 0) := by
  rw [hasTreeOrder_one_iff]
  intro τ hτ
  have hpos := BTree.order_pos τ
  omega

theorem eq_one_iff {p : ℕ} (g : G1 p) :
    g = one p ↔ ∀ τ : BTree, (hτ : τ.order ≤ p) →
      bSeriesHomAt p τ hτ g = 0 := by
  rw [eq_iff_forall_bSeriesHomAt]
  simp

end G1

end ButcherTableau
