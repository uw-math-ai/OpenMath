import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions
import OpenMath.ButcherGroup.Core
import OpenMath.ButcherGroup.Section384
import OpenMath.ButcherGroup.Section384Slices
import OpenMath.ButcherGroup.Section384SlicesMixed
import OpenMath.ButcherGroup.Section384SlicesQuadMixed
import OpenMath.ButcherGroup.Section386Conv
import OpenMath.ButcherGroup.QuotEquivSlices

/-!
# Butcher §38 — algebraic Runge–Kutta properties (umbrella)

Cycle 535 split this file because it crossed the 3000-line cap. The
§381 / §382 / §384-prep core is now in `OpenMath.ButcherGroup.Core`,
and the §384 right-block convolution chain is in
`OpenMath.ButcherGroup.Section384`. The §384 closed-form slice modules
are in `OpenMath.ButcherGroup.Section384Slices`,
`OpenMath.ButcherGroup.Section384SlicesMixed`, and
`OpenMath.ButcherGroup.Section384SlicesQuadMixed`. The §386 bSeries-only
admissible-cut convolution is in `OpenMath.ButcherGroup.Section386Conv`.
This umbrella imports those modules and contains the §387 power chain,
`IsRKEquivalentExt`, `IsG1Equiv`, and `G1`.

Downstream callers should continue to `import OpenMath.ButcherGroup`;
this module re-exposes the split sub-modules transitively.
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

/-- The leaf bSeries hom coefficient is the lifted weights sum. -/
theorem bSeriesHom_leaf {s : ℕ} (q : QuotEquiv s) :
    q.bSeriesHom BTree.leaf = q.weightsSum := by
  refine Quotient.inductionOn q ?_
  intro t
  simp [bSeriesHom, bSeries, weightsSum]

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

/-- Closed form for the stage count of an `(m * n)`-th right-associated
power. -/
theorem ButcherProduct.npowStages_mul (s m n : ℕ) :
    ButcherProduct.npowStages s (m * n) = m * n * s := by
  simpa using ButcherProduct.npowStages_eq s (m * n)

/-- Multiplicative exponent form for stage counts of powers. -/
theorem ButcherProduct.npowStages_mul_eq (s m n : ℕ) :
    ButcherProduct.npowStages s (m * n) =
      m * ButcherProduct.npowStages s n := by
  rw [ButcherProduct.npowStages_eq, ButcherProduct.npowStages_eq]
  exact Nat.mul_assoc m n s

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

/-- Multiplicative-exponent closed form for quotient power weights-sums. -/
theorem weightsSum_npow_mul {s : ℕ} (q : QuotEquiv s) (m n : ℕ) :
    (q.npow (m * n)).weightsSum = (m * n : ℝ) * q.weightsSum := by
  simpa using weightsSum_npow q (m * n)

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

/-- Multiplicative-exponent closed form for quotient power node-sums. -/
theorem cSum_npow_mul {s : ℕ} (q : QuotEquiv s) (m n : ℕ) :
    (q.npow (m * n)).cSum =
      (m * n : ℝ) * q.cSum
        + (s : ℝ) * ((m * n : ℝ) * ((m * n : ℝ) - 1) / 2) := by
  simpa using cSum_npow q (m * n)

/-- Alternate form of the weights-sum successor step in the right-associated
    orientation. -/
theorem weightsSum_npow_succ' {s : ℕ} (q : QuotEquiv s) (n : ℕ) :
    (q.npow (n + 1)).weightsSum =
      q.weightsSum + (q.npow n).weightsSum := by
  rw [weightsSum_npow_succ, add_comm]

/-- Nonnegative base weights-sum is bounded above by every positive power
weights-sum. -/
theorem weightsSum_npow_le {s : ℕ} (q : QuotEquiv s) (n : ℕ)
    (h : 0 ≤ q.weightsSum) :
    q.weightsSum ≤ (q.npow (n + 1)).weightsSum := by
  rw [weightsSum_npow q (n + 1)]
  push_cast
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  nlinarith

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

/-- `n = 5` instance of the closed-form `weightsSum_npow`. -/
theorem weightsSum_npow_five {s : ℕ} (q : QuotEquiv s) :
    (q.npow 5).weightsSum = 5 * q.weightsSum := by
  simpa using weightsSum_npow q 5

/-- `n = 5` instance of the closed-form `cSum_npow`. -/
theorem cSum_npow_five {s : ℕ} (q : QuotEquiv s) :
    (q.npow 5).cSum = 5 * q.cSum + 10 * (s : ℝ) := by
  have h := cSum_npow q 5
  push_cast at h
  linarith

/-- Closed form for the stage count of an `(n * m)`-th right-associated power. -/
theorem npowStages_npow_eq_npowStages_mul (s n m : ℕ) :
    ButcherProduct.npowStages s (n * m) = n * m * s := by
  rw [ButcherProduct.npowStages_eq]

/-- Stage count closed form after feeding an `n`th-power stage count back
into `npowStages`. -/
theorem npowStages_npow_eq_mul (s n : ℕ) :
    ButcherProduct.npowStages s (ButcherProduct.npowStages s n) =
      n * s * s := by
  simp [ButcherProduct.npowStages_eq]

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

/-- The first tracked well-definedness slice for `G1.mul`: product preserves
`G₁` equivalence through order two. -/
theorem product_congr_le_two
    {s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv 2 q q') (hr : IsG1Equiv 2 r r') :
    IsG1Equiv 2 (q.product r) (q'.product r') := by
  intro τ hτ
  have hleaf_order : BTree.leaf.order ≤ 2 := by simp
  have hnode_nil_order : (BTree.node []).order ≤ 2 := by native_decide
  have hsingleton_order : (BTree.node [BTree.leaf]).order ≤ 2 := by native_decide
  have hq_leaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf :=
    hq BTree.leaf hleaf_order
  have hr_leaf : r.bSeriesHom BTree.leaf = r'.bSeriesHom BTree.leaf :=
    hr BTree.leaf hleaf_order
  have hq_weights : q.weightsSum = q'.weightsSum := by
    simpa [QuotEquiv.bSeriesHom_leaf] using hq_leaf
  have hr_weights : r.weightsSum = r'.weightsSum := by
    simpa [QuotEquiv.bSeriesHom_leaf] using hr_leaf
  have hq_node_nil :
      q.bSeriesHom (BTree.node []) = q'.bSeriesHom (BTree.node []) :=
    hq (BTree.node []) hnode_nil_order
  have hq_singleton :
      q.bSeriesHom (BTree.node [BTree.leaf]) =
        q'.bSeriesHom (BTree.node [BTree.leaf]) :=
    hq (BTree.node [BTree.leaf]) hsingleton_order
  have hr_singleton :
      r.bSeriesHom (BTree.node [BTree.leaf]) =
        r'.bSeriesHom (BTree.node [BTree.leaf]) :=
    hr (BTree.node [BTree.leaf]) hsingleton_order
  rcases (BTree.order_le_two_iff τ).1 hτ with rfl | rfl | rfl | rfl
  · simp [QuotEquiv.bSeriesHom_leaf, QuotEquiv.product_weightsSum,
      hq_weights, hr_weights]
  · simp [QuotEquiv.bSeriesHom_product_node_nil, hq_weights, hr_weights]
  · rw [QuotEquiv.bSeriesHom_product_singleton_leaf,
      QuotEquiv.bSeriesHom_product_singleton_leaf]
    rw [hq_singleton, hr_singleton, hr_weights, hq_leaf]
  · rw [QuotEquiv.bSeriesHom_product_node_node_nil,
      QuotEquiv.bSeriesHom_product_node_node_nil]
    rw [hq_singleton, hr_singleton, hr_weights, hq_node_nil]

/-- Order of an all-leaves node: `(BTree.node (List.replicate n BTree.leaf)).order = n + 1`. -/
private theorem order_node_replicate_leaf (n : ℕ) :
    (BTree.node (List.replicate n BTree.leaf)).order = n + 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [BTree.order_node, List.foldr, BTree.order_leaf]
    have ihrw : (BTree.node (List.replicate m BTree.leaf)).order = m + 1 := ih
    simp only [BTree.order_node] at ihrw
    omega

/-- Cycle 542 second tracked `G1.mul`-direction well-definedness deliverable:
parametric in `n`, product preserves `G₁` equivalence on every all-leaves
tree `BTree.node (List.replicate n BTree.leaf)` whose order is at most `p`.
This covers one shape per order, all orders, and is the structural lift of
the cycle 540 / 541 finite enumeration to the all-leaves family. -/
theorem product_congr_node_replicate_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (n : ℕ) (hn : n + 1 ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node (List.replicate n BTree.leaf))
      = (q'.product r').bSeriesHom
        (BTree.node (List.replicate n BTree.leaf)) := by
  rw [QuotEquiv.bSeriesHom_product_node_replicate_leaf,
      QuotEquiv.bSeriesHom_product_node_replicate_leaf]
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq; rw [BTree.order_leaf]; omega
  have hnode_n :
      q.bSeriesHom (BTree.node (List.replicate n BTree.leaf))
        = q'.bSeriesHom (BTree.node (List.replicate n BTree.leaf)) := by
    apply hq; rw [order_node_replicate_leaf]; omega
  rw [hnode_n]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S _
  have hS : S.card ≤ n := by
    have hmem : S ⊆ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_powerset.mp ‹S ∈ _›
    have := Finset.card_le_card hmem
    simp at this
    exact this
  have hsub :
      r.bSeriesHom (BTree.node (List.replicate (n - S.card) BTree.leaf))
        = r'.bSeriesHom (BTree.node (List.replicate (n - S.card) BTree.leaf)) := by
    apply hr
    rw [order_node_replicate_leaf]
    omega
  rw [hleaf, hsub]

/-- Cycle 557 standalone triple-leaf `G₁.mul`-direction slice. Product
preserves `G₁` equivalence on `BTree.node [leaf, leaf, leaf]`, whose order
is four. -/
theorem product_congr_node_triple_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (hτ : (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]).order ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
      = (q'.product r').bSeriesHom
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) := by
  rw [QuotEquiv.bSeriesHom_product_node_triple_leaf,
      QuotEquiv.bSeriesHom_product_node_triple_leaf]
  have hp4 : 4 ≤ p := by
    simpa [BTree.order_node, List.foldr] using hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
        = q'.bSeriesHom
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) :=
    hq (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) hτ
  rw [hnode, hleaf]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  have hsub :
      r.bSeriesHom
          (BTree.node (List.replicate (tripleLeafChoiceCount k) BTree.leaf))
        = r'.bSeriesHom
          (BTree.node
            (List.replicate (tripleLeafChoiceCount k) BTree.leaf)) := by
    apply hr
    rw [order_node_replicate_leaf]
    have hcount := tripleLeafChoiceCount_sum k
    omega
  rw [hsub]

/-- Order of an all-empty-node node:
`(BTree.node (List.replicate n (BTree.node []))).order = n + 1`.
Each empty-children node has the same order as a leaf (= 1), so the
foldr sum collapses identically to the all-leaves case. -/
private theorem order_node_replicate_node_nil (n : ℕ) :
    (BTree.node (List.replicate n (BTree.node []))).order = n + 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [BTree.order_node, List.foldr]
    have ihrw : (BTree.node (List.replicate m (BTree.node []))).order
        = m + 1 := ih
    simp only [BTree.order_node] at ihrw
    have hnode_nil : (BTree.node []).order = 1 := by simp
    omega

/-- Cycle 544 third tracked `G1.mul`-direction well-definedness deliverable:
parametric in `n`, product preserves `G₁` equivalence on every all-empty-node
tree `BTree.node (List.replicate n (BTree.node []))` whose order is at most
`p`. Dual of `product_congr_node_replicate_leaf`. -/
theorem product_congr_node_replicate_node_nil
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (n : ℕ) (hn : n + 1 ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node (List.replicate n (BTree.node [])))
      = (q'.product r').bSeriesHom
        (BTree.node (List.replicate n (BTree.node []))) := by
  rw [QuotEquiv.bSeriesHom_product_node_replicate_node_nil,
      QuotEquiv.bSeriesHom_product_node_replicate_node_nil]
  have hnode_nil : q.bSeriesHom (BTree.node [])
      = q'.bSeriesHom (BTree.node []) := by
    apply hq
    have : (BTree.node []).order = 1 := by simp
    rw [this]; omega
  have hnode_n :
      q.bSeriesHom (BTree.node (List.replicate n (BTree.node [])))
        = q'.bSeriesHom (BTree.node (List.replicate n (BTree.node []))) := by
    apply hq; rw [order_node_replicate_node_nil]; omega
  rw [hnode_n]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S _
  have hS : S.card ≤ n := by
    have hmem : S ⊆ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_powerset.mp ‹S ∈ _›
    have := Finset.card_le_card hmem
    simp at this
    exact this
  have hsub :
      r.bSeriesHom
          (BTree.node (List.replicate (n - S.card) (BTree.node [])))
        = r'.bSeriesHom
          (BTree.node (List.replicate (n - S.card) (BTree.node []))) := by
    apply hr
    rw [order_node_replicate_node_nil]
    omega
  rw [hnode_nil, hsub]

/-- Order of an all-singleton-leaf node:
`(BTree.node (List.replicate n (BTree.node [BTree.leaf]))).order =
1 + 2 * n`. Each child contributes order 2. -/
private theorem order_node_replicate_singleton_leaf (n : ℕ) :
    (BTree.node (List.replicate n (BTree.node [BTree.leaf]))).order
      = 1 + 2 * n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [BTree.order_node, List.foldr]
    have htail :
        List.foldr (fun t n => t.order + n) 0
          (List.replicate m (BTree.node [BTree.leaf])) = 2 * m := by
      simp only [BTree.order_node] at ih
      omega
    rw [htail]
    simp
    omega

/-- Order of a mixed node with `a` leaf children followed by `b`
singleton-leaf children. This is the kept-side order accounting for the
cycle 547 nested powerset closed form. -/
private theorem order_node_replicate_leaf_append_replicate_singleton_leaf
    (a b : ℕ) :
    (BTree.node
      (List.replicate a BTree.leaf ++
        List.replicate b (BTree.node [BTree.leaf]))).order
      = 1 + a + 2 * b := by
  induction a with
  | zero =>
    have h := order_node_replicate_singleton_leaf b
    simp only [BTree.order_node] at h
    simp
    omega
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [BTree.order_node, List.foldr, BTree.order_leaf]
    simp only [BTree.order_node] at ih
    omega

/-- Cycle 559 standalone four-child mixed leaf/singleton-leaf `G₁.mul`
direction slice. Product preserves `G₁` equivalence on the concrete tree
`tQuadMixed`, whose order is six. -/
theorem product_congr_node_quadMixed
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (hτ : tQuadMixed.order ≤ p) :
    (q.product r).bSeriesHom tQuadMixed
      = (q'.product r').bSeriesHom tQuadMixed := by
  rw [QuotEquiv.bSeriesHom_product_node_quadMixed,
      QuotEquiv.bSeriesHom_product_node_quadMixed]
  have hp6 : 6 ≤ p := by
    simpa [tQuadMixed, BTree.order_node, List.foldr] using hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hsingleton :
      q.bSeriesHom (BTree.node [BTree.leaf])
        = q'.bSeriesHom (BTree.node [BTree.leaf]) := by
    apply hq
    simp [BTree.order_node, List.foldr]
    omega
  have hnode :
      q.bSeriesHom tQuadMixed = q'.bSeriesHom tQuadMixed :=
    hq tQuadMixed hτ
  rw [hnode, hleaf, hsingleton]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro h _
  have hsub :
      r.bSeriesHom (quadMixedChoiceTree k h)
        = r'.bSeriesHom (quadMixedChoiceTree k h) := by
    apply hr
    rw [quadMixedChoiceTree,
      order_node_replicate_leaf_append_replicate_singleton_leaf]
    have hcount := tripleLeafChoiceCount_sum k
    fin_cases h <;>
      simp [quadMixedSingletonLeafCount, quadMixedSingletonNodeCount] <;>
      omega
  rw [hsub]

/-- Cycle 560 standalone (2-leaf, 2-singleton-leaf) four-children mixed
`G₁.mul` direction slice. Product preserves `G₁` equivalence on the concrete
tree `tQuadMixedTwoTwo`, whose order is seven. -/
theorem product_congr_node_quadMixedTwoTwo
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (hτ : tQuadMixedTwoTwo.order ≤ p) :
    (q.product r).bSeriesHom tQuadMixedTwoTwo
      = (q'.product r').bSeriesHom tQuadMixedTwoTwo := by
  rw [QuotEquiv.bSeriesHom_product_node_quadMixedTwoTwo,
      QuotEquiv.bSeriesHom_product_node_quadMixedTwoTwo]
  have hp7 : 7 ≤ p := by
    simpa [tQuadMixedTwoTwo, BTree.order_node, List.foldr] using hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hsingleton :
      q.bSeriesHom (BTree.node [BTree.leaf])
        = q'.bSeriesHom (BTree.node [BTree.leaf]) := by
    apply hq
    simp [BTree.order_node, List.foldr]
    omega
  have hnode :
      q.bSeriesHom tQuadMixedTwoTwo = q'.bSeriesHom tQuadMixedTwoTwo :=
    hq tQuadMixedTwoTwo hτ
  rw [hnode, hleaf, hsingleton]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro h₁ _
  refine Finset.sum_congr rfl ?_
  intro h₂ _
  have hsub :
      r.bSeriesHom (quadMixedTwoTwoChoiceTree k h₁ h₂)
        = r'.bSeriesHom (quadMixedTwoTwoChoiceTree k h₁ h₂) := by
    apply hr
    rw [quadMixedTwoTwoChoiceTree,
      order_node_replicate_leaf_append_replicate_singleton_leaf]
    have hcount := quadMixedTwoTwoLeafChoiceCount_sum k
    fin_cases h₁ <;> fin_cases h₂ <;>
      simp [quadMixedSingletonLeafCount, quadMixedSingletonNodeCount] <;>
      omega
  rw [hsub]

/-- Cycle 561 standalone (1-leaf, 3-singleton-leaf) four-children mixed
`G₁.mul` direction slice. Product preserves `G₁` equivalence on the concrete
tree `tQuadMixedOneThree`, whose order is eight. -/
theorem product_congr_node_quadMixedOneThree
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (hτ : tQuadMixedOneThree.order ≤ p) :
    (q.product r).bSeriesHom tQuadMixedOneThree
      = (q'.product r').bSeriesHom tQuadMixedOneThree := by
  rw [QuotEquiv.bSeriesHom_product_node_quadMixedOneThree,
      QuotEquiv.bSeriesHom_product_node_quadMixedOneThree]
  have hp8 : 8 ≤ p := by
    simpa [tQuadMixedOneThree, BTree.order_node, List.foldr] using hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hsingleton :
      q.bSeriesHom (BTree.node [BTree.leaf])
        = q'.bSeriesHom (BTree.node [BTree.leaf]) := by
    apply hq
    simp [BTree.order_node, List.foldr]
    omega
  have hnode :
      q.bSeriesHom tQuadMixedOneThree
        = q'.bSeriesHom tQuadMixedOneThree :=
    hq tQuadMixedOneThree hτ
  rw [hnode, hleaf, hsingleton]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro h₁ _
  refine Finset.sum_congr rfl ?_
  intro h₂ _
  refine Finset.sum_congr rfl ?_
  intro h₃ _
  have hsub :
      r.bSeriesHom (quadMixedOneThreeChoiceTree k h₁ h₂ h₃)
        = r'.bSeriesHom (quadMixedOneThreeChoiceTree k h₁ h₂ h₃) := by
    apply hr
    rw [quadMixedOneThreeChoiceTree,
      order_node_replicate_leaf_append_replicate_singleton_leaf]
    fin_cases k <;> fin_cases h₁ <;> fin_cases h₂ <;> fin_cases h₃ <;>
      simp [quadMixedSingletonLeafCount, quadMixedSingletonNodeCount,
        quadMixedOneThreeLeafChoiceCount] <;>
      omega
  rw [hsub]

/-- Cycle 547 fifth tracked `G1.mul`-direction well-definedness
deliverable: product preserves `G₁` equivalence on every node whose root
children are all `BTree.node [BTree.leaf]`, with the order bound
`1 + 2 * n ≤ p`. -/
theorem product_congr_node_replicate_singleton_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (n : ℕ) (hn : 1 + 2 * n ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node (List.replicate n (BTree.node [BTree.leaf]))) := by
  rw [QuotEquiv.bSeriesHom_product_node_replicate_singleton_leaf,
      QuotEquiv.bSeriesHom_product_node_replicate_singleton_leaf]
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode_n :
      q.bSeriesHom
          (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
        = q'.bSeriesHom
          (BTree.node (List.replicate n (BTree.node [BTree.leaf]))) := by
    apply hq
    rw [order_node_replicate_singleton_leaf]
    omega
  rw [hnode_n]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S hS_mem
  have hS : S.card ≤ n := by
    have hmem : S ⊆ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_powerset.mp hS_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hsingleton_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf])) ^ S.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf])) ^ S.card := by
    by_cases hzero : S.card = 0
    · simp [hzero]
    · have hnpos : 0 < n := by
        have hSpos : 0 < S.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le hSpos hS
      have hp2 : 2 ≤ p := by omega
      have hsingleton :
          q.bSeriesHom (BTree.node [BTree.leaf])
            = q'.bSeriesHom (BTree.node [BTree.leaf]) := by
        apply hq
        have horder : (BTree.node [BTree.leaf]).order = 2 := by simp
        rw [horder]
        exact hp2
      rw [hsingleton]
  rw [hsingleton_pow]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro T hT_mem
  have hT : T.card ≤ (Sᶜ : Finset (Fin n)).card := by
    have hmem : T ⊆ Sᶜ := Finset.mem_powerset.mp hT_mem
    exact Finset.card_le_card hmem
  have hcomp : (Sᶜ : Finset (Fin n)).card = n - S.card := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin]
  have hmixed :
      r.bSeriesHom
          (BTree.node
            (List.replicate T.card BTree.leaf ++
              List.replicate ((Sᶜ : Finset (Fin n)).card - T.card)
                (BTree.node [BTree.leaf])))
        = r'.bSeriesHom
          (BTree.node
            (List.replicate T.card BTree.leaf ++
              List.replicate ((Sᶜ : Finset (Fin n)).card - T.card)
                (BTree.node [BTree.leaf]))) := by
    apply hr
    rw [order_node_replicate_leaf_append_replicate_singleton_leaf]
    omega
  rw [hleaf, hmixed]

/-- Sixth tracked `G1.mul`-direction well-definedness deliverable:
product preserves `G₁` equivalence on every node whose root children are
`a` plain leaves followed by `b` singleton-leaf nodes, with order bound
`1 + a + 2 * b ≤ p`. -/
theorem product_congr_node_mixed_leaf_singleton_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (a b : ℕ) (hab : 1 + a + 2 * b ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]))) := by
  rw [QuotEquiv.bSeriesHom_product_node_mixed_leaf_singleton_leaf,
      QuotEquiv.bSeriesHom_product_node_mixed_leaf_singleton_leaf]
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf])))
        = q'.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf]))) := by
    apply hq
    rw [order_node_replicate_leaf_append_replicate_singleton_leaf]
    omega
  rw [hnode]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S_leaf hS_leaf_mem
  have hS_leaf : S_leaf.card ≤ a := by
    have hmem : S_leaf ⊆ (Finset.univ : Finset (Fin a)) :=
      Finset.mem_powerset.mp hS_leaf_mem
    have := Finset.card_le_card hmem
    simpa using this
  refine Finset.sum_congr rfl ?_
  intro S_sl hS_sl_mem
  have hS_sl : S_sl.card ≤ b := by
    have hmem : S_sl ⊆ (Finset.univ : Finset (Fin b)) :=
      Finset.mem_powerset.mp hS_sl_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hsl_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf])) ^ S_sl.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf])) ^ S_sl.card := by
    by_cases hzero : S_sl.card = 0
    · simp [hzero]
    · have hbpos : 0 < b := by
        have : 0 < S_sl.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le this hS_sl
      have hp2 : 2 ≤ p := by omega
      have hsl :
          q.bSeriesHom (BTree.node [BTree.leaf])
            = q'.bSeriesHom (BTree.node [BTree.leaf]) := by
        apply hq
        have horder : (BTree.node [BTree.leaf]).order = 2 := by simp
        rw [horder]
        exact hp2
      rw [hsl]
  rw [hleaf, hsl_pow]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro T hT_mem
  have hT : T.card ≤ (S_slᶜ : Finset (Fin b)).card := by
    have hmem : T ⊆ S_slᶜ := Finset.mem_powerset.mp hT_mem
    exact Finset.card_le_card hmem
  have hcomp : (S_slᶜ : Finset (Fin b)).card = b - S_sl.card := by
    rw [Finset.card_compl]
    simp [Fintype.card_fin]
  have hmixed :
      r.bSeriesHom
          (BTree.node
            (List.replicate (a - S_leaf.card + T.card) BTree.leaf ++
              List.replicate ((S_slᶜ : Finset (Fin b)).card - T.card)
                (BTree.node [BTree.leaf])))
        = r'.bSeriesHom
          (BTree.node
            (List.replicate (a - S_leaf.card + T.card) BTree.leaf ++
              List.replicate ((S_slᶜ : Finset (Fin b)).card - T.card)
                (BTree.node [BTree.leaf]))) := by
    apply hr
    rw [order_node_replicate_leaf_append_replicate_singleton_leaf]
    rw [hcomp] at hT
    omega
  rw [hmixed]

/-- Order of an all-double-leaf node:
`(BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf]))).order =
1 + 3 * n`. -/
private theorem order_node_replicate_double_leaf (n : ℕ) :
    (BTree.node
      (List.replicate n (BTree.node [BTree.leaf, BTree.leaf]))).order
      = 1 + 3 * n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [BTree.order_node, List.foldr]
    have htail :
        List.foldr (fun t n => t.order + n) 0
          (List.replicate m (BTree.node [BTree.leaf, BTree.leaf])) = 3 * m := by
      simp only [BTree.order_node] at ih
      omega
    rw [htail]
    simp
    omega

/-- Order of an all-triple-leaf node:
`(BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf,
BTree.leaf]))).order = 1 + 4 * n`. -/
private theorem order_node_replicate_triple_leaf (n : ℕ) :
    (BTree.node
      (List.replicate n
        (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))).order
      = 1 + 4 * n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [BTree.order_node, List.foldr]
    have htail :
        List.foldr (fun t n => t.order + n) 0
          (List.replicate m
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) = 4 * m := by
      simp only [BTree.order_node] at ih
      omega
    rw [htail]
    simp
    omega

private theorem order_node_replicate_double_leaf_append_replicate_triple_leaf
    (c d : ℕ) :
    (BTree.node
      (List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
        List.replicate d
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))).order
      = 1 + 3 * c + 4 * d := by
  induction c with
  | zero =>
    have h := order_node_replicate_triple_leaf d
    simp only [BTree.order_node] at h
    simp
    omega
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [BTree.order_node, List.foldr]
    have htail :
        List.foldr (fun t n => t.order + n)
          0
          (List.replicate m (BTree.node [BTree.leaf, BTree.leaf]) ++
            List.replicate d
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))
          = 3 * m + 4 * d := by
      simp only [BTree.order_node] at ih
      omega
    rw [htail]
    simp
    omega

private theorem
    order_node_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf
    (b c d : ℕ) :
    (BTree.node
      (List.replicate b (BTree.node [BTree.leaf]) ++
        List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
          List.replicate d
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))).order
      = 1 + 2 * b + 3 * c + 4 * d := by
  induction b with
  | zero =>
    simpa using (order_node_replicate_double_leaf_append_replicate_triple_leaf c d)
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append]
    simp only [BTree.order_node, List.foldr]
    have htail :
        List.foldr (fun t n => t.order + n)
          0
          (List.replicate m (BTree.node [BTree.leaf]) ++
            List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
              List.replicate d
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))
          = 2 * m + 3 * c + 4 * d := by
      simp only [BTree.order_node] at ih
      omega
    rw [htail]
    simp
    omega

private theorem
    order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf
    (a b c d : ℕ) :
    (BTree.node
      (List.replicate a BTree.leaf ++
        List.replicate b (BTree.node [BTree.leaf]) ++
          List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
            List.replicate d
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))).order
      = 1 + a + 2 * b + 3 * c + 4 * d := by
  induction a with
  | zero =>
    simpa using
      (order_node_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf
        b c d)
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append, List.cons_append]
    simp only [BTree.order_node, List.foldr, BTree.order_leaf]
    have htail :
        List.foldr (fun t n => t.order + n)
          0
          (List.replicate m BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf]) ++
                List.replicate d
                  (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))
          = m + 2 * b + 3 * c + 4 * d := by
      simp only [BTree.order_node] at ih
      omega
    rw [htail]
    omega

/-- Order of a mixed node with `a` leaf children followed by `b`
double-leaf children. -/
private theorem order_node_replicate_leaf_append_replicate_double_leaf
    (a b : ℕ) :
    (BTree.node
      (List.replicate a BTree.leaf ++
        List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))).order
      = 1 + a + 3 * b := by
  induction a with
  | zero =>
    have h := order_node_replicate_double_leaf b
    simp only [BTree.order_node] at h
    simp
    omega
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [BTree.order_node, List.foldr, BTree.order_leaf]
    simp only [BTree.order_node] at ih
    omega

private theorem order_node_replicate_singleton_leaf_append_replicate_double_leaf
    (b c : ℕ) :
    (BTree.node
      (List.replicate b (BTree.node [BTree.leaf]) ++
        List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))).order
      = 1 + 2 * b + 3 * c := by
  induction b with
  | zero =>
    simpa using (order_node_replicate_double_leaf c)
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [BTree.order_node, List.foldr]
    have htail :
        List.foldr (fun t n => t.order + n)
          0
          (List.replicate m (BTree.node [BTree.leaf]) ++
            List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))
          = 2 * m + 3 * c := by
      simp only [BTree.order_node] at ih
      omega
    rw [htail]
    simp
    omega

private theorem
    order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf
    (a b c : ℕ) :
    (BTree.node
      (List.replicate a BTree.leaf ++
        List.replicate b (BTree.node [BTree.leaf]) ++
          List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))).order
      = 1 + a + 2 * b + 3 * c := by
  induction a with
  | zero =>
    simpa using
      (order_node_replicate_singleton_leaf_append_replicate_double_leaf b c)
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, List.cons_append]
    simp only [BTree.order_node, List.foldr, BTree.order_leaf]
    have htail :
        List.foldr (fun t n => t.order + n)
          0
          (List.replicate m BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))
          = m + 2 * b + 3 * c := by
      simp only [BTree.order_node] at ih
      omega
    rw [htail]
    omega

private theorem doubleLeafChoiceCount_sum {n : ℕ} (χ : Fin n → Fin 3) :
    doubleLeafChoiceCount χ ⟨0, by decide⟩
      + doubleLeafChoiceCount χ ⟨1, by decide⟩
      + doubleLeafChoiceCount χ ⟨2, by decide⟩ = n := by
  classical
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin 3)))
      (f := χ) (by intro x hx; simp)
  simpa [Fin.sum_univ_three, doubleLeafChoiceCount, Fintype.card_fin] using h.symm

private theorem order_doubleLeafChoiceTree
    {n : ℕ} (aKeep : ℕ) (χ : Fin n → Fin 3) :
    (doubleLeafChoiceTree aKeep χ).order
      = 1 + (aKeep + doubleLeafChoiceCount χ ⟨0, by decide⟩)
          + 2 * doubleLeafChoiceCount χ ⟨1, by decide⟩
          + 3 * doubleLeafChoiceCount χ ⟨2, by decide⟩ := by
  change
    (BTree.node
      (List.replicate (aKeep + doubleLeafChoiceCount χ ⟨0, by decide⟩) BTree.leaf ++
        List.replicate (doubleLeafChoiceCount χ ⟨1, by decide⟩)
          (BTree.node [BTree.leaf]) ++
        List.replicate (doubleLeafChoiceCount χ ⟨2, by decide⟩)
          (BTree.node [BTree.leaf, BTree.leaf]))).order = _
  rw [order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf]

private theorem order_doubleLeafChoiceTree_le
    {n a b p : ℕ} (aKeep : ℕ) (χ : Fin n → Fin 3)
    (haKeep : aKeep ≤ a) (hn : n ≤ b) (hab : 1 + a + 3 * b ≤ p) :
    (doubleLeafChoiceTree aKeep χ).order ≤ p := by
  rw [order_doubleLeafChoiceTree]
  have hsum := doubleLeafChoiceCount_sum χ
  have hweighted :
      doubleLeafChoiceCount χ ⟨0, by decide⟩
        + 2 * doubleLeafChoiceCount χ ⟨1, by decide⟩
        + 3 * doubleLeafChoiceCount χ ⟨2, by decide⟩ ≤ 3 * n := by
    omega
  omega

/-- Cycle 553 mixed leaf / double-leaf `G₁.mul`-direction slice. -/
theorem product_congr_node_mixed_leaf_double_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (a b : ℕ)
    (hτ :
      (BTree.node
        (List.replicate a BTree.leaf ++
          List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))).order ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) := by
  rw [QuotEquiv.bSeriesHom_product_node_mixed_leaf_double_leaf,
      QuotEquiv.bSeriesHom_product_node_mixed_leaf_double_leaf]
  have hab : 1 + a + 3 * b ≤ p := by
    rw [order_node_replicate_leaf_append_replicate_double_leaf] at hτ
    exact hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
        = q'.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) :=
    hq _ hτ
  rw [hnode, hleaf]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S_leaf hS_leaf_mem
  have hS_leaf : S_leaf.card ≤ a := by
    have hmem : S_leaf ⊆ (Finset.univ : Finset (Fin a)) :=
      Finset.mem_powerset.mp hS_leaf_mem
    have := Finset.card_le_card hmem
    simpa using this
  refine Finset.sum_congr rfl ?_
  intro S_dl hS_dl_mem
  have hS_dl : S_dl.card ≤ b := by
    have hmem : S_dl ⊆ (Finset.univ : Finset (Fin b)) :=
      Finset.mem_powerset.mp hS_dl_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hdouble_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card := by
    by_cases hzero : S_dl.card = 0
    · simp [hzero]
    · have hbpos : 0 < b := by
        have : 0 < S_dl.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le this hS_dl
      have hp3 : 3 ≤ p := by omega
      have hdouble :
          q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])
            = q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf]) := by
        apply hq
        have horder : (BTree.node [BTree.leaf, BTree.leaf]).order = 3 := by
          simp [BTree.order_node, List.foldr]
        rw [horder]
        exact hp3
      rw [hdouble]
  rw [hdouble_pow]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro χ _
  have hchoice :
      r.bSeriesHom (doubleLeafChoiceTree (a - S_leaf.card) χ)
        = r'.bSeriesHom (doubleLeafChoiceTree (a - S_leaf.card) χ) := by
    apply hr
    apply order_doubleLeafChoiceTree_le (a := a) (b := b)
    · omega
    · omega
    · exact hab
  rw [hchoice]

/-- Cycle 562 all-double-leaf parametric `G₁.mul`-direction slice. The
root tree `BTree.node (List.replicate n (BTree.node [BTree.leaf,
BTree.leaf]))` has order `1 + 3 * n`. -/
theorem product_congr_node_replicate_double_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (n : ℕ) (hn : 1 + 3 * n ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf]))) := by
  rw [QuotEquiv.bSeriesHom_product_node_replicate_double_leaf,
      QuotEquiv.bSeriesHom_product_node_replicate_double_leaf]
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom
          (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf])))
        = q'.bSeriesHom
          (BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf]))) := by
    apply hq
    rw [order_node_replicate_double_leaf]
    exact hn
  rw [hnode, hleaf]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S hS_mem
  have hS : S.card ≤ n := by
    have hmem : S ⊆ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_powerset.mp hS_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hdouble_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S.card := by
    by_cases hzero : S.card = 0
    · simp [hzero]
    · have hnpos : 0 < n := by
        have : 0 < S.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le this hS
      have hp3 : 3 ≤ p := by omega
      have hdouble :
          q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])
            = q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf]) := by
        apply hq
        have horder : (BTree.node [BTree.leaf, BTree.leaf]).order = 3 := by
          simp [BTree.order_node, List.foldr]
        rw [horder]
        exact hp3
      rw [hdouble]
  rw [hdouble_pow]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro χ _
  have hchoice :
      r.bSeriesHom (doubleLeafChoiceTree 0 χ)
        = r'.bSeriesHom (doubleLeafChoiceTree 0 χ) := by
    apply hr
    apply order_doubleLeafChoiceTree_le (a := 0) (b := n)
    · exact Nat.zero_le _
    · -- (n - S.card) ≤ n
      exact Nat.sub_le _ _
    · omega
  rw [hchoice]

/-- The four choice fibers for the triple-leaf residual shapes partition the
kept root children. -/
private theorem tripleLeafRootChoiceCount_sum {n : ℕ}
    (χ : Fin n → Fin 4) :
    tripleLeafRootChoiceCount χ ⟨0, by decide⟩
      + tripleLeafRootChoiceCount χ ⟨1, by decide⟩
      + tripleLeafRootChoiceCount χ ⟨2, by decide⟩
      + tripleLeafRootChoiceCount χ ⟨3, by decide⟩ = n := by
  classical
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin 4)))
      (f := χ) (by intro x hx; simp)
  simpa [Fin.sum_univ_four, tripleLeafRootChoiceCount, Fintype.card_fin] using h.symm

private theorem order_tripleLeafChoiceTree
    {n : ℕ} (χ : Fin n → Fin 4) :
    (tripleLeafChoiceTree χ).order
      = 1 + tripleLeafRootChoiceCount χ ⟨3, by decide⟩
          + 2 * tripleLeafRootChoiceCount χ ⟨2, by decide⟩
          + 3 * tripleLeafRootChoiceCount χ ⟨1, by decide⟩
          + 4 * tripleLeafRootChoiceCount χ ⟨0, by decide⟩ := by
  change
    (BTree.node
      (List.replicate (tripleLeafRootChoiceCount χ ⟨3, by decide⟩)
          BTree.leaf ++
        List.replicate (tripleLeafRootChoiceCount χ ⟨2, by decide⟩)
          (BTree.node [BTree.leaf]) ++
        List.replicate (tripleLeafRootChoiceCount χ ⟨1, by decide⟩)
          (BTree.node [BTree.leaf, BTree.leaf]) ++
        List.replicate (tripleLeafRootChoiceCount χ ⟨0, by decide⟩)
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))).order = _
  rw [order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf]

private theorem order_tripleLeafChoiceTree_le
    {n p : ℕ} (χ : Fin n → Fin 4) (hn : 1 + 4 * n ≤ p) :
    (tripleLeafChoiceTree χ).order ≤ p := by
  rw [order_tripleLeafChoiceTree]
  have hsum := tripleLeafRootChoiceCount_sum χ
  have hweighted :
      tripleLeafRootChoiceCount χ ⟨3, by decide⟩
        + 2 * tripleLeafRootChoiceCount χ ⟨2, by decide⟩
        + 3 * tripleLeafRootChoiceCount χ ⟨1, by decide⟩
        + 4 * tripleLeafRootChoiceCount χ ⟨0, by decide⟩ ≤ 4 * n := by
    omega
  omega

/-- Cycle 563 all-triple-leaf parametric `G₁.mul`-direction slice. The
root tree `BTree.node (List.replicate n (BTree.node [BTree.leaf,
BTree.leaf, BTree.leaf]))` has order `1 + 4 * n`. -/
theorem product_congr_node_replicate_triple_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (n : ℕ) (hn : 1 + 4 * n ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node
          (List.replicate n
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) := by
  rw [QuotEquiv.bSeriesHom_product_node_replicate_triple_leaf,
      QuotEquiv.bSeriesHom_product_node_replicate_triple_leaf]
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom
          (BTree.node
            (List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
        = q'.bSeriesHom
          (BTree.node
            (List.replicate n
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) := by
    apply hq
    rw [order_node_replicate_triple_leaf]
    exact hn
  rw [hnode, hleaf]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S hS_mem
  have hS : S.card ≤ n := by
    have hmem : S ⊆ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_powerset.mp hS_mem
    have := Finset.card_le_card hmem
    simpa using this
  have htriple_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^
          S.card := by
    by_cases hzero : S.card = 0
    · simp [hzero]
    · have hnpos : 0 < n := by
        have : 0 < S.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le this hS
      have hp4 : 4 ≤ p := by omega
      have htriple :
          q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
            = q'.bSeriesHom
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) := by
        apply hq
        have horder :
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]).order = 4 := by
          simp [BTree.order_node, List.foldr]
        rw [horder]
        exact hp4
      rw [htriple]
  rw [htriple_pow]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro χ _
  have hchoice :
      r.bSeriesHom (tripleLeafChoiceTree χ)
        = r'.bSeriesHom (tripleLeafChoiceTree χ) := by
    apply hr
    apply order_tripleLeafChoiceTree_le
    omega
  rw [hchoice]

private theorem order_node_replicate_leaf_append_replicate_triple_leaf
    (a b : ℕ) :
    (BTree.node
      (List.replicate a BTree.leaf ++
        List.replicate b
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))).order
      = 1 + a + 4 * b := by
  simpa using
    (order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf
      a 0 0 b)

private theorem order_mixedLeafTripleLeafChoiceTree
    {n : ℕ} (aKeep : ℕ) (χ : Fin n → Fin 4) :
    (mixedLeafTripleLeafChoiceTree aKeep χ).order
      = 1 + (aKeep + tripleLeafRootChoiceCount χ ⟨3, by decide⟩)
          + 2 * tripleLeafRootChoiceCount χ ⟨2, by decide⟩
          + 3 * tripleLeafRootChoiceCount χ ⟨1, by decide⟩
          + 4 * tripleLeafRootChoiceCount χ ⟨0, by decide⟩ := by
  change
    (BTree.node
      (List.replicate
          (aKeep + tripleLeafRootChoiceCount χ ⟨3, by decide⟩) BTree.leaf ++
        List.replicate (tripleLeafRootChoiceCount χ ⟨2, by decide⟩)
          (BTree.node [BTree.leaf]) ++
        List.replicate (tripleLeafRootChoiceCount χ ⟨1, by decide⟩)
          (BTree.node [BTree.leaf, BTree.leaf]) ++
        List.replicate (tripleLeafRootChoiceCount χ ⟨0, by decide⟩)
          (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))).order = _
  rw [order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf]

private theorem order_mixedLeafTripleLeafChoiceTree_le
    {n a b p : ℕ} (aKeep : ℕ) (χ : Fin n → Fin 4)
    (haKeep : aKeep ≤ a) (hn : n ≤ b) (hab : 1 + a + 4 * b ≤ p) :
    (mixedLeafTripleLeafChoiceTree aKeep χ).order ≤ p := by
  rw [order_mixedLeafTripleLeafChoiceTree]
  have hsum := tripleLeafRootChoiceCount_sum χ
  have hweighted :
      tripleLeafRootChoiceCount χ ⟨3, by decide⟩
        + 2 * tripleLeafRootChoiceCount χ ⟨2, by decide⟩
        + 3 * tripleLeafRootChoiceCount χ ⟨1, by decide⟩
        + 4 * tripleLeafRootChoiceCount χ ⟨0, by decide⟩ ≤ 4 * n := by
    omega
  omega

/-- Cycle 565 mixed leaf / triple-leaf parametric `G₁.mul`-direction slice.
The root tree has order `1 + a + 4 * b`. -/
theorem product_congr_node_replicate_mixed_leaf_triple_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (a b : ℕ)
    (hτ :
      (BTree.node
        (List.replicate a BTree.leaf ++
          List.replicate b
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))).order ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) := by
  rw [QuotEquiv.bSeriesHom_product_node_replicate_mixed_leaf_triple_leaf,
      QuotEquiv.bSeriesHom_product_node_replicate_mixed_leaf_triple_leaf]
  have hab : 1 + a + 4 * b ≤ p := by
    rw [order_node_replicate_leaf_append_replicate_triple_leaf] at hτ
    exact hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])))
        = q'.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b
                (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))) :=
    hq _ hτ
  rw [hnode, hleaf]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S_leaf hS_leaf_mem
  have hS_leaf : S_leaf.card ≤ a := by
    have hmem : S_leaf ⊆ (Finset.univ : Finset (Fin a)) :=
      Finset.mem_powerset.mp hS_leaf_mem
    have := Finset.card_le_card hmem
    simpa using this
  refine Finset.sum_congr rfl ?_
  intro S_tl hS_tl_mem
  have hS_tl : S_tl.card ≤ b := by
    have hmem : S_tl ⊆ (Finset.univ : Finset (Fin b)) :=
      Finset.mem_powerset.mp hS_tl_mem
    have := Finset.card_le_card hmem
    simpa using this
  have htriple_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^ S_tl.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])) ^
          S_tl.card := by
    by_cases hzero : S_tl.card = 0
    · simp [hzero]
    · have hbpos : 0 < b := by
        have : 0 < S_tl.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le this hS_tl
      have hp4 : 4 ≤ p := by omega
      have htriple :
          q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf])
            = q'.bSeriesHom
              (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]) := by
        apply hq
        have horder :
            (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]).order = 4 := by
          simp [BTree.order_node, List.foldr]
        rw [horder]
        exact hp4
      rw [htriple]
  rw [htriple_pow]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro χ _
  have hchoice :
      r.bSeriesHom (mixedLeafTripleLeafChoiceTree (a - S_leaf.card) χ)
        = r'.bSeriesHom
          (mixedLeafTripleLeafChoiceTree (a - S_leaf.card) χ) := by
    apply hr
    apply order_mixedLeafTripleLeafChoiceTree_le (a := a) (b := b)
    · omega
    · exact Nat.sub_le _ _
    · exact hab
  rw [hchoice]

/-- Cycle 554 mixed singleton-leaf / double-leaf `G₁.mul`-direction slice.
Each kept singleton-leaf root child contributes a `Fin 2` inner choice and
each kept double-leaf contributes a `Fin 3` inner choice. -/
theorem product_congr_node_mixed_singleton_leaf_double_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (a b : ℕ)
    (hτ :
      (BTree.node
        (List.replicate a (BTree.node [BTree.leaf]) ++
          List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))).order ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a (BTree.node [BTree.leaf]) ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node
          (List.replicate a (BTree.node [BTree.leaf]) ++
            List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) := by
  rw [QuotEquiv.bSeriesHom_product_node_mixed_singleton_leaf_double_leaf,
      QuotEquiv.bSeriesHom_product_node_mixed_singleton_leaf_double_leaf]
  have hab : 1 + 2 * a + 3 * b ≤ p := by
    rw [order_node_replicate_singleton_leaf_append_replicate_double_leaf] at hτ
    exact hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom
          (BTree.node
            (List.replicate a (BTree.node [BTree.leaf]) ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf])))
        = q'.bSeriesHom
          (BTree.node
            (List.replicate a (BTree.node [BTree.leaf]) ++
              List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))) :=
    hq _ hτ
  rw [hnode, hleaf]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S_sl hS_sl_mem
  have hS_sl : S_sl.card ≤ a := by
    have hmem : S_sl ⊆ (Finset.univ : Finset (Fin a)) :=
      Finset.mem_powerset.mp hS_sl_mem
    have := Finset.card_le_card hmem
    simpa using this
  refine Finset.sum_congr rfl ?_
  intro S_dl hS_dl_mem
  have hS_dl : S_dl.card ≤ b := by
    have hmem : S_dl ⊆ (Finset.univ : Finset (Fin b)) :=
      Finset.mem_powerset.mp hS_dl_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hsl_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf])) ^ S_sl.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf])) ^ S_sl.card := by
    by_cases hzero : S_sl.card = 0
    · simp [hzero]
    · have hapos : 0 < a := by
        have : 0 < S_sl.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le this hS_sl
      have hp2 : 2 ≤ p := by omega
      have hsl :
          q.bSeriesHom (BTree.node [BTree.leaf])
            = q'.bSeriesHom (BTree.node [BTree.leaf]) := by
        apply hq
        have horder : (BTree.node [BTree.leaf]).order = 2 := by
          simp [BTree.order_node, List.foldr]
        rw [horder]
        exact hp2
      rw [hsl]
  rw [hsl_pow]
  have hdl_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card := by
    by_cases hzero : S_dl.card = 0
    · simp [hzero]
    · have hbpos : 0 < b := by
        have : 0 < S_dl.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le this hS_dl
      have hp3 : 3 ≤ p := by omega
      have hdl :
          q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])
            = q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf]) := by
        apply hq
        have horder : (BTree.node [BTree.leaf, BTree.leaf]).order = 3 := by
          simp [BTree.order_node, List.foldr]
        rw [horder]
        exact hp3
      rw [hdl]
  rw [hdl_pow]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro T hT_mem
  have hT_card_le : T.card ≤ (S_slᶜ : Finset (Fin a)).card := by
    have hmem : T ⊆ (S_slᶜ : Finset (Fin a)) :=
      Finset.mem_powerset.mp hT_mem
    exact Finset.card_le_card hmem
  have hSslc_le : (S_slᶜ : Finset (Fin a)).card ≤ a := by
    have : (S_slᶜ : Finset (Fin a)).card ≤ (Finset.univ : Finset (Fin a)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa using this
  have hT_le_a : T.card ≤ a := le_trans hT_card_le hSslc_le
  congr 1
  refine Finset.sum_congr rfl ?_
  intro χ _
  have hsum_χ := doubleLeafChoiceCount_sum χ
  have hchoice :
      r.bSeriesHom
          (BTree.node
            (List.replicate
                (T.card + doubleLeafChoiceCount χ ⟨0, by decide⟩)
                BTree.leaf ++
              List.replicate
                  (((S_slᶜ : Finset (Fin a)).card - T.card) +
                    doubleLeafChoiceCount χ ⟨1, by decide⟩)
                  (BTree.node [BTree.leaf]) ++
                List.replicate
                  (doubleLeafChoiceCount χ ⟨2, by decide⟩)
                  (BTree.node [BTree.leaf, BTree.leaf])))
        = r'.bSeriesHom
          (BTree.node
            (List.replicate
                (T.card + doubleLeafChoiceCount χ ⟨0, by decide⟩)
                BTree.leaf ++
              List.replicate
                  (((S_slᶜ : Finset (Fin a)).card - T.card) +
                    doubleLeafChoiceCount χ ⟨1, by decide⟩)
                  (BTree.node [BTree.leaf]) ++
                List.replicate
                  (doubleLeafChoiceCount χ ⟨2, by decide⟩)
                  (BTree.node [BTree.leaf, BTree.leaf]))) := by
    apply hr
    rw [order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf]
    omega
  rw [hchoice]

/-- Cycle 556 mixed leaf / singleton-leaf / double-leaf `G₁.mul`-direction
slice. Each kept leaf at the root contributes only via cut/keep; each kept
singleton-leaf has a `Fin 2` inner choice and each kept double-leaf has a
`Fin 3` inner choice. -/
theorem product_congr_node_mixed_leaf_singleton_leaf_double_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (a b c : ℕ)
    (hτ :
      (BTree.node
        (List.replicate a BTree.leaf ++
          List.replicate b (BTree.node [BTree.leaf]) ++
            List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))).order ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf])))
      = (q'.product r').bSeriesHom
        (BTree.node
          (List.replicate a BTree.leaf ++
            List.replicate b (BTree.node [BTree.leaf]) ++
              List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))) := by
  rw [QuotEquiv.bSeriesHom_product_node_mixed_leaf_singleton_leaf_double_leaf,
      QuotEquiv.bSeriesHom_product_node_mixed_leaf_singleton_leaf_double_leaf]
  have habc : 1 + a + 2 * b + 3 * c ≤ p := by
    rw [order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf]
      at hτ
    exact hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf]) ++
                List.replicate c (BTree.node [BTree.leaf, BTree.leaf])))
        = q'.bSeriesHom
          (BTree.node
            (List.replicate a BTree.leaf ++
              List.replicate b (BTree.node [BTree.leaf]) ++
                List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))) :=
    hq _ hτ
  rw [hnode, hleaf]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S_l hS_l_mem
  have hS_l : S_l.card ≤ a := by
    have hmem : S_l ⊆ (Finset.univ : Finset (Fin a)) :=
      Finset.mem_powerset.mp hS_l_mem
    have := Finset.card_le_card hmem
    simpa using this
  refine Finset.sum_congr rfl ?_
  intro S_sl hS_sl_mem
  have hS_sl : S_sl.card ≤ b := by
    have hmem : S_sl ⊆ (Finset.univ : Finset (Fin b)) :=
      Finset.mem_powerset.mp hS_sl_mem
    have := Finset.card_le_card hmem
    simpa using this
  refine Finset.sum_congr rfl ?_
  intro S_dl hS_dl_mem
  have hS_dl : S_dl.card ≤ c := by
    have hmem : S_dl ⊆ (Finset.univ : Finset (Fin c)) :=
      Finset.mem_powerset.mp hS_dl_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hsl_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf])) ^ S_sl.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf])) ^ S_sl.card := by
    by_cases hzero : S_sl.card = 0
    · simp [hzero]
    · have hbpos : 0 < b := by
        have : 0 < S_sl.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le this hS_sl
      have hp2 : 2 ≤ p := by omega
      have hsl :
          q.bSeriesHom (BTree.node [BTree.leaf])
            = q'.bSeriesHom (BTree.node [BTree.leaf]) := by
        apply hq
        have horder : (BTree.node [BTree.leaf]).order = 2 := by
          simp [BTree.order_node, List.foldr]
        rw [horder]
        exact hp2
      rw [hsl]
  rw [hsl_pow]
  have hdl_pow :
      (q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card
        = (q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])) ^ S_dl.card := by
    by_cases hzero : S_dl.card = 0
    · simp [hzero]
    · have hcpos : 0 < c := by
        have : 0 < S_dl.card := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le this hS_dl
      have hp3 : 3 ≤ p := by omega
      have hdl :
          q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf])
            = q'.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf]) := by
        apply hq
        have horder : (BTree.node [BTree.leaf, BTree.leaf]).order = 3 := by
          simp [BTree.order_node, List.foldr]
        rw [horder]
        exact hp3
      rw [hdl]
  rw [hdl_pow]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro T hT_mem
  have hT_card_le : T.card ≤ (S_slᶜ : Finset (Fin b)).card := by
    have hmem : T ⊆ (S_slᶜ : Finset (Fin b)) :=
      Finset.mem_powerset.mp hT_mem
    exact Finset.card_le_card hmem
  have hSslc_le : (S_slᶜ : Finset (Fin b)).card ≤ b := by
    have : (S_slᶜ : Finset (Fin b)).card ≤ (Finset.univ : Finset (Fin b)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa using this
  have hT_le_b : T.card ≤ b := le_trans hT_card_le hSslc_le
  congr 1
  refine Finset.sum_congr rfl ?_
  intro χ _
  have hsum_χ := doubleLeafChoiceCount_sum χ
  have hchoice :
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
                  (BTree.node [BTree.leaf, BTree.leaf])))
        = r'.bSeriesHom
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
                  (BTree.node [BTree.leaf, BTree.leaf]))) := by
    apply hr
    rw [order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf]
    omega
  rw [hchoice]

/-- Cycle 545 fallback slice: product preserves `G₁` equivalence on
`BTree.node [BTree.leaf, BTree.node []]` when that tree has order at most
`p`. -/
theorem product_congr_node_leaf_node_nil
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (hτ : (BTree.node [BTree.leaf, BTree.node []]).order ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node [BTree.leaf, BTree.node []])
      = (q'.product r').bSeriesHom
        (BTree.node [BTree.leaf, BTree.node []]) := by
  rw [QuotEquiv.bSeriesHom_product_node_leaf_node_nil,
      QuotEquiv.bSeriesHom_product_node_leaf_node_nil]
  have hp3 : 3 ≤ p := by
    simpa [BTree.order_node, List.foldr] using hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom (BTree.node [BTree.leaf, BTree.node []])
        = q'.bSeriesHom (BTree.node [BTree.leaf, BTree.node []]) :=
    hq (BTree.node [BTree.leaf, BTree.node []]) hτ
  rw [hnode]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S hS_mem
  have hS : S.card ≤ 2 := by
    have hmem : S ⊆ (Finset.univ : Finset (Fin 2)) :=
      Finset.mem_powerset.mp hS_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hsub :
      r.bSeriesHom (BTree.node (List.replicate (2 - S.card) BTree.leaf))
        = r'.bSeriesHom
          (BTree.node (List.replicate (2 - S.card) BTree.leaf)) := by
    apply hr
    rw [order_node_replicate_leaf]
    omega
  rw [hleaf, hsub]

/-- Cycle 545 fallback slice: product preserves `G₁` equivalence on
`BTree.node [BTree.node [], BTree.leaf]` when that tree has order at most
`p`. -/
theorem product_congr_node_node_nil_leaf
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (hτ : (BTree.node [BTree.node [], BTree.leaf]).order ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node [BTree.node [], BTree.leaf])
      = (q'.product r').bSeriesHom
        (BTree.node [BTree.node [], BTree.leaf]) := by
  rw [QuotEquiv.bSeriesHom_product_node_node_nil_leaf,
      QuotEquiv.bSeriesHom_product_node_node_nil_leaf]
  have hp3 : 3 ≤ p := by
    simpa [BTree.order_node, List.foldr] using hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom (BTree.node [BTree.node [], BTree.leaf])
        = q'.bSeriesHom (BTree.node [BTree.node [], BTree.leaf]) :=
    hq (BTree.node [BTree.node [], BTree.leaf]) hτ
  rw [hnode]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S hS_mem
  have hS : S.card ≤ 2 := by
    have hmem : S ⊆ (Finset.univ : Finset (Fin 2)) :=
      Finset.mem_powerset.mp hS_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hsub :
      r.bSeriesHom (BTree.node (List.replicate (2 - S.card) BTree.leaf))
        = r'.bSeriesHom
          (BTree.node (List.replicate (2 - S.card) BTree.leaf)) := by
    apply hr
    rw [order_node_replicate_leaf]
    omega
  rw [hleaf, hsub]

/-- Cycle 545 fallback slice: product preserves `G₁` equivalence on
`BTree.node [BTree.leaf, BTree.leaf, BTree.node []]` when that tree has
order at most `p`. -/
theorem product_congr_node_leaf_leaf_node_nil
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (hτ :
      (BTree.node [BTree.leaf, BTree.leaf, BTree.node []]).order ≤ p) :
    (q.product r).bSeriesHom
        (BTree.node [BTree.leaf, BTree.leaf, BTree.node []])
      = (q'.product r').bSeriesHom
        (BTree.node [BTree.leaf, BTree.leaf, BTree.node []]) := by
  rw [QuotEquiv.bSeriesHom_product_node_leaf_leaf_node_nil,
      QuotEquiv.bSeriesHom_product_node_leaf_leaf_node_nil]
  have hp4 : 4 ≤ p := by
    simpa [BTree.order_node, List.foldr] using hτ
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq
    rw [BTree.order_leaf]
    omega
  have hnode :
      q.bSeriesHom (BTree.node [BTree.leaf, BTree.leaf, BTree.node []])
        = q'.bSeriesHom
          (BTree.node [BTree.leaf, BTree.leaf, BTree.node []]) :=
    hq (BTree.node [BTree.leaf, BTree.leaf, BTree.node []]) hτ
  rw [hnode]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S hS_mem
  have hS : S.card ≤ 3 := by
    have hmem : S ⊆ (Finset.univ : Finset (Fin 3)) :=
      Finset.mem_powerset.mp hS_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hsub :
      r.bSeriesHom (BTree.node (List.replicate (3 - S.card) BTree.leaf))
        = r'.bSeriesHom
          (BTree.node (List.replicate (3 - S.card) BTree.leaf)) := by
    apply hr
    rw [order_node_replicate_leaf]
    omega
  rw [hleaf, hsub]

/-- Order of a node whose every child is `BTree.leaf` or `BTree.node []`:
each trivial child contributes order `1`, so the foldr sum equals
`children.length`. -/
private theorem order_node_trivial_children {children : List BTree}
    (hTriv : ∀ p : Fin children.length,
        children.get p = BTree.leaf ∨ children.get p = BTree.node []) :
    (BTree.node children).order = children.length + 1 := by
  induction children with
  | nil => simp
  | cons c cs ih =>
    have hc : c = BTree.leaf ∨ c = BTree.node [] := by
      have hh := hTriv ⟨0, by simp⟩
      simpa using hh
    have hcs : ∀ p : Fin cs.length,
        cs.get p = BTree.leaf ∨ cs.get p = BTree.node [] := by
      intro p
      have hh := hTriv ⟨p.val + 1, by
        simp only [List.length_cons]; omega⟩
      simpa using hh
    have ih' := ih hcs
    have hco : c.order = 1 := by
      rcases hc with rfl | rfl
      · simp
      · simp [BTree.order_node, List.foldr]
    have hcs_fold : cs.foldr (fun t n => t.order + n) 0 = cs.length := by
      have := ih'
      simp only [BTree.order_node] at this
      omega
    simp only [BTree.order_node, List.foldr, List.length_cons]
    omega

/-- Cycle 546 fourth tracked `G1.mul`-direction well-definedness deliverable:
parametric in `children`, product preserves `G₁` equivalence on every
node `BTree.node children` whose children are each `BTree.leaf` or
`BTree.node []`, when the tree has order at most `p`. Subsumes the cycle
540 / 542 / 544 / 545 single-shape and finite mixed-shape G1 slices
in one parametric statement. -/
theorem product_congr_node_trivial_children
    {p s s' t t' : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv t} {r' : QuotEquiv t'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r')
    (children : List BTree)
    (hTriv : ∀ k : Fin children.length,
        children.get k = BTree.leaf ∨ children.get k = BTree.node [])
    (hOrd : (BTree.node children).order ≤ p) :
    (q.product r).bSeriesHom (BTree.node children)
      = (q'.product r').bSeriesHom (BTree.node children) := by
  rw [QuotEquiv.bSeriesHom_product_node_trivial_children q r children hTriv,
      QuotEquiv.bSeriesHom_product_node_trivial_children q' r' children hTriv]
  have hLen : (BTree.node children).order = children.length + 1 :=
    order_node_trivial_children hTriv
  have hpge : children.length + 1 ≤ p := by rw [← hLen]; exact hOrd
  have hleaf : q.bSeriesHom BTree.leaf = q'.bSeriesHom BTree.leaf := by
    apply hq; rw [BTree.order_leaf]; omega
  have hnode :
      q.bSeriesHom (BTree.node children)
        = q'.bSeriesHom (BTree.node children) :=
    hq (BTree.node children) hOrd
  rw [hnode]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro S hS_mem
  have hS : S.card ≤ children.length := by
    have hmem : S ⊆ (Finset.univ : Finset (Fin children.length)) :=
      Finset.mem_powerset.mp hS_mem
    have := Finset.card_le_card hmem
    simpa using this
  have hsub :
      r.bSeriesHom
          (BTree.node (List.replicate (children.length - S.card) BTree.leaf))
        = r'.bSeriesHom
          (BTree.node
            (List.replicate (children.length - S.card) BTree.leaf)) := by
    apply hr
    rw [order_node_replicate_leaf]
    omega
  rw [hleaf, hsub]

/-- **Cycle 572 headline**: the unrestricted product congruence for
`IsG1Equiv`. With `bSeriesConv_consistency` available, the product respects
`G₁(p)` equivalence on every tree of order ≤ `p`, with no shape restriction
on `τ`. This subsumes all of the cycle 540–565
`product_congr_node_*` slice lemmas. -/
theorem product_congr
    {s u s' u' p : ℕ}
    {q : QuotEquiv s} {q' : QuotEquiv s'}
    {r : QuotEquiv u} {r' : QuotEquiv u'}
    (hq : IsG1Equiv p q q') (hr : IsG1Equiv p r r') :
    IsG1Equiv p (q.product r) (q'.product r') := by
  intro τ hτ
  induction q using Quotient.inductionOn with
  | _ t₁ =>
    induction q' using Quotient.inductionOn with
    | _ t₁' =>
      induction r using Quotient.inductionOn with
      | _ t₂ =>
        induction r' using Quotient.inductionOn with
        | _ t₂' =>
          -- α-locality hypothesis from `hq`.
          have hα : ∀ τ' : BTree, τ'.order ≤ p →
              t₁.bSeries τ' = t₁'.bSeries τ' := by
            intro τ' hτ'
            exact hq τ' hτ'
          -- β-locality hypothesis from `hr`.
          have hβ : ∀ τ' : BTree, τ'.order ≤ p →
              t₂.bSeries τ' = t₂'.bSeries τ' := by
            intro τ' hτ'
            exact hr τ' hτ'
          -- Goal: B-series of the products at τ agree on representatives.
          show (ButcherProduct t₁ t₂).bSeries τ = (ButcherProduct t₁' t₂').bSeries τ
          rw [ButcherProduct.bSeriesConv_consistency,
              ButcherProduct.bSeriesConv_consistency]
          rw [hα τ hτ, ButcherTableau.bSeriesConv_congr_of_le hα hβ hτ]

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

/-- The §387 group multiplication on `G₁(p)`. Lifts `QuotEquiv.product` along
the `IsG1Equiv` quotient via `IsG1Equiv.product_congr`. -/
noncomputable def mul {p : ℕ} : G1 p → G1 p → G1 p :=
  Quotient.lift₂
    (fun x y : Σ s : ℕ, QuotEquiv s => mk (p := p) (x.2.product y.2))
    (by
      intro x₁ y₁ x₂ y₂ hx hy
      apply Quotient.sound
      exact IsG1Equiv.product_congr hx hy)

@[simp] theorem mul_mk {p s u : ℕ} (q : QuotEquiv s) (r : QuotEquiv u) :
    mul (mk (p := p) q) (mk (p := p) r) = mk (p := p) (q.product r) := rfl

/-- Representative-level `bSeriesHomAt` of a `G₁(p)` product: equals the
admissible-cut convolution of its representatives' coefficients. This is the
quotient-level shadow of `ButcherProduct.bSeriesConv_consistency`. -/
theorem bSeriesHomAt_mul_mk {p s u : ℕ}
    (q : QuotEquiv s) (r : QuotEquiv u) (τ : BTree) (hτ : τ.order ≤ p) :
    bSeriesHomAt p τ hτ (mul (mk (p := p) q) (mk (p := p) r)) =
      q.bSeries τ + bSeriesConv (q.bSeries) (r.bSeries) τ := by
  induction q using Quotient.inductionOn with
  | _ t₁ =>
    induction r using Quotient.inductionOn with
    | _ t₂ =>
      show (ButcherProduct t₁ t₂).bSeries τ =
          t₁.bSeries τ + bSeriesConv (t₁.bSeries) (t₂.bSeries) τ
      rw [ButcherProduct.bSeriesConv_consistency]

/-- Left identity for `G₁(p)` multiplication. -/
theorem one_mul {p : ℕ} (g : G1 p) : mul (one p) g = g := by
  induction g using Quotient.inductionOn with
  | _ x =>
    rcases x with ⟨s, q⟩
    show mul (one p) (mk (p := p) q) = mk (p := p) q
    unfold one
    rw [mul_mk]
    apply Quotient.sound
    intro τ _
    show (QuotEquiv.product (Quotient.mk _ trivialTableau) q).bSeries τ
        = q.bSeries τ
    exact QuotEquiv.product_bSeries_one_left q τ

/-- Right identity for `G₁(p)` multiplication. -/
theorem mul_one {p : ℕ} (g : G1 p) : mul g (one p) = g := by
  induction g using Quotient.inductionOn with
  | _ x =>
    rcases x with ⟨s, q⟩
    show mul (mk (p := p) q) (one p) = mk (p := p) q
    unfold one
    rw [mul_mk]
    apply Quotient.sound
    intro τ _
    show (QuotEquiv.product q (Quotient.mk _ trivialTableau)).bSeries τ
        = q.bSeries τ
    exact QuotEquiv.product_bSeries_one_right q τ

end G1

end ButcherTableau
