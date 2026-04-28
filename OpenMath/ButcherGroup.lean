import Mathlib
import OpenMath.RungeKutta
import OpenMath.OrderConditions

/-!
# Butcher §381: Equivalence classes of Runge–Kutta methods (relabeling layer)

This file establishes the **relabeling-equivalence** layer for Runge–Kutta
methods (Butcher §381, the easy half): two `ButcherTableau`s with the same
stage count `s` are equivalent if there is a permutation of the stage
indices that carries one tableau to the other.

This is the prerequisite layer for the full Butcher group construction
(§38). Composition (§382), the elementary-weight homomorphism `G₁` (§383),
and identities/inverses/powers (§387) are intentionally out of scope here.

Reference: Butcher, *Numerical Methods for Ordinary Differential Equations*,
§38.1.
-/

open Finset

namespace ButcherTableau

variable {s : ℕ}

/-- Raw tableau total weight, used before passing to relabel-equivalence
classes. -/
def weightsSum (t : ButcherTableau s) : ℝ :=
  ∑ i : Fin s, t.b i

/-- Two `ButcherTableau`s with the same stage count are **relabel-equivalent**
if there is a permutation `σ` of the stage indices that carries one to the
other. -/
def IsRKEquivalent (t₁ t₂ : ButcherTableau s) : Prop :=
  ∃ σ : Equiv.Perm (Fin s),
    (∀ i j, t₂.A i j = t₁.A (σ i) (σ j)) ∧
    (∀ i, t₂.b i = t₁.b (σ i)) ∧
    (∀ i, t₂.c i = t₁.c (σ i))

namespace IsRKEquivalent

/-- Reflexivity: every tableau is relabel-equivalent to itself, witnessed by
the identity permutation. -/
theorem refl (t : ButcherTableau s) : IsRKEquivalent t t := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
  · intro i j; rfl
  · intro i; rfl
  · intro i; rfl

/-- Symmetry: relabel-equivalence is symmetric, witnessed by the inverse
permutation. -/
theorem symm {t₁ t₂ : ButcherTableau s} (h : IsRKEquivalent t₁ t₂) :
    IsRKEquivalent t₂ t₁ := by
  obtain ⟨σ, hA, hb, hc⟩ := h
  refine ⟨σ.symm, ?_, ?_, ?_⟩
  · intro i j
    have := hA (σ.symm i) (σ.symm j)
    simp [Equiv.apply_symm_apply] at this
    exact this.symm
  · intro i
    have := hb (σ.symm i)
    simp [Equiv.apply_symm_apply] at this
    exact this.symm
  · intro i
    have := hc (σ.symm i)
    simp [Equiv.apply_symm_apply] at this
    exact this.symm

/-- Transitivity: relabel-equivalence is transitive, witnessed by composition
of permutations. -/
theorem trans {t₁ t₂ t₃ : ButcherTableau s}
    (h₁₂ : IsRKEquivalent t₁ t₂) (h₂₃ : IsRKEquivalent t₂ t₃) :
    IsRKEquivalent t₁ t₃ := by
  obtain ⟨σ, hA₁, hb₁, hc₁⟩ := h₁₂
  obtain ⟨τ, hA₂, hb₂, hc₂⟩ := h₂₃
  refine ⟨τ.trans σ, ?_, ?_, ?_⟩
  · intro i j
    rw [hA₂ i j, hA₁ (τ i) (τ j)]
    rfl
  · intro i
    rw [hb₂ i, hb₁ (τ i)]
    rfl
  · intro i
    rw [hc₂ i, hc₁ (τ i)]
    rfl

end IsRKEquivalent

/-- The relabel-equivalence relation as a `Setoid` on `ButcherTableau s`. -/
instance isRKEquivalentSetoid (s : ℕ) : Setoid (ButcherTableau s) where
  r := IsRKEquivalent
  iseqv :=
    { refl := IsRKEquivalent.refl
      symm := IsRKEquivalent.symm
      trans := IsRKEquivalent.trans }

namespace IsRKEquivalent

/-- **Sanity lemma (§381):** relabel-equivalent tableaux have the same total
weight `∑ i, b i`. The weights are reindexed by the permutation, and
`Equiv.sum_comp` collapses the permutation-composed sum to the original. -/
theorem weights_sum_eq {t₁ t₂ : ButcherTableau s}
    (h : IsRKEquivalent t₁ t₂) :
    ∑ i, t₁.b i = ∑ i, t₂.b i := by
  obtain ⟨σ, _, hb, _⟩ := h
  calc ∑ i, t₁.b i
      = ∑ i, t₁.b (σ i) := (Equiv.sum_comp σ t₁.b).symm
    _ = ∑ i, t₂.b i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact (hb i).symm

/-- **Sanity lemma (§381):** relabel-equivalent tableaux have the same total
abscissa sum `∑ i, c i`. -/
theorem c_sum_eq {t₁ t₂ : ButcherTableau s}
    (h : IsRKEquivalent t₁ t₂) :
    ∑ i, t₁.c i = ∑ i, t₂.c i := by
  obtain ⟨σ, _, _, hc⟩ := h
  calc ∑ i, t₁.c i
      = ∑ i, t₁.c (σ i) := (Equiv.sum_comp σ t₁.c).symm
    _ = ∑ i, t₂.c i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact (hc i).symm

/-- Relabel-equivalent tableaux have identical elementary weights after
reindexing stages by the witnessing permutation. -/
theorem elementaryWeight_eq
    {t₁ t₂ : ButcherTableau s} {σ : Equiv.Perm (Fin s)}
    (hA : ∀ i j, t₂.A i j = t₁.A (σ i) (σ j))
    (τ : BTree) (i : Fin s) :
    t₂.elementaryWeight τ i = t₁.elementaryWeight τ (σ i) := by
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin s,
      t₂.elementaryWeight τ i = t₁.elementaryWeight τ (σ i))
    (motive_2 := fun children => ∀ i : Fin s,
      children.foldr
        (fun t acc => acc * (∑ k : Fin s, t₂.A i k * t₂.elementaryWeight t k)) 1 =
      children.foldr
        (fun t acc => acc * (∑ k : Fin s, t₁.A (σ i) k * t₁.elementaryWeight t k)) 1)
    ?leaf ?node ?nil ?cons τ
  · intro i
    simp
  · intro children hchildren i
    simpa [ButcherTableau.elementaryWeight] using hchildren i
  · intro i
    simp
  · intro head tail ih_head ih_tail i
    simp only [List.foldr]
    have hsum :
        (∑ k : Fin s, t₂.A i k * t₂.elementaryWeight head k) =
          ∑ k : Fin s, t₁.A (σ i) k * t₁.elementaryWeight head k := by
      calc
        (∑ k : Fin s, t₂.A i k * t₂.elementaryWeight head k)
            = ∑ k : Fin s, t₁.A (σ i) (σ k) *
                t₁.elementaryWeight head (σ k) := by
                refine Finset.sum_congr rfl ?_
                intro k _
                rw [hA i k, ih_head k]
      _ = ∑ k : Fin s, t₁.A (σ i) k * t₁.elementaryWeight head k := by
                exact (Equiv.sum_comp σ
                  (fun k : Fin s => t₁.A (σ i) k * t₁.elementaryWeight head k))
    rw [ih_tail i, hsum]

/-- The b-weighted elementary-weight sum is invariant under
relabel-equivalence. This is the Butcher-series coefficient attached to a
tree `τ`. -/
theorem bSeries_eq {t₁ t₂ : ButcherTableau s}
    (h : IsRKEquivalent t₁ t₂) (τ : BTree) :
    (∑ i : Fin s, t₁.b i * t₁.elementaryWeight τ i) =
      (∑ i : Fin s, t₂.b i * t₂.elementaryWeight τ i) := by
  obtain ⟨σ, hA, hb, _⟩ := h
  have hsum :
      (∑ i : Fin s, t₂.b i * t₂.elementaryWeight τ i) =
        ∑ i : Fin s, t₁.b i * t₁.elementaryWeight τ i := by
    calc
      (∑ i : Fin s, t₂.b i * t₂.elementaryWeight τ i)
          = ∑ i : Fin s, t₁.b (σ i) * t₁.elementaryWeight τ (σ i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [hb i, elementaryWeight_eq hA τ i]
      _ = ∑ i : Fin s, t₁.b i * t₁.elementaryWeight τ i := by
              exact (Equiv.sum_comp σ
                (fun i : Fin s => t₁.b i * t₁.elementaryWeight τ i))
  exact hsum.symm

/-- The rooted-tree order condition is invariant under relabel-equivalence. -/
theorem satisfiesTreeCondition_iff {t₁ t₂ : ButcherTableau s}
    (h : IsRKEquivalent t₁ t₂) (τ : BTree) :
    t₁.satisfiesTreeCondition τ ↔ t₂.satisfiesTreeCondition τ := by
  unfold ButcherTableau.satisfiesTreeCondition
  have hsum := bSeries_eq h τ
  constructor
  · intro h₁
    rw [← hsum]
    exact h₁
  · intro h₂
    rw [hsum]
    exact h₂

/-- Tree order up to any order `p` is invariant under relabel-equivalence. -/
theorem hasTreeOrder_iff {t₁ t₂ : ButcherTableau s}
    (h : IsRKEquivalent t₁ t₂) (p : ℕ) :
    t₁.hasTreeOrder p ↔ t₂.hasTreeOrder p := by
  simp only [ButcherTableau.hasTreeOrder]
  exact forall_congr' fun τ => imp_congr_right fun _ => satisfiesTreeCondition_iff h τ

end IsRKEquivalent

/-! ### §381/§383 quotient-facing packaging

Lift the order-condition predicates and sanity sums onto the quotient
`Quotient (isRKEquivalentSetoid s)` using the cycle-497 invariance lemmas
as well-definedness witnesses. -/

/-- Thin alias for the quotient of `ButcherTableau s` by relabel-equivalence. -/
def QuotEquiv (s : ℕ) : Type := Quotient (isRKEquivalentSetoid s)

namespace QuotEquiv

variable {s : ℕ}

/-- Tree order condition lifted to relabel-equivalence classes. -/
noncomputable def satisfiesTreeCondition (q : QuotEquiv s) (τ : BTree) : Prop :=
  Quotient.lift (fun t : ButcherTableau s => t.satisfiesTreeCondition τ)
    (fun _ _ h => propext (IsRKEquivalent.satisfiesTreeCondition_iff h τ)) q

/-- Tree-order-up-to-`p` lifted to relabel-equivalence classes. -/
noncomputable def hasTreeOrder (q : QuotEquiv s) (p : ℕ) : Prop :=
  Quotient.lift (fun t : ButcherTableau s => t.hasTreeOrder p)
    (fun _ _ h => propext (IsRKEquivalent.hasTreeOrder_iff h p)) q

/-- Computation lemma: the lifted order condition unfolds on a representative. -/
@[simp] theorem satisfiesTreeCondition_mk (t : ButcherTableau s) (τ : BTree) :
    satisfiesTreeCondition (Quotient.mk _ t) τ = t.satisfiesTreeCondition τ := rfl

/-- Computation lemma: the lifted order predicate unfolds on a representative. -/
@[simp] theorem hasTreeOrder_mk (t : ButcherTableau s) (p : ℕ) :
    hasTreeOrder (Quotient.mk _ t) p = t.hasTreeOrder p := rfl

/-- Sum of weights `∑ i, b i` lifted to relabel-equivalence classes. -/
def weightsSum (q : QuotEquiv s) : ℝ :=
  Quotient.lift (fun t : ButcherTableau s => ∑ i, t.b i)
    (fun _ _ h => IsRKEquivalent.weights_sum_eq h) q

/-- Sum of nodes `∑ i, c i` lifted to relabel-equivalence classes. -/
def cSum (q : QuotEquiv s) : ℝ :=
  Quotient.lift (fun t : ButcherTableau s => ∑ i, t.c i)
    (fun _ _ h => IsRKEquivalent.c_sum_eq h) q

/-- Computation lemma: the lifted weights-sum unfolds on a representative. -/
@[simp] theorem weightsSum_mk (t : ButcherTableau s) :
    weightsSum (Quotient.mk _ t) = ∑ i, t.b i := rfl

/-- Computation lemma: the lifted node-sum unfolds on a representative. -/
@[simp] theorem cSum_mk (t : ButcherTableau s) :
    cSum (Quotient.mk _ t) = ∑ i, t.c i := rfl

/-- Butcher series coefficient `∑ b_i Φ_i(τ)` lifted to relabel classes.
This is the left-hand side of the order condition for a tree `τ`. -/
noncomputable def bSeries (q : QuotEquiv s) (τ : BTree) : ℝ :=
  Quotient.lift (fun t : ButcherTableau s =>
      ∑ i, t.b i * t.elementaryWeight τ i)
    (fun _ _ h => IsRKEquivalent.bSeries_eq h τ) q

/-- Computation lemma: the lifted Butcher-series coefficient unfolds on a
representative. -/
@[simp] theorem bSeries_mk (t : ButcherTableau s) (τ : BTree) :
    bSeries (Quotient.mk _ t) τ =
      ∑ i, t.b i * t.elementaryWeight τ i := rfl

/-- The lifted tree order condition is exactly the lifted Butcher-series
coefficient equation. -/
theorem satisfiesTreeCondition_iff_bSeries (q : QuotEquiv s) (τ : BTree) :
    satisfiesTreeCondition q τ ↔ bSeries q τ = 1 / (τ.density : ℝ) := by
  refine Quotient.inductionOn q ?_
  intro t
  simp [ButcherTableau.satisfiesTreeCondition]

end QuotEquiv

/-! ### §387 trivial element

The zero-stage tableau is the group identity. Since `Fin 0` is empty, all
fields are vacuous and any two zero-stage tableaux are definitionally equal. -/

/-- The zero-stage Butcher tableau. All fields are functions out of `Fin 0`,
defined vacuously by `Fin.elim0`. -/
def trivialTableau : ButcherTableau 0 where
  A := fun i => Fin.elim0 i
  b := fun i => Fin.elim0 i
  c := fun i => Fin.elim0 i

/-- Uniqueness of the zero-stage tableau: there is only one inhabitant of
`ButcherTableau 0`. -/
theorem trivialTableau_unique (t : ButcherTableau 0) : t = trivialTableau := by
  cases t with
  | mk A b c =>
    apply ButcherTableau.mk.injEq _ _ _ _ _ _ |>.mpr
    refine ⟨?_, ?_, ?_⟩
    · funext i; exact Fin.elim0 i
    · funext i; exact Fin.elim0 i
    · funext i; exact Fin.elim0 i

/-! ### §382 raw composition

Concatenate the stages of two `ButcherTableau`s. The first `s` stages
come from `t₁`; the next `t` stages come from `t₂`, scaled and offset
to represent "run `t₁` for one step, then run `t₂` from the resulting
state".

The raw definition is *not* associative on the nose — the
associativity issue is recorded in
`.prover-state/issues/butcher_section382_composition.md` and is the
target of a **future** cycle, not this one. -/

/-- Butcher composition of two tableaux.

* The first `s` stages are the stages of `t₁`.
* The next `t` stages are the stages of `t₂`, but they see the result
  of one full step of `t₁` first.
* `b` is the concatenation of `t₁.b` and `t₂.b`.
* `c` is `(t₁.c, 1 + t₂.c)` (the second method runs after one step
  of length `1`).
* `A` is block lower-triangular: upper-left `s × s` block is `t₁.A`,
  lower-right `t × t` block is `t₂.A`, lower-left `t × s` block is
  `t₁.b` broadcast across rows, upper-right `s × t` block is `0`. -/
def ButcherProduct {s t : ℕ}
    (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherTableau (s + t) where
  A := fun i j =>
    Fin.addCases
      (fun i₁ =>
        Fin.addCases
          (fun j₁ => t₁.A i₁ j₁)
          (fun _ => 0)
          j)
      (fun i₂ =>
        Fin.addCases
          (fun j₁ => t₁.b j₁)
          (fun j₂ => t₂.A i₂ j₂)
          j)
      i
  b := fun i =>
    Fin.addCases (fun i₁ => t₁.b i₁) (fun i₂ => t₂.b i₂) i
  c := fun i =>
    Fin.addCases (fun i₁ => t₁.c i₁) (fun i₂ => 1 + t₂.c i₂) i

@[simp] theorem butcherProduct_b_castAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (i : Fin s) :
    (ButcherProduct t₁ t₂).b (Fin.castAdd t i) = t₁.b i := by
  simp [ButcherProduct]

@[simp] theorem butcherProduct_b_natAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (i : Fin t) :
    (ButcherProduct t₁ t₂).b (Fin.natAdd s i) = t₂.b i := by
  simp [ButcherProduct]

@[simp] theorem butcherProduct_c_castAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (i : Fin s) :
    (ButcherProduct t₁ t₂).c (Fin.castAdd t i) = t₁.c i := by
  simp [ButcherProduct]

@[simp] theorem butcherProduct_c_natAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (i : Fin t) :
    (ButcherProduct t₁ t₂).c (Fin.natAdd s i) = 1 + t₂.c i := by
  simp [ButcherProduct]

theorem butcherProduct_b_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (∑ i, (ButcherProduct t₁ t₂).b i)
      = (∑ i, t₁.b i) + (∑ i, t₂.b i) := by
  rw [Fin.sum_univ_add]
  simp [ButcherProduct]

/-- Butcher composition respects simultaneous relabeling of both factors. -/
theorem ButcherProduct.equiv_congr {s t : ℕ}
    {t₁ t₁' : ButcherTableau s} {t₂ t₂' : ButcherTableau t}
    (h₁ : IsRKEquivalent t₁ t₁') (h₂ : IsRKEquivalent t₂ t₂') :
    IsRKEquivalent (ButcherProduct t₁ t₂) (ButcherProduct t₁' t₂') := by
  obtain ⟨σ₁, hA₁, hb₁, hc₁⟩ := h₁
  obtain ⟨σ₂, hA₂, hb₂, hc₂⟩ := h₂
  let σ : Equiv.Perm (Fin (s + t)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr σ₁ σ₂).trans finSumFinEquiv)
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i₁
      refine Fin.addCases ?_ ?_ j
      · intro j₁
        simp [σ, ButcherProduct, hA₁]
      · intro j₂
        simp [σ, ButcherProduct]
    · intro i₂
      refine Fin.addCases ?_ ?_ j
      · intro j₁
        simp [σ, ButcherProduct, hb₁]
      · intro j₂
        simp [σ, ButcherProduct, hA₂]
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i₁
      simp [σ, ButcherProduct, hb₁]
    · intro i₂
      simp [σ, ButcherProduct, hb₂]
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i₁
      simp [σ, ButcherProduct, hc₁]
    · intro i₂
      simp [σ, ButcherProduct, hc₂]

namespace QuotEquiv

/-- Butcher composition lifted to relabel-equivalence classes. -/
def product {s t : ℕ} : QuotEquiv s → QuotEquiv t → QuotEquiv (s + t) :=
  Quotient.lift₂
    (fun t₁ t₂ => Quotient.mk _ (ButcherProduct t₁ t₂))
    (by
      intro t₁ t₁' t₂ t₂' h₁ h₂
      exact Quotient.sound (ButcherProduct.equiv_congr h₁ h₂))

@[simp] theorem product_mk {s t : ℕ}
    (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    product (Quotient.mk _ t₁) (Quotient.mk _ t₂)
      = Quotient.mk _ (ButcherProduct t₁ t₂) := rfl

/-- The lifted product adds total RK weights. -/
theorem product_weightsSum {s t : ℕ}
    (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) :
    (product q₁ q₂).weightsSum = q₁.weightsSum + q₂.weightsSum := by
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro t₁ t₂
  simp [product, butcherProduct_b_sum]

end QuotEquiv

/-! ### §382 partial associativity (`A` and `b` only)

Full `IsRKEquivalent` associativity for `ButcherProduct` does **not** hold:
the `c` (node) field disagrees in the third block — `(t₁ * t₂) * t₃`
gives `1 + t₃.c` while `t₁ * (t₂ * t₃)` gives `1 + (1 + t₃.c)`. See
`.prover-state/issues/butcher_section382_composition.md`.

The `A` matrix and `b` weight vector *do* line up under the canonical
reassociation `Fin ((s+t)+u) ≃ Fin (s+(t+u))` (the value-preserving
`finCongr (Nat.add_assoc s t u)`). This file lands that partial result,
which is the part actually needed by §384's elementary-weight homomorphism. -/

/-- The canonical reassociation `Fin ((s+t)+u) ≃ Fin (s+(t+u))`, identity
on underlying values. -/
def finReassoc (s t u : ℕ) : Fin ((s + t) + u) ≃ Fin (s + (t + u)) :=
  finCongr (Nat.add_assoc s t u)

@[simp] theorem finReassoc_val {s t u : ℕ} (i : Fin ((s + t) + u)) :
    (finReassoc s t u i).val = i.val := by
  simp [finReassoc]

/-- Image of an `s`-block index under `finReassoc`: stays in the
`s`-block of `s + (t + u)`. -/
theorem finReassoc_castAdd_castAdd {s t u : ℕ} (i : Fin s) :
    finReassoc s t u (Fin.castAdd u (Fin.castAdd t i)) =
      Fin.castAdd (t + u) i := by
  apply Fin.ext; simp [finReassoc, Fin.castAdd]

/-- Image of a `t`-block index (middle, sitting inside the left `s+t`)
under `finReassoc`: lands in the `t`-block of `s + (t + u)`. -/
theorem finReassoc_castAdd_natAdd {s t u : ℕ} (j : Fin t) :
    finReassoc s t u (Fin.castAdd u (Fin.natAdd s j)) =
      Fin.natAdd s (Fin.castAdd u j) := by
  apply Fin.ext
  simp [finReassoc, Fin.castAdd, Fin.natAdd]

/-- Image of a `u`-block index (rightmost) under `finReassoc`: lands in the
`u`-block of `s + (t + u)`. -/
theorem finReassoc_natAdd {s t u : ℕ} (k : Fin u) :
    finReassoc s t u (Fin.natAdd (s + t) k) =
      Fin.natAdd s (Fin.natAdd t k) := by
  apply Fin.ext
  simp [finReassoc, Fin.natAdd, Nat.add_assoc]

/-- Partial associativity: the `A` (stage-coefficient) matrix of
`(t₁ * t₂) * t₃` equals that of `t₁ * (t₂ * t₃)` after reindexing both
arguments by `finReassoc`. -/
theorem ButcherProduct.assoc_A {s t u : ℕ}
    (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (t₃ : ButcherTableau u)
    (i j : Fin ((s + t) + u)) :
    (ButcherProduct (ButcherProduct t₁ t₂) t₃).A i j =
      (ButcherProduct t₁ (ButcherProduct t₂ t₃)).A
        (finReassoc s t u i) (finReassoc s t u j) := by
  refine Fin.addCases (motive := fun i =>
      (ButcherProduct (ButcherProduct t₁ t₂) t₃).A i j =
        (ButcherProduct t₁ (ButcherProduct t₂ t₃)).A
          (finReassoc s t u i) (finReassoc s t u j)) ?_ ?_ i
  · intro i₁₂
    refine Fin.addCases (motive := fun i₁₂ =>
        (ButcherProduct (ButcherProduct t₁ t₂) t₃).A (Fin.castAdd u i₁₂) j =
          (ButcherProduct t₁ (ButcherProduct t₂ t₃)).A
            (finReassoc s t u (Fin.castAdd u i₁₂))
            (finReassoc s t u j)) ?_ ?_ i₁₂
    · intro i₁
      -- row in the s-block
      refine Fin.addCases (motive := fun j =>
          (ButcherProduct (ButcherProduct t₁ t₂) t₃).A
              (Fin.castAdd u (Fin.castAdd t i₁)) j =
            (ButcherProduct t₁ (ButcherProduct t₂ t₃)).A
              (finReassoc s t u (Fin.castAdd u (Fin.castAdd t i₁)))
              (finReassoc s t u j)) ?_ ?_ j
      · intro j₁₂
        refine Fin.addCases (motive := fun j₁₂ =>
            (ButcherProduct (ButcherProduct t₁ t₂) t₃).A
                (Fin.castAdd u (Fin.castAdd t i₁)) (Fin.castAdd u j₁₂) =
              (ButcherProduct t₁ (ButcherProduct t₂ t₃)).A
                (finReassoc s t u (Fin.castAdd u (Fin.castAdd t i₁)))
                (finReassoc s t u (Fin.castAdd u j₁₂))) ?_ ?_ j₁₂
        · intro j₁
          -- (s, s): both reduce to t₁.A i₁ j₁
          simp [ButcherProduct, finReassoc_castAdd_castAdd]
        · intro j₂
          -- (s, t): both reduce to 0
          simp [ButcherProduct, finReassoc_castAdd_castAdd,
                finReassoc_castAdd_natAdd]
      · intro j₃
        -- (s, u): both reduce to 0
        simp [ButcherProduct, finReassoc_castAdd_castAdd, finReassoc_natAdd]
    · intro i₂
      -- row in the t-block (middle)
      refine Fin.addCases (motive := fun j =>
          (ButcherProduct (ButcherProduct t₁ t₂) t₃).A
              (Fin.castAdd u (Fin.natAdd s i₂)) j =
            (ButcherProduct t₁ (ButcherProduct t₂ t₃)).A
              (finReassoc s t u (Fin.castAdd u (Fin.natAdd s i₂)))
              (finReassoc s t u j)) ?_ ?_ j
      · intro j₁₂
        refine Fin.addCases (motive := fun j₁₂ =>
            (ButcherProduct (ButcherProduct t₁ t₂) t₃).A
                (Fin.castAdd u (Fin.natAdd s i₂)) (Fin.castAdd u j₁₂) =
              (ButcherProduct t₁ (ButcherProduct t₂ t₃)).A
                (finReassoc s t u (Fin.castAdd u (Fin.natAdd s i₂)))
                (finReassoc s t u (Fin.castAdd u j₁₂))) ?_ ?_ j₁₂
        · intro j₁
          -- (t, s): both reduce to t₁.b j₁
          simp [ButcherProduct, finReassoc_castAdd_natAdd,
                finReassoc_castAdd_castAdd]
        · intro j₂
          -- (t, t): both reduce to t₂.A i₂ j₂
          simp [ButcherProduct, finReassoc_castAdd_natAdd]
      · intro j₃
        -- (t, u): both reduce to 0
        simp [ButcherProduct, finReassoc_castAdd_natAdd, finReassoc_natAdd]
  · intro i₃
    -- row in the u-block (rightmost)
    refine Fin.addCases (motive := fun j =>
        (ButcherProduct (ButcherProduct t₁ t₂) t₃).A (Fin.natAdd (s + t) i₃) j =
          (ButcherProduct t₁ (ButcherProduct t₂ t₃)).A
            (finReassoc s t u (Fin.natAdd (s + t) i₃))
            (finReassoc s t u j)) ?_ ?_ j
    · intro j₁₂
      refine Fin.addCases (motive := fun j₁₂ =>
          (ButcherProduct (ButcherProduct t₁ t₂) t₃).A
              (Fin.natAdd (s + t) i₃) (Fin.castAdd u j₁₂) =
            (ButcherProduct t₁ (ButcherProduct t₂ t₃)).A
              (finReassoc s t u (Fin.natAdd (s + t) i₃))
              (finReassoc s t u (Fin.castAdd u j₁₂))) ?_ ?_ j₁₂
      · intro j₁
        -- (u, s): both reduce to t₁.b j₁
        simp [ButcherProduct, finReassoc_natAdd, finReassoc_castAdd_castAdd]
      · intro j₂
        -- (u, t): both reduce to t₂.b j₂
        simp [ButcherProduct, finReassoc_natAdd, finReassoc_castAdd_natAdd]
    · intro j₃
      -- (u, u): both reduce to t₃.A i₃ j₃
      simp [ButcherProduct, finReassoc_natAdd]

/-- Cross-size generalization of `IsRKEquivalent.elementaryWeight_eq`:
two tableaux of possibly different stage counts whose `A` matrices
are related by a stage-`Equiv` have equal elementary weights after
relabeling. The `c` field plays no role in `elementaryWeight`, so this
result needs only an `A`-compatibility hypothesis. -/
theorem elementaryWeight_eq_of_A
    {s s' : ℕ} {t : ButcherTableau s} {t' : ButcherTableau s'}
    (σ : Fin s' ≃ Fin s)
    (hA : ∀ i j, t'.A i j = t.A (σ i) (σ j))
    (τ : BTree) (i : Fin s') :
    t'.elementaryWeight τ i = t.elementaryWeight τ (σ i) := by
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin s',
      t'.elementaryWeight τ i = t.elementaryWeight τ (σ i))
    (motive_2 := fun children => ∀ i : Fin s',
      children.foldr
        (fun r acc => acc * (∑ k : Fin s', t'.A i k * t'.elementaryWeight r k)) 1 =
      children.foldr
        (fun r acc => acc * (∑ k : Fin s, t.A (σ i) k * t.elementaryWeight r k)) 1)
    ?leaf ?node ?nil ?cons τ
  · intro i; simp
  · intro children hchildren i
    simpa [ButcherTableau.elementaryWeight] using hchildren i
  · intro i; simp
  · intro head tail ih_head ih_tail i
    simp only [List.foldr]
    have hsum :
        (∑ k : Fin s', t'.A i k * t'.elementaryWeight head k) =
          ∑ k : Fin s, t.A (σ i) k * t.elementaryWeight head k := by
      calc
        (∑ k : Fin s', t'.A i k * t'.elementaryWeight head k)
            = ∑ k : Fin s', t.A (σ i) (σ k) *
                t.elementaryWeight head (σ k) := by
                refine Finset.sum_congr rfl ?_
                intro k _
                rw [hA i k, ih_head k]
      _ = ∑ k : Fin s, t.A (σ i) k * t.elementaryWeight head k := by
                exact (Equiv.sum_comp σ
                  (fun k : Fin s => t.A (σ i) k * t.elementaryWeight head k))
    rw [ih_tail i, hsum]

/-- Partial associativity: the `b` weight vector of `(t₁ * t₂) * t₃`
equals that of `t₁ * (t₂ * t₃)` after reindexing by `finReassoc`. -/
theorem ButcherProduct.assoc_b {s t u : ℕ}
    (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (t₃ : ButcherTableau u)
    (i : Fin ((s + t) + u)) :
    (ButcherProduct (ButcherProduct t₁ t₂) t₃).b i =
      (ButcherProduct t₁ (ButcherProduct t₂ t₃)).b
        (finReassoc s t u i) := by
  refine Fin.addCases (motive := fun i =>
      (ButcherProduct (ButcherProduct t₁ t₂) t₃).b i =
        (ButcherProduct t₁ (ButcherProduct t₂ t₃)).b
          (finReassoc s t u i)) ?_ ?_ i
  · intro i₁₂
    refine Fin.addCases (motive := fun i₁₂ =>
        (ButcherProduct (ButcherProduct t₁ t₂) t₃).b (Fin.castAdd u i₁₂) =
          (ButcherProduct t₁ (ButcherProduct t₂ t₃)).b
            (finReassoc s t u (Fin.castAdd u i₁₂))) ?_ ?_ i₁₂
    · intro i₁
      simp [ButcherProduct, finReassoc_castAdd_castAdd]
    · intro i₂
      simp [ButcherProduct, finReassoc_castAdd_natAdd]
  · intro i₃
    simp [ButcherProduct, finReassoc_natAdd]

/-- Butcher-series associativity at the raw-tableau level: even though
`ButcherProduct` is not associative on the nose (the `c`-field disagrees),
the `b`-weighted elementary-weight sum *is* associative for every tree.
This is what feeds Butcher §384's elementary-weight homomorphism. -/
theorem ButcherProduct.bSeries_assoc {s t u : ℕ}
    (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (t₃ : ButcherTableau u)
    (τ : BTree) :
    (∑ i, (ButcherProduct (ButcherProduct t₁ t₂) t₃).b i *
        (ButcherProduct (ButcherProduct t₁ t₂) t₃).elementaryWeight τ i) =
      (∑ i, (ButcherProduct t₁ (ButcherProduct t₂ t₃)).b i *
        (ButcherProduct t₁ (ButcherProduct t₂ t₃)).elementaryWeight τ i) := by
  set L := ButcherProduct (ButcherProduct t₁ t₂) t₃
  set R := ButcherProduct t₁ (ButcherProduct t₂ t₃)
  set σ : Fin ((s + t) + u) ≃ Fin (s + (t + u)) := finReassoc s t u
  have hA : ∀ i j, L.A i j = R.A (σ i) (σ j) := by
    intro i j; exact ButcherProduct.assoc_A t₁ t₂ t₃ i j
  have hb : ∀ i, L.b i = R.b (σ i) := by
    intro i; exact ButcherProduct.assoc_b t₁ t₂ t₃ i
  calc
    (∑ i, L.b i * L.elementaryWeight τ i)
        = ∑ i, R.b (σ i) * R.elementaryWeight τ (σ i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hb i, elementaryWeight_eq_of_A σ hA τ i]
    _ = ∑ i, R.b i * R.elementaryWeight τ i :=
            Equiv.sum_comp σ (fun i => R.b i * R.elementaryWeight τ i)

/-! ### §384 identity prep for the Butcher-series map -/

/-- The zero-stage tableau is a left identity for the b-weighted
elementary-weight sum of a product tableau. -/
theorem ButcherProduct.bSeries_one_left {t : ℕ}
    (t₂ : ButcherTableau t) (τ : BTree) :
    (∑ i, (ButcherProduct trivialTableau t₂).b i *
        (ButcherProduct trivialTableau t₂).elementaryWeight τ i) =
      ∑ i, t₂.b i * t₂.elementaryWeight τ i := by
  let L := ButcherProduct trivialTableau t₂
  let σ : Fin (0 + t) ≃ Fin t := finCongr (Nat.zero_add t)
  have hA : ∀ i j, L.A i j = t₂.A (σ i) (σ j) := by
    intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i₀
      exact Fin.elim0 i₀
    · intro i₂
      refine Fin.addCases ?_ ?_ j
      · intro j₀
        exact Fin.elim0 j₀
      · intro j₂
        simp [L, σ, ButcherProduct, Fin.addCases]
  have hb : ∀ i, L.b i = t₂.b (σ i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i₀
      exact Fin.elim0 i₀
    · intro i₂
      simp [L, σ, ButcherProduct, Fin.addCases]
  calc
    (∑ i, (ButcherProduct trivialTableau t₂).b i *
        (ButcherProduct trivialTableau t₂).elementaryWeight τ i)
        = ∑ i, L.b i * L.elementaryWeight τ i := rfl
    _ = ∑ i, t₂.b (σ i) * t₂.elementaryWeight τ (σ i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hb i, elementaryWeight_eq_of_A σ hA τ i]
    _ = ∑ i, t₂.b i * t₂.elementaryWeight τ i :=
        Equiv.sum_comp σ (fun i => t₂.b i * t₂.elementaryWeight τ i)

/-- The zero-stage tableau is a right identity for the b-weighted
elementary-weight sum of a product tableau. -/
theorem ButcherProduct.bSeries_one_right {s : ℕ}
    (t₁ : ButcherTableau s) (τ : BTree) :
    (∑ i, (ButcherProduct t₁ trivialTableau).b i *
        (ButcherProduct t₁ trivialTableau).elementaryWeight τ i) =
      ∑ i, t₁.b i * t₁.elementaryWeight τ i := by
  let L := ButcherProduct t₁ trivialTableau
  let σ : Fin (s + 0) ≃ Fin s := finCongr (Nat.add_zero s)
  have hcast (x : Fin s) (h : (x : ℕ) < s) : x.castLT h = x := by
    ext
    rfl
  have hA : ∀ i j, L.A i j = t₁.A (σ i) (σ j) := by
    intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i₁
      refine Fin.addCases ?_ ?_ j
      · intro j₁
        change L.A (Fin.castAdd 0 i₁) (Fin.castAdd 0 j₁) = t₁.A i₁ j₁
        simp [L, ButcherProduct, Fin.addCases, hcast]
      · intro j₀
        exact Fin.elim0 j₀
    · intro i₀
      exact Fin.elim0 i₀
  have hb : ∀ i, L.b i = t₁.b (σ i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i₁
      change L.b (Fin.castAdd 0 i₁) = t₁.b i₁
      simp [L, ButcherProduct, Fin.addCases, hcast]
    · intro i₀
      exact Fin.elim0 i₀
  calc
    (∑ i, (ButcherProduct t₁ trivialTableau).b i *
        (ButcherProduct t₁ trivialTableau).elementaryWeight τ i)
        = ∑ i, L.b i * L.elementaryWeight τ i := rfl
    _ = ∑ i, t₁.b (σ i) * t₁.elementaryWeight τ (σ i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hb i, elementaryWeight_eq_of_A σ hA τ i]
    _ = ∑ i, t₁.b i * t₁.elementaryWeight τ i :=
        Equiv.sum_comp σ (fun i => t₁.b i * t₁.elementaryWeight τ i)

/-! ### §384 convolution prep

The next layer of the Butcher group construction expresses the
elementary weight of `(ButcherProduct t₁ t₂)` at a `node children`
tree, in a row of the second-method block, as a sum over choices of
which children are "cut" (handled by the first method's `b`-row of
the lower-left block) versus which remain attached (handled
recursively through `t₂.A`). The full closed-form
`(t₁.product t₂).bSeries τ = ∑ (trunk, cuts) ...` of Butcher §384
requires recursing on the attached children and is deferred to a
later cycle. This section lands the list-level combinator and the
raw "sum over cuts" identity at a node — the smallest piece
independent of any specific tree decomposition.

See `.prover-state/issues/butcher_section384_convolution.md`. -/

/-- Raw Butcher-series coefficient of a tableau at a rooted tree:
`∑ i, bᵢ Φᵢ(τ)`. The quotient-level version is `QuotEquiv.bSeries`;
this representative-level wrapper is convenient for the §384 convolution
identities before quotienting. -/
noncomputable def bSeries (tab : ButcherTableau s) (τ : BTree) : ℝ :=
  ∑ i, tab.b i * tab.elementaryWeight τ i

/-- The elementary weight of `ButcherProduct t₁ t₂` at an upper-left block
stage is exactly the elementary weight of `t₁`. This is the cut-side
reduction needed for the §384 convolution: once a child has crossed through
the lower-left `t₁.b` block, all further descendants remain inside the
first tableau. -/
theorem ButcherProduct.elementaryWeight_castAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin s) :
    (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i)
      = t₁.elementaryWeight τ i := by
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin s,
      (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i)
        = t₁.elementaryWeight τ i)
    (motive_2 := fun children => ∀ i : Fin s,
      children.foldr
        (fun r acc => acc * (∑ k : Fin (s + t),
          (ButcherProduct t₁ t₂).A (Fin.castAdd t i) k *
            (ButcherProduct t₁ t₂).elementaryWeight r k)) 1 =
      children.foldr
        (fun r acc => acc * (∑ k : Fin s,
          t₁.A i k * t₁.elementaryWeight r k)) 1)
    ?leaf ?node ?nil ?cons τ
  · intro i
    simp
  · intro children hchildren i
    simpa [ButcherTableau.elementaryWeight] using hchildren i
  · intro i
    simp
  · intro head tail ih_head ih_tail i
    simp only [List.foldr]
    have hsum :
        (∑ k : Fin (s + t),
          (ButcherProduct t₁ t₂).A (Fin.castAdd t i) k *
            (ButcherProduct t₁ t₂).elementaryWeight head k) =
          ∑ k : Fin s, t₁.A i k * t₁.elementaryWeight head k := by
      rw [Fin.sum_univ_add]
      have hzero :
          (∑ k : Fin t,
            (ButcherProduct t₁ t₂).A (Fin.castAdd t i) (Fin.natAdd s k) *
              (ButcherProduct t₁ t₂).elementaryWeight head (Fin.natAdd s k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        simp [ButcherProduct]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ih_head k]
      simp [ButcherProduct]
    rw [ih_tail i, hsum]

/-- The cut-side weighted sum through the upper-left block is the raw
Butcher-series coefficient of the first tableau. -/
theorem ButcherProduct.bSeries_castAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) :
    (∑ i : Fin s, t₁.b i *
      (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i))
      = t₁.bSeries τ := by
  simp [bSeries, ButcherProduct.elementaryWeight_castAdd]

/-- List-level combinator: a `foldr`-style product of binomial sums
expands as a Finset.powerset-indexed sum over which factor is taken
from each list position. This is the list-version mirror of
`Finset.prod_add`. -/
private theorem foldr_mul_add_eq_powerset_sum {α : Type*}
    (children : List α) (x y : α → ℝ) :
    children.foldr (fun c acc => acc * (x c + y c)) 1
      = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ k ∈ T, x children[k]) * ∏ k ∈ Finset.univ \ T, y children[k] := by
  have hprod : children.foldr (fun c acc => acc * (x c + y c)) 1
      = ∏ k : Fin children.length, (x children[k] + y children[k]) := by
    induction children with
    | nil => simp
    | cons c cs ih =>
      show cs.foldr (fun c acc => acc * (x c + y c)) 1 * (x c + y c)
           = ∏ k : Fin (cs.length + 1), (x (c :: cs)[k] + y (c :: cs)[k])
      rw [ih, Fin.prod_univ_succ]
      have h0 : (c :: cs)[(0 : Fin (cs.length + 1))] = c := rfl
      have hsucc : ∀ k : Fin cs.length,
          (c :: cs)[(k.succ : Fin (cs.length + 1))] = cs[k] := fun _ => rfl
      rw [h0]
      simp_rw [hsucc]
      ring
  rw [hprod, Finset.prod_add]

/-- Raw "sum over cuts" identity for the elementary weight of
`ButcherProduct t₁ t₂` at a `node children` tree, in a row
`Fin.natAdd s i` of the second-method block. The inner sum
`∑ k : Fin (s+t), (ButcherProduct t₁ t₂).A (natAdd s i) k * Φ_k` splits
into the lower-left block (`t₁.b j₁` broadcast across rows, paired
with `Φ` at upper-left columns `Fin.castAdd t j₁`) and the lower-right
block (`t₂.A i j₂`, paired with `Φ` at lower-right columns
`Fin.natAdd s j₂`). Applying `foldr_mul_add_eq_powerset_sum` to this
binomial split gives the powerset-indexed sum below.

This is the §384 "for each child, choose first-method `b`-cut versus
second-method `A`-keep" identity at a single node, with the inner
elementary weights kept in their raw `ButcherProduct`-indexed form.
The next layer (deferred) will recurse on the attached children to
reduce each factor to a `t₁.bSeries`/`t₂.elementaryWeight` shape. -/
theorem ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.natAdd s i)
      = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ k ∈ T,
             ∑ j₁ : Fin s, t₁.b j₁ *
               (ButcherProduct t₁ t₂).elementaryWeight children[k] (Fin.castAdd t j₁))
            * ∏ k ∈ Finset.univ \ T,
                 ∑ j₂ : Fin t, t₂.A i j₂ *
                   (ButcherProduct t₁ t₂).elementaryWeight children[k] (Fin.natAdd s j₂) := by
  have hsplit : ∀ c : BTree,
      (∑ k : Fin (s + t),
        (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
          (ButcherProduct t₁ t₂).elementaryWeight c k) =
      (∑ j₁ : Fin s, t₁.b j₁ *
        (ButcherProduct t₁ t₂).elementaryWeight c (Fin.castAdd t j₁))
      + (∑ j₂ : Fin t, t₂.A i j₂ *
        (ButcherProduct t₁ t₂).elementaryWeight c (Fin.natAdd s j₂)) := by
    intro c
    rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro j₁ _
      simp [ButcherProduct]
    · refine Finset.sum_congr rfl ?_
      intro j₂ _
      simp [ButcherProduct]
  rw [show (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.natAdd s i)
        = children.foldr
          (fun c acc => acc * (∑ k : Fin (s + t),
            (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
              (ButcherProduct t₁ t₂).elementaryWeight c k)) 1 from by
        simp [elementaryWeight]]
  have heq : (fun c (acc : ℝ) => acc * (∑ k : Fin (s + t),
        (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
          (ButcherProduct t₁ t₂).elementaryWeight c k))
      = (fun c acc => acc *
        ((∑ j₁ : Fin s, t₁.b j₁ *
          (ButcherProduct t₁ t₂).elementaryWeight c (Fin.castAdd t j₁))
        + (∑ j₂ : Fin t, t₂.A i j₂ *
          (ButcherProduct t₁ t₂).elementaryWeight c (Fin.natAdd s j₂)))) := by
    funext c acc
    rw [hsplit]
  rw [heq]
  exact foldr_mul_add_eq_powerset_sum children
    (fun c => ∑ j₁ : Fin s, t₁.b j₁ *
      (ButcherProduct t₁ t₂).elementaryWeight c (Fin.castAdd t j₁))
    (fun c => ∑ j₂ : Fin t, t₂.A i j₂ *
      (ButcherProduct t₁ t₂).elementaryWeight c (Fin.natAdd s j₂))

/-- The same node-level §384 powerset identity as
`ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum`, with the
cut-side factor reduced to the raw Butcher-series coefficient of `t₁`.
The summation index `S` records the children kept attached to the second
method; the complement `Sᶜ` records the children cut through `t₁.bSeries`. -/
theorem ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum_bSeries
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.natAdd s i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∏ p ∈ S, ∑ j₂ : Fin t, t₂.A i j₂ *
            (ButcherProduct t₁ t₂).elementaryWeight (children.get p) (Fin.natAdd s j₂)) := by
  classical
  let cut : Fin children.length → ℝ := fun p => t₁.bSeries (children.get p)
  let keep : Fin children.length → ℝ := fun p =>
    ∑ j₂ : Fin t, t₂.A i j₂ *
      (ButcherProduct t₁ t₂).elementaryWeight (children.get p) (Fin.natAdd s j₂)
  have hraw :
      (ButcherProduct t₁ t₂).elementaryWeight (BTree.node children) (Fin.natAdd s i)
        = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
            (∏ p ∈ T, cut p) *
            (∏ p ∈ Finset.univ \ T, keep p) := by
    rw [ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum]
    simp [cut, keep, ButcherProduct.bSeries_castAdd]
  have hraw_univ :
      (∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ p ∈ T, cut p) *
          (∏ p ∈ Finset.univ \ T, keep p))
        = ∑ T : Finset (Fin children.length),
            (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p) := by
    simp [Finset.compl_eq_univ_sdiff]
  have hcompl :
      (∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, cut p) * (∏ p ∈ S, keep p))
        = ∑ T : Finset (Fin children.length),
            (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p) := by
    let complPerm : Equiv.Perm (Finset (Fin children.length)) :=
      { toFun := fun S => Sᶜ
        invFun := fun S => Sᶜ
        left_inv := by
          intro S
          ext p
          simp
        right_inv := by
          intro S
          ext p
          simp }
    simpa [complPerm] using
      (Equiv.sum_comp complPerm (fun T : Finset (Fin children.length) =>
        (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p)))
  rw [hraw, hraw_univ]
  exact hcompl.symm

/-- §384 right-block auxiliary `ψ`: the recursive contribution attached
to a second-method stage `i : Fin t` after the upper-left block has been
collapsed via `t₁.bSeries`. The `t₁` data only enters through `bSeries`
values on subtrees, which is the structural witness that the next layer
of the §384 convolution recursion can consume to expose a closed-form
`(trunk, cuts)` decomposition. -/
noncomputable def ButcherProduct.rightAuxAt
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    BTree → Fin t → ℝ
  | .leaf, _ => 1
  | .node children, i =>
      children.foldr
        (fun c acc => acc * (t₁.bSeries c +
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAt t₁ t₂ c j)) 1
termination_by t => sizeOf t
decreasing_by
  have hmem : sizeOf c < sizeOf children :=
    List.sizeOf_lt_of_mem (by assumption)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by simp
  exact Nat.lt_trans hmem hnode

@[simp] theorem ButcherProduct.rightAuxAt_leaf
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ BTree.leaf i = 1 := by
  simp [ButcherProduct.rightAuxAt]

theorem ButcherProduct.rightAuxAt_node
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
      = children.foldr
          (fun c acc => acc * (t₁.bSeries c +
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ c j)) 1 := by
  rw [ButcherProduct.rightAuxAt]

/-- §384 right-block recursive reduction: the elementary weight of
`ButcherProduct t₁ t₂` at a second-method stage `Fin.natAdd s i` is the
recursive auxiliary `rightAuxAt t₁ t₂ τ i`. The `t₁` data only enters
through `bSeries`, which makes the closed-form `(trunk, cuts)`
decomposition viable on the next layer. -/
theorem ButcherProduct.elementaryWeight_natAdd
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
      = ButcherProduct.rightAuxAt t₁ t₂ τ i := by
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin t,
      (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
        = ButcherProduct.rightAuxAt t₁ t₂ τ i)
    (motive_2 := fun children => ∀ i : Fin t,
      children.foldr
        (fun r acc => acc * (∑ k : Fin (s + t),
          (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
            (ButcherProduct t₁ t₂).elementaryWeight r k)) 1 =
      children.foldr
        (fun r acc => acc * (t₁.bSeries r +
          ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAt t₁ t₂ r j)) 1)
    ?leaf ?node ?nil ?cons τ
  · intro i
    simp
  · intro children hchildren i
    simpa [ButcherTableau.elementaryWeight,
           ButcherProduct.rightAuxAt_node] using hchildren i
  · intro i
    simp
  · intro head tail ih_head ih_tail i
    simp only [List.foldr]
    have hsum :
        (∑ k : Fin (s + t),
          (ButcherProduct t₁ t₂).A (Fin.natAdd s i) k *
            (ButcherProduct t₁ t₂).elementaryWeight head k) =
          t₁.bSeries head +
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ head j := by
      rw [Fin.sum_univ_add]
      have hL :
          (∑ k : Fin s,
            (ButcherProduct t₁ t₂).A (Fin.natAdd s i) (Fin.castAdd t k) *
              (ButcherProduct t₁ t₂).elementaryWeight head (Fin.castAdd t k)) =
            t₁.bSeries head := by
        rw [ButcherTableau.bSeries]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [ButcherProduct.elementaryWeight_castAdd]
        simp [ButcherProduct]
      have hR :
          (∑ k : Fin t,
            (ButcherProduct t₁ t₂).A (Fin.natAdd s i) (Fin.natAdd s k) *
              (ButcherProduct t₁ t₂).elementaryWeight head (Fin.natAdd s k)) =
            ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ head j := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [ih_head k]
        simp [ButcherProduct]
      rw [hL, hR]
    rw [ih_tail i, hsum]

/-- Node-level powerset expansion of the §384 right-block auxiliary. The
summation index `S` records children kept in the recursive second-method
stage sum; the complement records children already cut to `t₁.bSeries`. -/
theorem ButcherProduct.rightAuxAt_node_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j) := by
  classical
  let cut : Fin children.length → ℝ := fun p => t₁.bSeries (children.get p)
  let keep : Fin children.length → ℝ := fun p =>
    ∑ j : Fin t, t₂.A i j *
      ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j
  have hraw :
      ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
        = ∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
            (∏ p ∈ T, cut p) *
            (∏ p ∈ Finset.univ \ T, keep p) := by
    rw [ButcherProduct.rightAuxAt_node]
    simpa [cut, keep] using
      (foldr_mul_add_eq_powerset_sum children
        (fun c => t₁.bSeries c)
        (fun c => ∑ j : Fin t, t₂.A i j *
          ButcherProduct.rightAuxAt t₁ t₂ c j))
  have hraw_univ :
      (∑ T ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ p ∈ T, cut p) *
          (∏ p ∈ Finset.univ \ T, keep p))
        = ∑ T : Finset (Fin children.length),
            (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p) := by
    simp [Finset.compl_eq_univ_sdiff]
  have hcompl :
      (∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, cut p) * (∏ p ∈ S, keep p))
        = ∑ T : Finset (Fin children.length),
            (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p) := by
    let complPerm : Equiv.Perm (Finset (Fin children.length)) :=
      { toFun := fun S => Sᶜ
        invFun := fun S => Sᶜ
        left_inv := by
          intro S
          ext p
          simp
        right_inv := by
          intro S
          ext p
          simp }
    simpa [complPerm] using
      (Equiv.sum_comp complPerm (fun T : Finset (Fin children.length) =>
        (∏ p ∈ T, cut p) * (∏ p ∈ Tᶜ, keep p)))
  rw [hraw, hraw_univ]
  exact hcompl.symm

/-- The stage-`b` weighted form of
`ButcherProduct.rightAuxAt_node_eq_powerset_sum`, ready for the §384
closed-form convolution: after choosing kept children `S`, the cut-side
`t₁.bSeries` product is independent of the second-method stage sum. -/
theorem ButcherProduct.bSeries_natAdd_node_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j)) := by
  classical
  let cut : Finset (Fin children.length) → ℝ := fun S =>
    ∏ p ∈ Sᶜ, t₁.bSeries (children.get p)
  let keep : Fin t → Finset (Fin children.length) → ℝ := fun i S =>
    ∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
      ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j
  have hstage : ∀ i : Fin t,
      ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
        = ∑ S : Finset (Fin children.length), cut S * keep i S := by
    intro i
    simpa [cut, keep] using
      (ButcherProduct.rightAuxAt_node_eq_powerset_sum t₁ t₂ children i)
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            (∑ S : Finset (Fin children.length), cut S * keep i S) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hstage i]
    _ = ∑ i : Fin t, ∑ S : Finset (Fin children.length),
          t₂.b i * (cut S * keep i S) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ S : Finset (Fin children.length), ∑ i : Fin t,
          t₂.b i * (cut S * keep i S) := by
        rw [Finset.sum_comm]
    _ = ∑ S : Finset (Fin children.length),
          cut S * (∑ i : Fin t, t₂.b i * keep i S) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j)) := by
        simp [cut, keep]

/-- Two-level powerset expansion of the §384 right-block auxiliary: each
kept child's contribution is itself decomposed by case analysis on the
child's tree shape, exposing the second-method side one full structural
layer deeper. Leaf children contribute a bare `t₂.A i j` row sum (since
`rightAuxAt t₁ t₂ leaf j = 1`); node children unfold into the inner
`(cut, kept)` powerset sum at the new parent index `j`. -/
theorem ButcherProduct.rightAuxAt_node_two_level_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∏ p ∈ S,
            (match children.get p with
             | BTree.leaf => ∑ j : Fin t, t₂.A i j
             | BTree.node gc =>
                 ∑ j : Fin t, t₂.A i j *
                   (∑ S' : Finset (Fin gc.length),
                     (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
                     (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                       ButcherProduct.rightAuxAt t₁ t₂ (gc.get q) k)))) := by
  rw [ButcherProduct.rightAuxAt_node_eq_powerset_sum]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  refine Finset.prod_congr rfl ?_
  intro p _
  generalize children.get p = c
  cases c with
  | leaf =>
    simp [ButcherProduct.rightAuxAt_leaf]
  | node gc =>
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAt_node_eq_powerset_sum]

/-- The stage-`b` weighted form of
`ButcherProduct.rightAuxAt_node_two_level_eq_powerset_sum`: the cut-side
`t₁.bSeries` product factors out of the second-method `b`-weighted stage
sum, and each kept child's contribution is the explicit leaf-or-node
case split that exposes `t₁` only through `bSeries` calls on
grand-subtrees. -/
theorem ButcherProduct.bSeries_natAdd_node_two_level_eq_powerset_sum
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAt t₁ t₂ (gc.get q) k))))) := by
  classical
  let cut : Finset (Fin children.length) → ℝ := fun S =>
    ∏ p ∈ Sᶜ, t₁.bSeries (children.get p)
  let kept : Fin t → Finset (Fin children.length) → ℝ := fun i S =>
    ∏ p ∈ S,
      (match children.get p with
       | BTree.leaf => ∑ j : Fin t, t₂.A i j
       | BTree.node gc =>
           ∑ j : Fin t, t₂.A i j *
             (∑ S' : Finset (Fin gc.length),
               (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
               (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                 ButcherProduct.rightAuxAt t₁ t₂ (gc.get q) k)))
  have hstage : ∀ i : Fin t,
      ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i
        = ∑ S : Finset (Fin children.length), cut S * kept i S := by
    intro i
    simpa [cut, kept] using
      (ButcherProduct.rightAuxAt_node_two_level_eq_powerset_sum t₁ t₂ children i)
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            (∑ S : Finset (Fin children.length), cut S * kept i S) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hstage i]
    _ = ∑ i : Fin t, ∑ S : Finset (Fin children.length),
          t₂.b i * (cut S * kept i S) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ S : Finset (Fin children.length), ∑ i : Fin t,
          t₂.b i * (cut S * kept i S) := by
        rw [Finset.sum_comm]
    _ = ∑ S : Finset (Fin children.length),
          cut S * (∑ i : Fin t, t₂.b i * kept i S) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAt t₁ t₂ (gc.get q) k))))) := by
        simp [cut, kept]

/-- Closed-form right-block auxiliary: at each node, sum over subsets
`S` of children. Children outside `S` are cut via `coef` (later specialised
to `t₁.bSeries`); children inside `S` are kept and feed back into the
recursion through `t₂.A i j`. -/
noncomputable def ButcherProduct.rightAuxAtCoef
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    BTree → Fin t → ℝ
  | .leaf, _ => 1
  | .node children, i =>
      ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
        (∏ p ∈ Sᶜ, coef (children.get p)) *
        (∏ p ∈ S,
          ∑ j : Fin t,
            t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j)
termination_by τ => sizeOf τ
decreasing_by
  have hmem : sizeOf (children.get p) < sizeOf children :=
    List.sizeOf_lt_of_mem (List.get_mem children p)
  have hnode : sizeOf children < sizeOf (BTree.node children) := by simp
  exact Nat.lt_trans hmem hnode

@[simp] theorem ButcherProduct.rightAuxAtCoef_leaf
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef BTree.leaf i = 1 := by
  simp [ButcherProduct.rightAuxAtCoef]

theorem ButcherProduct.rightAuxAtCoef_node
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i =
      ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
        (∏ p ∈ Sᶜ, coef (children.get p)) *
        (∏ p ∈ S,
          ∑ j : Fin t,
            t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j) := by
  rw [ButcherProduct.rightAuxAtCoef]

/-- Leaf-level `b`-weighted reduction for the coefficient-parametric
right-block auxiliary: leaves do not see the cut coefficient function. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_leaf
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef BTree.leaf i)
      = t₂.weightsSum := by
  simp [ButcherTableau.weightsSum]

/-- One-child node specialization of the coefficient-parametric right-block
auxiliary. It exposes the single `cut OR keep` branch. -/
theorem ButcherProduct.rightAuxAtCoef_node_singleton
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (child : BTree) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [child]) i
      = coef child +
        ∑ j : Fin t,
          t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j := by
  simp [ButcherProduct.rightAuxAtCoef_node]
  have hpowerset :
      ({0} : Finset (Fin 1)).powerset =
        ({∅, {0}} : Finset (Finset (Fin 1))) := by
    ext S
    simp [Finset.subset_singleton_iff]
  have hcompl : ({0} : Finset (Fin 1))ᶜ = ∅ := by
    ext x
    fin_cases x
    simp
  rw [hpowerset]
  simp [hcompl]

/-- One-child `b`-weighted closed form for the coefficient-parametric
right-block auxiliary. The cut term factors through `weightsSum`, while
the kept term retains the `A`-twisted recursion. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_singleton
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) (child : BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [child]) i)
      = coef child * t₂.weightsSum +
        ∑ i : Fin t, t₂.b i *
          ∑ j : Fin t,
            t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j := by
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node [child]) i)
        = ∑ i : Fin t, t₂.b i *
            (coef child +
              ∑ j : Fin t,
                t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [ButcherProduct.rightAuxAtCoef_node_singleton]
    _ = ∑ i : Fin t,
          (t₂.b i * coef child +
            t₂.b i *
              ∑ j : Fin t,
                t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = (∑ i : Fin t, t₂.b i * coef child) +
          ∑ i : Fin t, t₂.b i *
            ∑ j : Fin t,
              t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j := by
        rw [Finset.sum_add_distrib]
    _ = coef child * t₂.weightsSum +
          ∑ i : Fin t, t₂.b i *
            ∑ j : Fin t,
              t₂.A i j * ButcherProduct.rightAuxAtCoef t₂ coef child j := by
        congr 1
        calc
          (∑ i : Fin t, t₂.b i * coef child)
              = ∑ i : Fin t, coef child * t₂.b i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
          _ = coef child * t₂.weightsSum := by
            simp [ButcherTableau.weightsSum, Finset.mul_sum]

/-- Powerset-form unfolding of the coefficient-parametric right-block
auxiliary at a node, with the indexing set restated as the universal
`Finset (Fin children.length)`. The summation index `S` records the
children kept attached to the second method via `t₂.A`-twisted recursion;
the complement `Sᶜ` records the children cut through `coef`. This is the
§384 mirror of `ButcherProduct.rightAuxAt_node_eq_powerset_sum` with
`coef` replacing `t₁.bSeries`. -/
theorem ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
            ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j) := by
  rw [ButcherProduct.rightAuxAtCoef_node, Finset.powerset_univ]

/-- The stage-`b` weighted form of
`ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum`, ready for the §384
closed-form convolution: after choosing kept children `S`, the cut-side
`coef` product is independent of the second-method stage sum. This is the
`coef`-parametric mirror of
`ButcherProduct.bSeries_natAdd_node_eq_powerset_sum`. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j)) := by
  classical
  let cut : Finset (Fin children.length) → ℝ := fun S =>
    ∏ p ∈ Sᶜ, coef (children.get p)
  let keep : Fin t → Finset (Fin children.length) → ℝ := fun i S =>
    ∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
      ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j
  have hstage : ∀ i : Fin t,
      ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i
        = ∑ S : Finset (Fin children.length), cut S * keep i S := by
    intro i
    simpa [cut, keep] using
      (ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum t₂ coef children i)
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            (∑ S : Finset (Fin children.length), cut S * keep i S) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hstage i]
    _ = ∑ i : Fin t, ∑ S : Finset (Fin children.length),
          t₂.b i * (cut S * keep i S) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ S : Finset (Fin children.length), ∑ i : Fin t,
          t₂.b i * (cut S * keep i S) := by
        rw [Finset.sum_comm]
    _ = ∑ S : Finset (Fin children.length),
          cut S * (∑ i : Fin t, t₂.b i * keep i S) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S, ∑ j : Fin t, t₂.A i j *
              ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j)) := by
        simp [cut, keep]

/-- Two-level powerset expansion of the coefficient-parametric right-block
auxiliary. Each kept child is case-split: leaves collapse to a row sum of
`t₂.A`, while node children unfold into the inner powerset decomposition at
the new parent stage. -/
theorem ButcherProduct.rightAuxAtCoef_node_two_level_eq_powerset_sum
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∏ p ∈ S,
            (match children.get p with
             | BTree.leaf => ∑ j : Fin t, t₂.A i j
             | BTree.node gc =>
                 ∑ j : Fin t, t₂.A i j *
                   (∑ S' : Finset (Fin gc.length),
                     (∏ q ∈ S'ᶜ, coef (gc.get q)) *
                     (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                       ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k)))) := by
  rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]
  refine Finset.sum_congr rfl ?_
  intro S _
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
    rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]

/-- The stage-`b` weighted form of
`ButcherProduct.rightAuxAtCoef_node_two_level_eq_powerset_sum`. The
cut-side `coef` product factors through the second-method weighted stage
sum, while each kept child is expanded one structural layer deeper. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_two_level
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, coef (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k))))) := by
  classical
  let cut : Finset (Fin children.length) → ℝ := fun S =>
    ∏ p ∈ Sᶜ, coef (children.get p)
  let kept : Fin t → Finset (Fin children.length) → ℝ := fun i S =>
    ∏ p ∈ S,
      (match children.get p with
       | BTree.leaf => ∑ j : Fin t, t₂.A i j
       | BTree.node gc =>
           ∑ j : Fin t, t₂.A i j *
             (∑ S' : Finset (Fin gc.length),
               (∏ q ∈ S'ᶜ, coef (gc.get q)) *
               (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                 ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k)))
  have hstage : ∀ i : Fin t,
      ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i
        = ∑ S : Finset (Fin children.length), cut S * kept i S := by
    intro i
    simpa [cut, kept] using
      (ButcherProduct.rightAuxAtCoef_node_two_level_eq_powerset_sum t₂ coef children i)
  calc
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
        = ∑ i : Fin t, t₂.b i *
            (∑ S : Finset (Fin children.length), cut S * kept i S) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hstage i]
    _ = ∑ i : Fin t, ∑ S : Finset (Fin children.length),
          t₂.b i * (cut S * kept i S) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ S : Finset (Fin children.length), ∑ i : Fin t,
          t₂.b i * (cut S * kept i S) := by
        rw [Finset.sum_comm]
    _ = ∑ S : Finset (Fin children.length),
          cut S * (∑ i : Fin t, t₂.b i * kept i S) := by
        refine Finset.sum_congr rfl ?_
        intro S _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, coef (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, coef (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k))))) := by
        simp [cut, kept]

theorem ButcherProduct.rightAuxAt_leaf_eq_coef
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ BTree.leaf i =
      ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) BTree.leaf i := by
  simp [ButcherProduct.rightAuxAt_leaf, ButcherProduct.rightAuxAtCoef_leaf]

theorem ButcherProduct.rightAuxAt_node_eq_coef_one_level
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ (BTree.node children) i =
      ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
        (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
        (∏ p ∈ S,
          ∑ j : Fin t,
            t₂.A i j * ButcherProduct.rightAuxAt t₁ t₂ (children.get p) j) := by
  simpa using
    (ButcherProduct.rightAuxAt_node_eq_powerset_sum t₁ t₂ children i)

/-- §384 right-block structural equivalence: the recursive auxiliary
`rightAuxAt t₁ t₂` equals the closed-form `rightAuxAtCoef t₂ (t₁.bSeries)`,
i.e., `t₁` enters the right-block recursion only through its
`bSeries` values on subtrees. This is the structural witness Butcher's
§384 homomorphism statement consumes. -/
theorem ButcherProduct.rightAuxAt_eq_rightAuxAtCoef_bSeries
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin t) :
    ButcherProduct.rightAuxAt t₁ t₂ τ i
      = ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) τ i := by
  classical
  revert i
  refine BTree.rec
    (motive_1 := fun τ => ∀ i : Fin t,
      ButcherProduct.rightAuxAt t₁ t₂ τ i
        = ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) τ i)
    (motive_2 := fun children => ∀ c ∈ children, ∀ j : Fin t,
      ButcherProduct.rightAuxAt t₁ t₂ c j
        = ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) c j)
    ?leaf ?node ?nil ?cons τ
  · intro i
    exact ButcherProduct.rightAuxAt_leaf_eq_coef t₁ t₂ i
  · intro children hchildren i
    rw [ButcherProduct.rightAuxAt_node_eq_coef_one_level,
        ButcherProduct.rightAuxAtCoef_node]
    refine Finset.sum_congr rfl ?_
    intro S _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro p _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hchildren (children.get p) (List.get_mem children p) j]
  · intro c hc
    simp at hc
  · intro head tail ih_head ih_tail c hc j
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ih_head j
    · exact ih_tail c hc' j

/-- §384 elementary-weight corollary: the elementary weight of
`ButcherProduct t₁ t₂` at a second-method stage `Fin.natAdd s i` equals
the closed-form `rightAuxAtCoef t₂ (t₁.bSeries)`. This composes
`elementaryWeight_natAdd` with the structural equivalence. -/
theorem ButcherProduct.elementaryWeight_natAdd_eq_rightAuxAtCoef
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (τ : BTree) (i : Fin t) :
    (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
      = ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) τ i := by
  rw [ButcherProduct.elementaryWeight_natAdd,
      ButcherProduct.rightAuxAt_eq_rightAuxAtCoef_bSeries]

/-- §384 bSeries-level corollary: the second-method `b`-weighted stage
sum of `ButcherProduct t₁ t₂` evaluated at any tree `τ` collapses to a
sum of `rightAuxAtCoef`-values, mentioning `t₁` only through its
`bSeries`. -/
theorem ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (τ : BTree) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i))
      = ∑ i : Fin t, t₂.b i *
          ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) τ i := by
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [ButcherProduct.elementaryWeight_natAdd_eq_rightAuxAtCoef]

/-- `bSeries`-level two-level right-block expansion, specialized from the
coefficient-parametric auxiliary with `coef = t₁.bSeries`. This is the
node-level bridge from the product tableau's second block to the closed
coefficient-parametric §384 recursion one structural layer below the root. -/
theorem ButcherProduct.bSeries_natAdd_node_two_level_eq_rightAuxAtCoef
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S : Finset (Fin children.length),
          (∏ p ∈ Sᶜ, t₁.bSeries (children.get p)) *
          (∑ i : Fin t, t₂.b i *
            (∏ p ∈ S,
              (match children.get p with
               | BTree.leaf => ∑ j : Fin t, t₂.A i j
               | BTree.node gc =>
                   ∑ j : Fin t, t₂.A i j *
                     (∑ S' : Finset (Fin gc.length),
                       (∏ q ∈ S'ᶜ, t₁.bSeries (gc.get q)) *
                       (∏ q ∈ S', ∑ k : Fin t, t₂.A j k *
                         ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) (gc.get q) k))))) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_two_level]

/-- Leaf-level `b`-weighted closed form, restated as `weightsSum`. This is
the cycle 528 `_eq` companion to `bWeighted_rightAuxAtCoef_leaf`, with the
same statement, exposed under the rotation-naming convention used by the
node-side closures. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_leaf_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef BTree.leaf i)
      = t₂.weightsSum :=
  ButcherProduct.bWeighted_rightAuxAtCoef_leaf t₂ coef

/-- Leaf specialization of the right-block coefficient at `coef := t₁.bSeries`:
the second-method `b`-weighted stage sum of the product tableau evaluated at
`BTree.leaf` collapses to `t₂.weightsSum`. -/
theorem ButcherProduct.bSeries_natAdd_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight BTree.leaf
            (Fin.natAdd s i))
      = t₂.weightsSum := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_leaf]

/-- Trunk-recursion form of the `b`-weighted root sum at a node tree: the
powerset sum is reindexed so that the chosen subset `S` records the children
*cut* via `coef`, while the complement `Sᶜ` records the children kept
attached through the second-method `t₂.A`-twisted recursion. This is the
`S`/`Sᶜ` swap of `bWeighted_rightAuxAtCoef_node`, ready for the §384
trunk-side closed form. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Fin children.length)).powerset,
          (∏ p ∈ S, coef (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              (∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                  ButcherProduct.rightAuxAtCoef t₂ coef (children.get p) j)) := by
  classical
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node, Finset.powerset_univ]
  refine Finset.sum_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_ ?_
  · intros S _; exact Finset.mem_univ _
  · intros S _; exact Finset.mem_univ _
  · intros S _; exact compl_compl S
  · intros S _; exact compl_compl S
  · intros S _; rw [compl_compl]

/-- Trunk-recursion kept-leaf simplification: if every child of the root is
`BTree.leaf`, the kept-side auxiliary factor in the trunk recursion collapses
to the plain row sum `∑ j, t₂.A i j`. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (coef : BTree → ℝ)
    (children : List BTree)
    (hAllLeaf : ∀ c ∈ children, c = BTree.leaf) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ _p ∈ S, coef BTree.leaf) *
            (∑ i : Fin t, t₂.b i *
                ∏ _p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j) := by
  classical
  have _ht₁ : t₁ = t₁ := rfl
  have hchild : ∀ p : Fin children.length, children.get p = BTree.leaf := by
    intro p
    exact hAllLeaf (children.get p) (List.get_mem children p)
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro p _
    rw [hchild p]
  · refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [hchild p]
    simp [ButcherProduct.rightAuxAtCoef_leaf]

/-- Trunk-recursion kept singleton-node simplification: if every child of the
root is a one-child node `BTree.node [gc p]`, the kept-side recursive auxiliary
factor in the trunk recursion expands one structural level using the
single-child unfolding `ButcherProduct.rightAuxAtCoef_node_singleton`,
exposing only coefficient values on the grandchild trees `gc p`. This is the
kept-node companion to `bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq`,
demonstrating that the trunk recursion factors through `coef`-only values one
level beyond the leaf base case from cycle 529. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (gc : Fin children.length → BTree)
    (hChild : ∀ p : Fin children.length, children.get p = BTree.node [gc p]) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (BTree.node [gc p])) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                (coef (gc p) +
                  ∑ k : Fin t, t₂.A j k *
                    ButcherProduct.rightAuxAtCoef t₂ coef (gc p) k)) := by
  classical
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro p _
    rw [hChild p]
  · refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [hChild p]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_node_singleton]

/-- Trunk-recursion kept node simplification: if every child of the root is
a node `BTree.node (gc p)`, the kept-side recursive auxiliary factor in the
trunk recursion expands by the full powerset decomposition over the
grandchildren of each kept child. This generalizes
`bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq` from singleton
grandchild lists to arbitrary grandchild lists. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_node_eq
    {t : ℕ} (t₂ : ButcherTableau t) (coef : BTree → ℝ)
    (children : List BTree) (gc : Fin children.length → List BTree)
    (hChild : ∀ p : Fin children.length, children.get p = BTree.node (gc p)) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (BTree.node (gc p))) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                (∑ T : Finset (Fin (gc p).length),
                  (∏ q ∈ Tᶜ, coef ((gc p).get q)) *
                    (∏ q ∈ T, ∑ k : Fin t, t₂.A j k *
                      ButcherProduct.rightAuxAtCoef t₂ coef ((gc p).get q) k))) := by
  classical
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
      Finset.powerset_univ]
  refine Finset.sum_congr rfl ?_
  intro S _
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro p _
    rw [hChild p]
  · refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [hChild p]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]

/-- bSeries-form corollary of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq`: when every
child of the root is `BTree.leaf`, the second-method `b`-weighted stage sum
of `ButcherProduct t₁ t₂` evaluated at `BTree.node children` collapses to
the trunk-recursion RHS with `coef := t₁.bSeries`, so each cut factor
becomes `t₁.bSeries BTree.leaf` and the kept factor is the plain row sum
`∑ j, t₂.A i j`. -/
theorem ButcherProduct.bSeries_natAdd_node_trunk_kept_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree)
    (hAllLeaf : ∀ c ∈ children, c = BTree.leaf) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ _p ∈ S, t₁.bSeries BTree.leaf) *
            (∑ i : Fin t, t₂.b i *
                ∏ _p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq
        t₁ t₂ (t₁.bSeries) children hAllLeaf]

/-- bSeries-form corollary of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq`:
when every child of the root is a one-child node `BTree.node [gc p]`, the
second-method `b`-weighted stage sum of `ButcherProduct t₁ t₂` is the
coefficient-parametric trunk-recursion RHS specialized at
`coef := t₁.bSeries`. -/
theorem ButcherProduct.bSeries_natAdd_node_trunk_kept_singleton_node_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (children : List BTree) (gc : Fin children.length → BTree)
    (hChild : ∀ p : Fin children.length, children.get p = BTree.node [gc p]) :
    (∑ i : Fin t, t₂.b i *
        (ButcherProduct t₁ t₂).elementaryWeight
          (BTree.node children) (Fin.natAdd s i))
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, t₁.bSeries (BTree.node [gc p])) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ, ∑ j : Fin t, t₂.A i j *
                (t₁.bSeries (gc p) +
                  ∑ k : Fin t, t₂.A j k *
                    ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) (gc p) k)) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq
        t₂ (t₁.bSeries) children gc hChild]

/-- Trunk-recursion unified kept-children simplification: each kept-side
recursive auxiliary factor in the trunk recursion is simplified by
case-splitting on whether the corresponding root child is a leaf or a node.
A leaf kept-child contributes the plain row sum `∑ j, t₂.A i j`; a node
kept-child contributes `∑ j, t₂.A i j *` times the inner powerset sum from
`rightAuxAtCoef_node_eq_powerset_sum`. This generalizes
`bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq` and
`bWeighted_rightAuxAtCoef_node_trunk_kept_node_eq` to arbitrary mixes of
leaves and nodes among the root's children. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (coef : BTree → ℝ) (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       (∑ T : Finset (Fin gc.length),
                         (∏ q ∈ Tᶜ, coef (gc.get q)) *
                         (∏ q ∈ T, ∑ k : Fin t, t₂.A j k *
                           ButcherProduct.rightAuxAtCoef t₂ coef (gc.get q) k)))) := by
  classical
  have _ht₁ : t₁ = t₁ := rfl
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion,
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
    rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]

/-- bSeries-form corollary of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq`: the
second-method `b`-weighted stage sum of `ButcherProduct t₁ t₂` evaluated at
`BTree.node children` is the trunk-recursion RHS specialized at
`coef := t₁.bSeries`, with each kept-child factor simplified by
case-splitting on whether the root child is a leaf or a node. -/
theorem ButcherProduct.bSeries_natAdd_node_trunk_kept_eq
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
                       (∑ T : Finset (Fin gc.length),
                         (∏ q ∈ Tᶜ, t₁.bSeries (gc.get q)) *
                         (∏ q ∈ T, ∑ k : Fin t, t₂.A j k *
                           ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries)
                             (gc.get q) k)))) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq
        t₁ t₂ (t₁.bSeries) children]

/-- Trunk-recursion depth-2 kept-children simplification: after the cycle 532
kept-child pass-through, each kept grandchild that remains attached under a
kept node child is simplified one structural layer further by case-splitting
on whether that grandchild is a leaf or a node. -/
theorem ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_two_level_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t)
    (coef : BTree → ℝ) (children : List BTree) :
    (∑ i : Fin t, t₂.b i *
        ButcherProduct.rightAuxAtCoef t₂ coef (BTree.node children) i)
      = ∑ S ∈ (Finset.univ : Finset (Finset (Fin children.length))),
          (∏ p ∈ S, coef (children.get p)) *
            (∑ i : Fin t, t₂.b i *
              ∏ p ∈ Sᶜ,
                (match children.get p with
                 | BTree.leaf => ∑ j : Fin t, t₂.A i j
                 | BTree.node gc =>
                     ∑ j : Fin t, t₂.A i j *
                       (∑ T : Finset (Fin gc.length),
                         (∏ q ∈ Tᶜ, coef (gc.get q)) *
                         (∏ q ∈ T,
                           (match gc.get q with
                            | BTree.leaf => ∑ k : Fin t, t₂.A j k
                            | BTree.node ggc =>
                                ∑ k : Fin t, t₂.A j k *
                                  (∑ U : Finset (Fin ggc.length),
                                    (∏ r ∈ Uᶜ, coef (ggc.get r)) *
                                    (∏ r ∈ U, ∑ l : Fin t, t₂.A k l *
                                      ButcherProduct.rightAuxAtCoef t₂ coef
                                        (ggc.get r) l))))))) := by
  classical
  have _ht₁ : t₁ = t₁ := rfl
  rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq
    t₁ t₂ coef children]
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
    rfl
  | node gc =>
    refine Finset.sum_congr rfl ?_
    intro j _
    congr 1
    refine Finset.sum_congr rfl ?_
    intro T _
    congr 1
    refine Finset.prod_congr rfl ?_
    intro q _
    generalize gc.get q = c
    cases c with
    | leaf =>
      simp [ButcherProduct.rightAuxAtCoef_leaf]
    | node ggc =>
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum]

/-- bSeries-form corollary of
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_two_level_eq`:
specialize the depth-2 trunk kept-children simplification at
`coef := t₁.bSeries`. -/
theorem ButcherProduct.bSeries_natAdd_node_trunk_kept_two_level_eq
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
                       (∑ T : Finset (Fin gc.length),
                         (∏ q ∈ Tᶜ, t₁.bSeries (gc.get q)) *
                         (∏ q ∈ T,
                           (match gc.get q with
                            | BTree.leaf => ∑ k : Fin t, t₂.A j k
                            | BTree.node ggc =>
                                ∑ k : Fin t, t₂.A j k *
                                  (∑ U : Finset (Fin ggc.length),
                                    (∏ r ∈ Uᶜ, t₁.bSeries (ggc.get r)) *
                                    (∏ r ∈ U, ∑ l : Fin t, t₂.A k l *
                                      ButcherProduct.rightAuxAtCoef t₂
                                        (t₁.bSeries) (ggc.get r) l))))))) := by
  rw [ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef,
      ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_two_level_eq
        t₁ t₂ (t₁.bSeries) children]

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
