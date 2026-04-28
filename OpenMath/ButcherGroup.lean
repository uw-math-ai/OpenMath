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

end ButcherTableau
