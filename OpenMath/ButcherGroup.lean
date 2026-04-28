import Mathlib
import OpenMath.RungeKutta

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

end IsRKEquivalent

end ButcherTableau
