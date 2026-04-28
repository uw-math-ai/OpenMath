import Mathlib
import OpenMath.RungeKutta

/-!
# Algebraic Properties of Runge--Kutta Methods

This file starts the formalization of Butcher, §38.  It contains the
stage-relabelling equivalence (§381), the tableau product from §380, and the
zero-stage identity laws from §387.  The associativity theorem from §382 is
left as the single deferred proof for the next cycle.
-/

/-- Stage relabelling: a permutation of the stages of a Butcher tableau leaves
the underlying RK method unchanged. -/
def relabel {s : ℕ} (σ : Equiv.Perm (Fin s)) (t : ButcherTableau s) :
    ButcherTableau s where
  A := fun i j => t.A (σ i) (σ j)
  b := fun i => t.b (σ i)
  c := fun i => t.c (σ i)

/-- Reindex a tableau along an equivalence of finite stage sets.  This is used
only to express the canonical `0 + s` rebrand in the left identity law. -/
def reindexStages {s t : ℕ} (e : Fin s ≃ Fin t) (x : ButcherTableau s) :
    ButcherTableau t where
  A := fun i j => x.A (e.symm i) (e.symm j)
  b := fun i => x.b (e.symm i)
  c := fun i => x.c (e.symm i)

/-- Two tableaux of the same stage count are RK-equivalent if they are related
by a stage relabelling (§381). -/
def IsRKEquivalent {s : ℕ} (t₁ t₂ : ButcherTableau s) : Prop :=
  ∃ σ : Equiv.Perm (Fin s), relabel σ t₁ = t₂

private theorem tableau_ext {s : ℕ} {t t' : ButcherTableau s}
    (hA : ∀ i j, t.A i j = t'.A i j)
    (hb : ∀ i, t.b i = t'.b i)
    (hc : ∀ i, t.c i = t'.c i) : t = t' := by
  cases t
  cases t'
  simp at hA hb hc
  simp [ButcherTableau.mk.injEq, funext_iff, hA, hb, hc]

/-- Relabelling composes contravariantly with Lean's `Equiv.trans`
convention. -/
theorem relabel_comp {s : ℕ} (σ τ : Equiv.Perm (Fin s)) (t : ButcherTableau s) :
    relabel (σ.trans τ) t = relabel σ (relabel τ t) := by
  cases t
  simp [relabel, Equiv.trans_apply]

namespace IsRKEquivalent

theorem refl {s : ℕ} (t : ButcherTableau s) : IsRKEquivalent t t := by
  refine ⟨1, ?_⟩
  cases t
  simp [relabel]

theorem symm {s : ℕ} {t₁ t₂ : ButcherTableau s} :
    IsRKEquivalent t₁ t₂ → IsRKEquivalent t₂ t₁ := by
  rintro ⟨σ, hσ⟩
  refine ⟨σ.symm, ?_⟩
  subst hσ
  cases t₁
  simp [relabel]

theorem trans {s : ℕ} {t₁ t₂ t₃ : ButcherTableau s} :
    IsRKEquivalent t₁ t₂ → IsRKEquivalent t₂ t₃ →
      IsRKEquivalent t₁ t₃ := by
  rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩
  subst hσ
  subst hτ
  refine ⟨τ.trans σ, ?_⟩
  simpa using relabel_comp τ σ t₁

/-- RK-equivalence is an equivalence relation on tableaux with a fixed stage
count. -/
theorem equivalence (s : ℕ) : Equivalence (@IsRKEquivalent s) where
  refl := fun t => refl t
  symm := fun h => symm h
  trans := fun h₁ h₂ => trans h₁ h₂

end IsRKEquivalent

/-- The setoid of tableaux modulo stage relabelling. -/
instance rkEquivalentSetoid (s : ℕ) : Setoid (ButcherTableau s) where
  r := IsRKEquivalent
  iseqv := IsRKEquivalent.equivalence s

/-- Butcher composition / product (§380).  The composite of an `s`-stage
tableau followed by a `t`-stage tableau, taken with step weights `(γ₁, γ₂)`, is
an `(s+t)`-stage tableau. -/
def ButcherProduct {s t : ℕ}
    (γ₁ γ₂ : ℝ)
    (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherTableau (s + t) where
  A := fun i j =>
    Fin.addCases
      (motive := fun _ => ℝ)
      (fun i' => Fin.addCases (fun j' => γ₁ * t₁.A i' j')
                              (fun _ => 0) j)
      (fun i' => Fin.addCases (fun j' => γ₁ * t₁.b j')
                              (fun j' => γ₂ * t₂.A i' j') j)
      i
  b := fun i =>
    Fin.addCases (fun i' => γ₁ * t₁.b i') (fun i' => γ₂ * t₂.b i') i
  c := fun i =>
    Fin.addCases (fun i' => γ₁ * t₁.c i') (fun i' => γ₁ + γ₂ * t₂.c i') i

private lemma addCases_zero_left {α : Sort*} {s : ℕ}
    (left : Fin 0 → α) (right : Fin s → α) (i : Fin (0 + s)) :
    Fin.addCases left right i = right ((finCongr (Nat.zero_add s)) i) := by
  cases i using Fin.addCases with
  | left i => exact Fin.elim0 i
  | right i =>
      rw [Fin.addCases_right]
      simp

private lemma addCases_zero_right {α : Sort*} {s : ℕ}
    (left : Fin s → α) (right : Fin 0 → α) (i : Fin (s + 0)) :
    Fin.addCases left right i = left ((finCongr (Nat.add_zero s)) i) := by
  cases i using Fin.addCases with
  | left i =>
      rw [Fin.addCases_left]
      simp
  | right i => exact Fin.elim0 i

/-- §387 left identity: a zero-stage tableau followed by `t` with weights
`(0, 1)` is equivalent to the canonical `0 + s` reindex of `t`. -/
theorem butcherProduct_identity_left {s : ℕ}
    (z : ButcherTableau 0) (t : ButcherTableau s) :
    IsRKEquivalent (ButcherProduct 0 1 z t)
      (reindexStages (finCongr (Nat.zero_add s).symm) t) := by
  refine ⟨1, ?_⟩
  apply tableau_ext
  · intro i j
    simp [relabel, ButcherProduct, reindexStages, addCases_zero_left]
  · intro i
    simp [relabel, ButcherProduct, reindexStages, addCases_zero_left]
  · intro i
    simp [relabel, ButcherProduct, reindexStages, addCases_zero_left]

/-- §387 right identity: `t` followed by a zero-stage tableau with weights
`(1, 0)` is equivalent to `t`. -/
theorem butcherProduct_identity_right {s : ℕ}
    (t : ButcherTableau s) (z : ButcherTableau 0) :
    IsRKEquivalent (ButcherProduct 1 0 t z) t := by
  refine ⟨1, ?_⟩
  apply tableau_ext
  · intro i j
    simp [relabel, ButcherProduct, addCases_zero_right]
  · intro i
    simp [relabel, ButcherProduct, addCases_zero_right]
  · intro i
    simp [relabel, ButcherProduct, addCases_zero_right]

/-- §382: associativity modulo RK-equivalence.  Deferred: the witnessing
permutation is the natural associator on `Fin ((s+t)+u)`, transported across
`finSumFinEquiv` / `Equiv.sumAssoc`. -/
theorem butcherProduct_assoc_modEquiv {s t u : ℕ}
    (γ₁ γ₂ δ₁ δ₂ : ℝ)
    (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (t₃ : ButcherTableau u) :
    IsRKEquivalent
      (ButcherProduct γ₁ γ₂ (ButcherProduct δ₁ δ₂ t₁ t₂) t₃)
      ((Nat.add_assoc s t u).symm ▸
        ButcherProduct γ₁ γ₂ t₁ (ButcherProduct δ₁ δ₂ t₂ t₃)) := by
  sorry
