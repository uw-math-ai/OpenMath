import OpenMath.Adjoint

/-!
# Reflected Runge–Kutta Methods

This file formalizes the reflected tableau from Iserles, Section 4.2
(equation (343a)) and its transfer properties for the simplifying
assumptions `B`, `C`, `D`, `E`.
-/

open Finset Real

namespace ButcherTableau

variable {s : ℕ}

@[ext] theorem ext {t t' : ButcherTableau s}
    (hA : ∀ i j, t.A i j = t'.A i j)
    (hb : ∀ i, t.b i = t'.b i)
    (hc : ∀ i, t.c i = t'.c i) : t = t' := by
  cases t
  cases t'
  simp at hA hb hc
  simp [ButcherTableau.mk.injEq, funext_iff, hA, hb, hc]

/-- The reflected Runge–Kutta tableau `(1 - c, b - A, b)`. -/
def reflect (t : ButcherTableau s) : ButcherTableau s where
  c := fun i => 1 - t.c i
  A := fun i j => t.b j - t.A i j
  b := t.b

@[simp] theorem reflect_c (t : ButcherTableau s) (i : Fin s) :
    t.reflect.c i = 1 - t.c i := rfl

@[simp] theorem reflect_A (t : ButcherTableau s) (i j : Fin s) :
    t.reflect.A i j = t.b j - t.A i j := rfl

@[simp] theorem reflect_b (t : ButcherTableau s) (i : Fin s) :
    t.reflect.b i = t.b i := rfl

@[simp] theorem reflect_reflect (t : ButcherTableau s) :
    t.reflect.reflect = t := by
  refine ButcherTableau.ext ?_ ?_ ?_
  · intro i j
    simp [reflect]
  · intro i
    simp [reflect]
  · intro i
    simp [reflect]

/-- Reflection preserves the weight-sum condition `B(1)`. -/
theorem reflect_order1 (t : ButcherTableau s) :
    t.reflect.order1 ↔ t.order1 := by
  simp [ButcherTableau.order1, reflect]

/-- If `t` satisfies the row-sum condition and `B(1)`, then its reflection does too. -/
theorem reflect_rowSum (t : ButcherTableau s) (hB1 : t.SatisfiesB 1)
    (hrow : t.IsRowSumConsistent) : t.reflect.IsRowSumConsistent := by
  intro i
  have hweights : ∑ j : Fin s, t.b j = 1 := (satisfiesB_one_iff t).mp hB1
  calc
    t.reflect.c i = 1 - t.c i := by simp [reflect]
    _ = (∑ j : Fin s, t.b j) - ∑ j : Fin s, t.A i j := by rw [hweights, hrow i]
    _ = ∑ j : Fin s, (t.b j - t.A i j) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ j : Fin s, t.reflect.A i j := by simp [reflect]

/-- Reflection preserves consistency. -/
theorem reflect_consistent (t : ButcherTableau s) (h : t.IsConsistent) :
    t.reflect.IsConsistent := by
  refine ⟨?_, ?_⟩
  · simpa [reflect, ButcherTableau.order1] using h.weights_sum
  · exact reflect_rowSum t ((satisfiesB_one_iff t).mpr h.weights_sum) h.row_sum

/-- The reflected tableau preserves `B`. Textbook Theorem 343B, equation (343d). -/
theorem reflect_satisfiesB {t : ButcherTableau s} {η : ℕ}
    (hB : t.SatisfiesB η) : t.reflect.SatisfiesB η := by
  sorry

/-- The reflected tableau preserves `C` under `B ∧ C`.
Textbook Theorem 343B, equation (343e). -/
theorem reflect_satisfiesC {t : ButcherTableau s} {η : ℕ}
    (hB : t.SatisfiesB η) (hC : t.SatisfiesC η) : t.reflect.SatisfiesC η := by
  sorry

/-- The reflected tableau preserves `D` under `B ∧ D`.
Textbook Theorem 343B, equation (343f). -/
theorem reflect_satisfiesD {t : ButcherTableau s} {η : ℕ}
    (hB : t.SatisfiesB η) (hD : t.SatisfiesD η) : t.reflect.SatisfiesD η := by
  sorry

/-- The reflected tableau preserves `E` under `B ∧ E`.
Textbook Theorem 343B, equation (343g). -/
theorem reflect_satisfiesE {t : ButcherTableau s} {η ζ : ℕ}
    (hB : t.SatisfiesB (η + ζ)) (hE : t.SatisfiesE η ζ) :
    t.reflect.SatisfiesE η ζ := by
  sorry

end ButcherTableau

/-! ## Concrete reflected tableaux -/

/-- Forward Euler reflects to backward Euler. -/
theorem rkEuler_reflect_eq_implicitEuler : rkEuler.reflect = rkImplicitEuler := by
  refine ButcherTableau.ext ?_ ?_ ?_
  · intro i j
    fin_cases i
    fin_cases j
    simp [ButcherTableau.reflect, rkEuler, rkImplicitEuler]
  · intro i
    fin_cases i
    simp [ButcherTableau.reflect, rkEuler, rkImplicitEuler]
  · intro i
    fin_cases i
    simp [ButcherTableau.reflect, rkEuler, rkImplicitEuler]
