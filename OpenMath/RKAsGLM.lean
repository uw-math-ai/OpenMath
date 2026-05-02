import OpenMath.RungeKutta
import OpenMath.GeneralLinearMethod

/-!
# Butcher §502 — Runge–Kutta methods as general linear methods

Embed an `s`-stage Butcher tableau into the general linear method
framework with `r = 1`, `U = 𝟙`, `V = 1`. This is purely structural:
the GLM stage and step equations specialise to the standard RK stage
and update equations.

Reference: J. C. Butcher, *Numerical Methods for Ordinary Differential
Equations*, 2nd ed., §502.
-/

open Finset Real
open scoped NNReal

namespace ButcherTableau

variable {s : ℕ}

/-- §502 — embed an `s`-stage Butcher tableau as a general linear method
with `r = 1`, `U = 1`, `V = 1`. -/
def toGLM (t : ButcherTableau s) : GeneralLinearMethod s 1 where
  A := fun i j => t.A i j
  U := fun _ _ => 1
  B := fun _ j => t.b j
  V := fun _ _ => 1

@[simp] theorem toGLM_A (t : ButcherTableau s) (i j : Fin s) :
    t.toGLM.A i j = t.A i j := rfl

@[simp] theorem toGLM_U (t : ButcherTableau s) (i : Fin s) (k : Fin 1) :
    t.toGLM.U i k = 1 := rfl

@[simp] theorem toGLM_B (t : ButcherTableau s) (k : Fin 1) (j : Fin s) :
    t.toGLM.B k j = t.b j := rfl

@[simp] theorem toGLM_V (t : ButcherTableau s) (k l : Fin 1) :
    t.toGLM.V k l = 1 := rfl

/-- The GLM stage map of `t.toGLM` at the constant input `yIn ≡ y₀`
matches the standard RK stage equation `Y_i = y₀ + h · ∑ A_ij f(Y_j)`. -/
theorem toGLM_stageMap_eq (t : ButcherTableau s) (f : ℝ → ℝ) (h y₀ : ℝ)
    (Y : Fin s → ℝ) (i : Fin s) :
    t.toGLM.stageMap f h (fun _ => y₀) Y i =
      y₀ + h * ∑ j, t.A i j * f (Y j) := by
  simp [GeneralLinearMethod.stageMap_apply, toGLM]; ring

/-- The GLM step of `t.toGLM` at the constant input `yIn ≡ y₀` matches
the standard RK update `y₁ = y₀ + h · ∑ b_j f(Y_j)`. -/
theorem toGLM_step_eq (t : ButcherTableau s) (f : ℝ → ℝ) (h y₀ : ℝ)
    (Y : Fin s → ℝ) (k : Fin 1) :
    t.toGLM.step f h (fun _ => y₀) Y k =
      y₀ + h * ∑ j, t.b j * f (Y j) := by
  simp [GeneralLinearMethod.step_apply, toGLM]; ring

/-- §502 — explicitness is preserved by the embedding. -/
theorem toGLM_isExplicit (t : ButcherTableau s)
    (ht : t.IsExplicit) : t.toGLM.IsExplicit := by
  intro i j hij
  exact ht i j (Fin.le_iff_val_le_val.mpr hij)

/-- §502 — RK stage equations are uniquely solvable under the §341
contraction hypothesis, derived through `toGLM`. -/
theorem toGLM_stageEquations_unique_solution (t : ButcherTableau s)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {h : ℝ} (hh : 0 ≤ h) (y₀ : ℝ)
    (hsmall : h * (L : ℝ) * t.toGLM.rowAbsSumMax < 1) :
    ∃! Y : Fin s → ℝ,
      Y = t.toGLM.stageMap f h (fun _ => y₀) Y := by
  exact t.toGLM.stageEquations_unique_solution hf hh (fun _ => y₀) hsmall

/-- §502 sanity check — every RK embedding is preconsistent (Butcher §510).
The witness is the constant input vector `q ≡ 1`, fixed by the scalar
`V = 1` and sent to the all-ones stage vector by `U = 𝟙`. -/
theorem toGLM_isPreconsistent (t : ButcherTableau s) :
    t.toGLM.IsPreconsistent := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro k
    simp [toGLM_V]
  · intro i
    simp [toGLM_U]

/-- §502 sanity check — every RK embedding is stable (Butcher §510).
The single input quantity is propagated by the scalar `V = 1`, so every
iterate of the propagation map is the identity on `Fin 1 → ℝ`. -/
theorem toGLM_isStable (t : ButcherTableau s) :
    t.toGLM.IsStable := by
  refine ⟨1, zero_le_one, ?_⟩
  intro n q hq
  induction n with
  | zero =>
    intro k
    simpa using hq k
  | succ n ih =>
    intro k
    rw [Function.iterate_succ_apply']
    simp only [toGLM_V, one_mul, Fin.sum_univ_one] at ih ⊢
    exact ih 0

end ButcherTableau
