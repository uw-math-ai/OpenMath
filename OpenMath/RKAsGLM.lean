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

@[simp] theorem toGLM_Aℂ (t : ButcherTableau s) (i j : Fin s) :
    t.toGLM.Aℂ i j = (t.A i j : ℂ) := rfl

@[simp] theorem toGLM_Uℂ (t : ButcherTableau s) (i : Fin s) (k : Fin 1) :
    t.toGLM.Uℂ i k = 1 := rfl

@[simp] theorem toGLM_Bℂ (t : ButcherTableau s) (k : Fin 1) (j : Fin s) :
    t.toGLM.Bℂ k j = (t.b j : ℂ) := rfl

@[simp] theorem toGLM_Vℂ (t : ButcherTableau s) (k l : Fin 1) :
    t.toGLM.Vℂ k l = 1 := rfl

/-- §520 / §502 — scalar Runge--Kutta stability function in the same
total-inverse convention as `GeneralLinearMethod.stabilityMatrix`. -/
noncomputable def stabilityFunction (t : ButcherTableau s) (z : ℂ) : ℂ :=
  let Aℂ : Matrix (Fin s) (Fin s) ℂ := fun i j => (t.A i j : ℂ)
  1 + z * ∑ i, ∑ j,
    (t.b i : ℂ) * ((1 : Matrix (Fin s) (Fin s) ℂ) - z • Aℂ)⁻¹ i j

/-- §502 sanity check for §520: the GLM stability matrix of an RK method
is the `1 × 1` matrix whose sole entry is the scalar RK stability
function. -/
theorem toGLM_stabilityMatrix (t : ButcherTableau s) (z : ℂ) :
    t.toGLM.stabilityMatrix z =
      fun _ _ => t.stabilityFunction z := by
  ext k l
  rw [GeneralLinearMethod.stabilityMatrix_apply]
  have hA : t.toGLM.Aℂ =
      ((fun i j => (t.A i j : ℂ)) : Matrix (Fin s) (Fin s) ℂ) := by
    ext i j
    rfl
  rw [hA]
  simp [stabilityFunction]

private lemma charpoly_fin_one_const (a : ℂ) :
    Matrix.charpoly
        (((fun (_ : Fin 1) (_ : Fin 1) => a) :
          Matrix (Fin 1) (Fin 1) ℂ)) =
      Polynomial.X - Polynomial.C a := by
  rw [Matrix.charpoly]
  simp [Matrix.charmatrix]

private lemma charpoly_fin_one_const_isRoot_iff (a μ : ℂ) :
    (Matrix.charpoly
        (((fun (_ : Fin 1) (_ : Fin 1) => a) :
          Matrix (Fin 1) (Fin 1) ℂ))).IsRoot μ ↔ μ = a := by
  rw [charpoly_fin_one_const]
  simp [Polynomial.IsRoot, sub_eq_zero]

/-- An RK method is A-stable in the GLM sense iff its stability
function satisfies `‖R(z)‖ ≤ 1` on the closed left half-plane. -/
theorem toGLM_isAStable_iff (t : ButcherTableau s) :
    t.toGLM.IsAStable ↔
      ∀ z : ℂ, z.re ≤ 0 → ‖t.stabilityFunction z‖ ≤ 1 := by
  constructor
  · intro h z hz
    exact h z hz (t.stabilityFunction z) (by
      rw [toGLM_stabilityMatrix]
      change (Matrix.charpoly
          (((fun (_ : Fin 1) (_ : Fin 1) => t.stabilityFunction z) :
            Matrix (Fin 1) (Fin 1) ℂ))).IsRoot (t.stabilityFunction z)
      rw [charpoly_fin_one_const_isRoot_iff])
  · intro h z hz μ hμ
    have hroot :
        (Matrix.charpoly
          (((fun (_ : Fin 1) (_ : Fin 1) => t.stabilityFunction z) :
            Matrix (Fin 1) (Fin 1) ℂ))).IsRoot μ := by
      simpa [toGLM_stabilityMatrix] using hμ
    have hμeq : μ = t.stabilityFunction z :=
      (charpoly_fin_one_const_isRoot_iff (t.stabilityFunction z) μ).mp hroot
    simpa [hμeq] using h z hz

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

/-- §502 sanity check — every consistent RK tableau embeds as a
consistent GLM (Butcher §510). Witnesses: `q ≡ 1`, `q' ≡ 0`. The third
conjunct collapses to `∑ j, t.b j = 1`, which is exactly RK weight-sum
consistency. -/
theorem toGLM_isConsistent (t : ButcherTableau s)
    (ht : t.IsConsistent) : t.toGLM.IsConsistent := by
  refine ⟨fun _ => 1, fun _ => 0, ?_, ?_, ?_⟩
  · intro k
    simp [toGLM_V]
  · intro i
    simp [toGLM_U]
  · intro k
    simp only [toGLM_V, toGLM_B, mul_zero, Finset.sum_const_zero, add_zero]
    exact ht.weights_sum

/-- §502 sanity check — every consistent RK tableau embeds as a convergent
GLM (Butcher §512). Combines `toGLM_isConsistent` and `toGLM_isStable`. -/
theorem toGLM_isConvergent (t : ButcherTableau s) (ht : t.IsConsistent) :
    t.toGLM.IsConvergent :=
  ⟨t.toGLM_isConsistent ht, t.toGLM_isStable⟩

end ButcherTableau

/-- Implicit Euler is A-stable after the §502 embedding into GLMs. -/
theorem rkImplicitEuler_toGLM_isAStable :
    (rkImplicitEuler).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  have hne' : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hne : 1 - z * (rkImplicitEuler.A 0 0 : ℂ) ≠ 0 := by
    simpa [rkImplicitEuler] using hne'
  have h := rkImplicitEuler_aStable z hz hne
  have hfun : rkImplicitEuler.stabilityFunction z = rkImplicitEuler.stabilityFn1 z := by
    simp [ButcherTableau.stabilityFunction, ButcherTableau.stabilityFn1, rkImplicitEuler]
    field_simp [hne']
    ring
  simpa [hfun] using h

/-- Implicit midpoint is A-stable after the §502 embedding into GLMs. -/
theorem rkImplicitMidpoint_toGLM_isAStable :
    (rkImplicitMidpoint).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  have hne' : (1 : ℂ) - z * (1/2 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hre
    linarith
  have hne : 1 - z * (rkImplicitMidpoint.A 0 0 : ℂ) ≠ 0 := by
    simpa [rkImplicitMidpoint] using hne'
  have hne2 : (2 : ℂ) - z ≠ 0 := by
    intro h2
    apply hne'
    calc
      (1 : ℂ) - z * (1/2 : ℂ) = ((2 : ℂ) - z) / 2 := by ring
      _ = 0 := by simp [h2]
  have h := rkImplicitMidpoint_aStable z hz hne
  have hfun : rkImplicitMidpoint.stabilityFunction z = rkImplicitMidpoint.stabilityFn1 z := by
    simp [ButcherTableau.stabilityFunction, ButcherTableau.stabilityFn1, rkImplicitMidpoint]
    field_simp [hne', hne2]
    ring
  simpa [hfun] using h
