import OpenMath.RungeKutta
import OpenMath.GeneralLinearMethod
import OpenMath.SDIRK
import OpenMath.SDIRK3
import OpenMath.RadauIIA3
import OpenMath.RadauIA3
import OpenMath.GaussLegendre3
import OpenMath.LobattoIIIA
import OpenMath.LobattoIIIA3
import OpenMath.LobattoIIIB
import OpenMath.LobattoIIIC
import OpenMath.LobattoIIIC3

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

lemma charpoly_fin_one_const_isRoot_iff (a μ : ℂ) :
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

/-! ## §521 — Stability defect for RK as GLM -/

theorem toGLM_qℂ_one (k : Fin 1) :
    GeneralLinearMethod.qℂ (fun _ : Fin 1 => (1 : ℝ)) k = (1 : ℂ) := by
  simp [GeneralLinearMethod.qℂ]

theorem toGLM_stabilityDefect_apply (t : ButcherTableau s)
    (z : ℂ) (k : Fin 1) :
    t.toGLM.stabilityDefect (fun _ => (1 : ℝ)) z k =
      t.stabilityFunction z - Complex.exp z := by
  unfold GeneralLinearMethod.stabilityDefect
  rw [toGLM_stabilityMatrix]
  simp [Matrix.mulVec, dotProduct, GeneralLinearMethod.qℂ,
    Pi.smul_apply, smul_eq_mul, Pi.sub_apply]

theorem toGLM_stabilityDefect_zero (t : ButcherTableau s) :
    t.toGLM.stabilityDefect (fun _ => (1 : ℝ)) 0 = 0 := by
  apply GeneralLinearMethod.stabilityDefect_zero
  intro k
  simp [toGLM_V]

theorem toGLM_stabilityDefect_eq_zero_iff (t : ButcherTableau s)
    (z : ℂ) :
    t.toGLM.stabilityDefect (fun _ => (1 : ℝ)) z = 0 ↔
      t.stabilityFunction z = Complex.exp z := by
  constructor
  · intro h
    have h0 : t.stabilityFunction z - Complex.exp z = 0 := by
      simpa [toGLM_stabilityDefect_apply] using congrFun h 0
    exact sub_eq_zero.mp h0
  · intro h
    funext k
    simp [toGLM_stabilityDefect_apply, h]

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

/-- **§530 / §502 bridge** — Every consistent RK tableau embeds as a
GLM of order ≥ 1. This is a one-line wrapper around
`toGLM_isConsistent`. -/
theorem toGLM_hasOrderGe1 (t : ButcherTableau s)
    (ht : t.IsConsistent) : t.toGLM.HasOrderGe1 :=
  t.toGLM_isConsistent ht

/-- **§530 / §502 bridge** — Every consistent RK tableau of order ≥ 2
embeds as a GLM of order ≥ 2. Witnesses: `q ≡ 1`, `q' ≡ 0`, `q'' ≡ 0`.
The first three identities collapse exactly as in
`toGLM_isConsistent`. The fourth (second-derivative) identity becomes
`2 · ∑ j, t.b j * (∑ i, t.A j i) = 1`, which under `hC.row_sum`
rewrites to `2 · ∑ j, t.b j * t.c j = 1`, i.e. `t.order2`. -/
theorem toGLM_hasOrderGe2 (t : ButcherTableau s)
    (h2 : t.HasOrderGe2) (hC : t.IsConsistent) :
    t.toGLM.HasOrderGe2 := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro k
    simp [toGLM_V]
  · intro i
    simp [toGLM_U]
  · intro k
    simp only [toGLM_V, toGLM_B, mul_zero, Finset.sum_const_zero, add_zero]
    exact h2.1
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb2 : ∑ j, t.b j * t.c j = 1 / 2 := h2.2
    rw [hb2]; norm_num

/-- **§530 / §502 bridge** — Every consistent RK tableau of order ≥ 3
embeds as a GLM of order ≥ 3. Witnesses: `q ≡ 1`, `q' ≡ 0`,
`q'' ≡ 0`, `q''' ≡ 0`. The first four identities collapse exactly as
in `toGLM_hasOrderGe2`. The fifth (third-derivative) identity reduces
under RK Nordsieck (q' = q'' = 0) to
`6 · ∑_j b_j ∑_i A_ji * c_i = 1`, i.e. `t.order3b`. -/
theorem toGLM_hasOrderGe3 (t : ButcherTableau s)
    (h3 : t.HasOrderGe3) (hC : t.IsConsistent) :
    t.toGLM.HasOrderGe3 := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0,
          ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simp [toGLM_V]
  · intro i; simp [toGLM_U]
  · intro k
    simp only [toGLM_V, toGLM_B, mul_zero, Finset.sum_const_zero, add_zero]
    exact h3.1
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb2 : ∑ j, t.b j * t.c j = 1 / 2 := h3.2.1
    rw [hb2]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb3 : ∑ i : Fin s, ∑ j : Fin s, t.b i * t.A i j * t.c j = 1 / 6 :=
      h3.2.2.2
    have key : (∑ j : Fin s, t.b j * ∑ i, t.A j i * t.c i) = 1 / 6 := by
      have hreshape :
          (∑ j : Fin s, t.b j * ∑ i, t.A j i * t.c i)
            = ∑ j : Fin s, ∑ i, t.b j * t.A j i * t.c i := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]; exact hb3
    rw [key]; norm_num

/-- **§530 / §502 bridge** — Every consistent RK tableau of order ≥ 4
embeds as a GLM of order ≥ 4. Witnesses: `q ≡ 1`, `q' ≡ 0`,
`q'' ≡ 0`, `q''' ≡ 0`, `q'''' ≡ 0`. The first five identities collapse
exactly as in `toGLM_hasOrderGe3`. The new sixth (fourth-derivative)
identity reduces under RK Nordsieck (`q' = q'' = q''' = q'''' = 0`)
and the consistency rewrite `∑_i'' A_i'i'' = c_i'` to
`24 · ∑_j b_j (∑_i A_ji (∑_i' A_ii' * c_i')) = 1`, i.e. `t.order4d`
after reshape. -/
theorem toGLM_hasOrderGe4 (t : ButcherTableau s)
    (h4 : t.HasOrderGe4) (hC : t.IsConsistent) :
    t.toGLM.HasOrderGe4 := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simp [toGLM_V]
  · intro i; simp [toGLM_U]
  · intro k
    simp only [toGLM_V, toGLM_B, mul_zero, Finset.sum_const_zero, add_zero]
    exact h4.1
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb2 : ∑ j, t.b j * t.c j = 1 / 2 := h4.2.1
    rw [hb2]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb3 : ∑ i : Fin s, ∑ j : Fin s, t.b i * t.A i j * t.c j = 1 / 6 :=
      h4.2.2.2.1
    have key : (∑ j : Fin s, t.b j * ∑ i, t.A j i * t.c i) = 1 / 6 := by
      have hreshape :
          (∑ j : Fin s, t.b j * ∑ i, t.A j i * t.c i)
            = ∑ j : Fin s, ∑ i, t.b j * t.A j i * t.c i := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]; exact hb3
    rw [key]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb4 : ∑ i : Fin s, ∑ j : Fin s, ∑ k' : Fin s,
        t.b i * t.A i j * t.A j k' * t.c k' = 1 / 24 :=
      h4.2.2.2.2.2.2.2
    have key :
        (∑ j : Fin s, t.b j *
          ∑ i, t.A j i * ∑ i', t.A i i' * t.c i') = 1 / 24 := by
      have hreshape :
          (∑ j : Fin s, t.b j *
            ∑ i, t.A j i * ∑ i', t.A i i' * t.c i')
            = ∑ j : Fin s, ∑ i, ∑ i',
                t.b j * t.A j i * t.A i i' * t.c i' := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]; exact hb4
    rw [key]; norm_num

/-- **§530 / §502 bridge** — Every consistent RK tableau of order ≥ 5
embeds as a GLM of order ≥ 5. Witnesses: `q ≡ 1`, `q' ≡ 0`,
`q'' ≡ 0`, `q''' ≡ 0`, `q'''' ≡ 0`, `q''''' ≡ 0`. The first six
identities collapse exactly as in `toGLM_hasOrderGe4`. The new seventh
(fifth-derivative) identity reduces under RK Nordsieck to
`120 · ∑_j b_j (∑_i A_ji (∑_i' A_ii' (∑_i'' A_i'i'' * c_i''))) = 1`,
i.e. `t.order5i` after reshape. -/
theorem toGLM_hasOrderGe5 (t : ButcherTableau s)
    (h5 : t.HasOrderGe5) (hC : t.IsConsistent) :
    t.toGLM.HasOrderGe5 := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0,
          fun _ => 0, fun _ => 0,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simp [toGLM_V]
  · intro i; simp [toGLM_U]
  · intro k
    simp only [toGLM_V, toGLM_B, mul_zero, Finset.sum_const_zero, add_zero]
    exact h5.1.1
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb2 : ∑ j, t.b j * t.c j = 1 / 2 := h5.1.2.1
    rw [hb2]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb3 : ∑ i : Fin s, ∑ j : Fin s, t.b i * t.A i j * t.c j = 1 / 6 :=
      h5.1.2.2.2.1
    have key : (∑ j : Fin s, t.b j * ∑ i, t.A j i * t.c i) = 1 / 6 := by
      have hreshape :
          (∑ j : Fin s, t.b j * ∑ i, t.A j i * t.c i)
            = ∑ j : Fin s, ∑ i, t.b j * t.A j i * t.c i := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]; exact hb3
    rw [key]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb4 : ∑ i : Fin s, ∑ j : Fin s, ∑ k' : Fin s,
        t.b i * t.A i j * t.A j k' * t.c k' = 1 / 24 :=
      h5.1.2.2.2.2.2.2.2
    have key :
        (∑ j : Fin s, t.b j *
          ∑ i, t.A j i * ∑ i', t.A i i' * t.c i') = 1 / 24 := by
      have hreshape :
          (∑ j : Fin s, t.b j *
            ∑ i, t.A j i * ∑ i', t.A i i' * t.c i')
            = ∑ j : Fin s, ∑ i, ∑ i',
                t.b j * t.A j i * t.A i i' * t.c i' := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]; exact hb4
    rw [key]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb5 : t.order5i := h5.2.2.2.2.2.2.2.2.2
    have key :
        (∑ j : Fin s, t.b j *
          ∑ i, t.A j i *
            ∑ i', t.A i i' *
              ∑ i'', t.A i' i'' * t.c i'') = 1 / 120 := by
      have hreshape :
          (∑ j : Fin s, t.b j *
            ∑ i, t.A j i *
              ∑ i', t.A i i' *
                ∑ i'', t.A i' i'' * t.c i'')
            = ∑ j : Fin s, ∑ i, ∑ i',
                t.b j * t.A j i * t.A i i' *
                  ∑ i'', t.A i' i'' * t.c i'' := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]
      exact hb5
    rw [key]; norm_num

/-- §530 — Embed an `s`-stage RK tableau of order ≥ 6 as a general linear method
of order ≥ 6. The first seven identities collapse exactly as in
`toGLM_hasOrderGe5`. The new eighth (sixth-derivative) identity reduces under
RK Nordsieck to
`720 · ∑_j b_j (∑_i A_ji (∑_i' A_ii' (∑_i'' A_i'i'' (∑_i''' A_i''i''' * c_i''')))) = 1`,
i.e. `t.order6t` after reshape. -/
theorem toGLM_hasOrderGe6 (t : ButcherTableau s)
    (h6 : t.HasOrderGe6) (hC : t.IsConsistent) :
    t.toGLM.HasOrderGe6 := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0,
          fun _ => 0, fun _ => 0, fun _ => 0,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simp [toGLM_V]
  · intro i; simp [toGLM_U]
  · intro k
    simp only [toGLM_V, toGLM_B, mul_zero, Finset.sum_const_zero, add_zero]
    exact h6.1.1.1
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb2 : ∑ j, t.b j * t.c j = 1 / 2 := h6.1.1.2.1
    rw [hb2]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb3 : ∑ i : Fin s, ∑ j : Fin s, t.b i * t.A i j * t.c j = 1 / 6 :=
      h6.1.1.2.2.2.1
    have key : (∑ j : Fin s, t.b j * ∑ i, t.A j i * t.c i) = 1 / 6 := by
      have hreshape :
          (∑ j : Fin s, t.b j * ∑ i, t.A j i * t.c i)
            = ∑ j : Fin s, ∑ i, t.b j * t.A j i * t.c i := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]; exact hb3
    rw [key]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb4 : ∑ i : Fin s, ∑ j : Fin s, ∑ k' : Fin s,
        t.b i * t.A i j * t.A j k' * t.c k' = 1 / 24 :=
      h6.1.1.2.2.2.2.2.2.2
    have key :
        (∑ j : Fin s, t.b j *
          ∑ i, t.A j i * ∑ i', t.A i i' * t.c i') = 1 / 24 := by
      have hreshape :
          (∑ j : Fin s, t.b j *
            ∑ i, t.A j i * ∑ i', t.A i i' * t.c i')
            = ∑ j : Fin s, ∑ i, ∑ i',
                t.b j * t.A j i * t.A i i' * t.c i' := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]; exact hb4
    rw [key]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb5 : t.order5i := h6.1.2.2.2.2.2.2.2.2.2
    have key :
        (∑ j : Fin s, t.b j *
          ∑ i, t.A j i *
            ∑ i', t.A i i' *
              ∑ i'', t.A i' i'' * t.c i'') = 1 / 120 := by
      have hreshape :
          (∑ j : Fin s, t.b j *
            ∑ i, t.A j i *
              ∑ i', t.A i i' *
                ∑ i'', t.A i' i'' * t.c i'')
            = ∑ j : Fin s, ∑ i, ∑ i',
                t.b j * t.A j i * t.A i i' *
                  ∑ i'', t.A i' i'' * t.c i'' := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]
      exact hb5
    rw [key]; norm_num
  · intro k
    simp only [toGLM_V, toGLM_B, toGLM_A, toGLM_U, mul_zero,
      Finset.sum_const_zero, add_zero]
    have hcj : ∀ j, (∑ i, t.A j i) = t.c j := fun j => (hC.row_sum j).symm
    simp_rw [hcj]
    have hb6 : t.order6t :=
      h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have key :
        (∑ j : Fin s, t.b j *
          ∑ i, t.A j i *
            ∑ i', t.A i i' *
              ∑ i'', t.A i' i'' *
                ∑ i''', t.A i'' i''' * t.c i''') = 1 / 720 := by
      have hreshape :
          (∑ j : Fin s, t.b j *
            ∑ i, t.A j i *
              ∑ i', t.A i i' *
                ∑ i'', t.A i' i'' *
                  ∑ i''', t.A i'' i''' * t.c i''')
            = ∑ j : Fin s, ∑ i, ∑ i',
                t.b j * t.A j i * t.A i i' *
                  ∑ i'', t.A i' i'' *
                    ∑ i''', t.A i'' i''' * t.c i''' := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hreshape]
      exact hb6
    rw [key]; norm_num

end ButcherTableau

/-- **§530 sanity** — `rkEuler` (forward Euler) embeds as a GLM
of order ≥ 1. -/
theorem rkEuler_toGLM_hasOrderGe1 :
    (rkEuler).toGLM.HasOrderGe1 :=
  rkEuler.toGLM_hasOrderGe1 rkEuler_consistent

/-- **§530 sanity** — `rkImplicitMidpoint` embeds as a GLM
of order ≥ 1. -/
theorem rkImplicitMidpoint_toGLM_hasOrderGe1 :
    (rkImplicitMidpoint).toGLM.HasOrderGe1 :=
  rkImplicitMidpoint.toGLM_hasOrderGe1 rkImplicitMidpoint_consistent

/-- **§530 sanity** — `rkImplicitMidpoint` embeds as a GLM
of order ≥ 2. (Order 2 is the sharp order of implicit midpoint;
do **not** state an order-≥ 3 analogue for this method.) -/
theorem rkImplicitMidpoint_toGLM_hasOrderGe2 :
    (rkImplicitMidpoint).toGLM.HasOrderGe2 :=
  rkImplicitMidpoint.toGLM_hasOrderGe2
    rkImplicitMidpoint_order2 rkImplicitMidpoint_consistent

/-- §530 sanity — Heun's method (explicit RK2) embeds as a GLM
of order ≥ 2. -/
theorem rkHeun_toGLM_hasOrderGe2 :
    rkHeun.toGLM.HasOrderGe2 :=
  rkHeun.toGLM_hasOrderGe2 rkHeun_order2 rkHeun_consistent

/-- §530 sanity — SDIRK2 (the singly-diagonally-implicit RK2 method)
embeds as a GLM of order ≥ 2. -/
theorem rkSDIRK2_toGLM_hasOrderGe2 :
    rkSDIRK2.toGLM.HasOrderGe2 :=
  rkSDIRK2.toGLM_hasOrderGe2 rkSDIRK2_order2 rkSDIRK2_consistent

/-- §530 sanity — the explicit midpoint method embeds as a GLM
of order ≥ 2. -/
theorem rkMidpoint_toGLM_hasOrderGe2 :
    rkMidpoint.toGLM.HasOrderGe2 :=
  rkMidpoint.toGLM_hasOrderGe2 rkMidpoint_order2 rkMidpoint_consistent

/-- §530 sanity — the classical 4-stage RK4 method has order 4 and so
embeds as a GLM of order ≥ 2 (project `HasOrderGe4` to `HasOrderGe2`). -/
theorem rkRK4_toGLM_hasOrderGe2 :
    rk4.toGLM.HasOrderGe2 :=
  rk4.toGLM_hasOrderGe2
    ⟨rk4_order4.1, rk4_order4.2.1⟩ rk4_consistent

/-- §530 sanity — the 2-stage Gauss–Legendre method has order 4 and so
embeds as a GLM of order ≥ 2. -/
theorem rkGaussLegendre2_toGLM_hasOrderGe2 :
    rkGaussLegendre2.toGLM.HasOrderGe2 :=
  rkGaussLegendre2.toGLM_hasOrderGe2
    ⟨rkGaussLegendre2_order4.1, rkGaussLegendre2_order4.2.1⟩
    rkGaussLegendre2_consistent

/-- §530 sanity — the 3-stage Gauss–Legendre method has order 6 (≥ 4)
and so embeds as a GLM of order ≥ 2. -/
theorem rkGaussLegendre3_toGLM_hasOrderGe2 :
    rkGaussLegendre3.toGLM.HasOrderGe2 :=
  rkGaussLegendre3.toGLM_hasOrderGe2
    ⟨rkGaussLegendre3_order4.1, rkGaussLegendre3_order4.2.1⟩
    rkGaussLegendre3_consistent

/-- §530 sanity — `rkSDIRK3` (singly diagonally implicit RK3) embeds
as a GLM of order ≥ 3. Order 3 is sharp for SDIRK3
(`rkSDIRK3_not_order4`); do **not** state an order-≥ 4 analogue. -/
theorem rkSDIRK3_toGLM_hasOrderGe3 :
    rkSDIRK3.toGLM.HasOrderGe3 :=
  rkSDIRK3.toGLM_hasOrderGe3 rkSDIRK3_order3 rkSDIRK3_consistent

/-- §530 sanity — RK4 has order 4 and so embeds as a GLM
of order ≥ 3. The order-3 hypothesis is extracted from the order-4
certificate. -/
theorem rkRK4_toGLM_hasOrderGe3 :
    rk4.toGLM.HasOrderGe3 :=
  rk4.toGLM_hasOrderGe3
    ⟨rk4_order4.1, rk4_order4.2.1,
     rk4_order4.2.2.1, rk4_order4.2.2.2.1⟩
    rk4_consistent

/-- §530 sanity — Gauss–Legendre 2-stage has order 4 and so embeds
as a GLM of order ≥ 3. The order-3 hypothesis is extracted from the
order-4 certificate. -/
theorem rkGaussLegendre2_toGLM_hasOrderGe3 :
    rkGaussLegendre2.toGLM.HasOrderGe3 :=
  rkGaussLegendre2.toGLM_hasOrderGe3
    ⟨rkGaussLegendre2_order4.1,
     rkGaussLegendre2_order4.2.1,
     rkGaussLegendre2_order4.2.2.1,
     rkGaussLegendre2_order4.2.2.2.1⟩
    rkGaussLegendre2_consistent

/-- §530 sanity — Gauss–Legendre 3-stage has order 6 and so embeds
as a GLM of order ≥ 3. -/
theorem rkGaussLegendre3_toGLM_hasOrderGe3 :
    rkGaussLegendre3.toGLM.HasOrderGe3 :=
  rkGaussLegendre3.toGLM_hasOrderGe3
    ⟨rkGaussLegendre3_order4.1,
     rkGaussLegendre3_order4.2.1,
     rkGaussLegendre3_order4.2.2.1,
     rkGaussLegendre3_order4.2.2.2.1⟩
    rkGaussLegendre3_consistent

/-- §530 sanity — RK4 has order 4 and so embeds as a GLM
of order ≥ 4. -/
theorem rkRK4_toGLM_hasOrderGe4 :
    rk4.toGLM.HasOrderGe4 :=
  rk4.toGLM_hasOrderGe4 rk4_order4 rk4_consistent

/-- §530 sanity — Gauss–Legendre 2-stage has order 4 and so embeds
as a GLM of order ≥ 4. -/
theorem rkGaussLegendre2_toGLM_hasOrderGe4 :
    rkGaussLegendre2.toGLM.HasOrderGe4 :=
  rkGaussLegendre2.toGLM_hasOrderGe4
    rkGaussLegendre2_order4 rkGaussLegendre2_consistent

/-- §530 sanity — Gauss–Legendre 3-stage has order 6 (≥ 4) and so
embeds as a GLM of order ≥ 4. -/
theorem rkGaussLegendre3_toGLM_hasOrderGe4 :
    rkGaussLegendre3.toGLM.HasOrderGe4 :=
  rkGaussLegendre3.toGLM_hasOrderGe4
    rkGaussLegendre3_order4 rkGaussLegendre3_consistent

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

/-- Bridge from the canonical GLM-side `stabilityFunction` to the
classical scalar `sdirk2StabilityFn` on the SDIRK2 tableau. -/
theorem rkSDIRK2_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkSDIRK2.stabilityFunction z = sdirk2StabilityFn z := by
  have hl_pos : (0 : ℝ) < sdirk2Lambda := sdirk2Lambda_pos
  have hne1 : (1 : ℂ) - z * (sdirk2Lambda : ℝ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hre
    nlinarith [hl_pos, hz]
  have hne1' : (1 : ℂ) - z * (sdirk2Lambda : ℂ) ≠ 0 := by exact_mod_cast hne1
  rw [ButcherTableau.stabilityFunction]
  have hM :
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - z •
          (Matrix.of (fun i j => ((rkSDIRK2.A i j : ℝ) : ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ)) =
      !![1 - z * (sdirk2Lambda : ℂ), 0;
         -(z * (1 - (sdirk2Lambda : ℂ))), 1 - z * (sdirk2Lambda : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rkSDIRK2, Matrix.one_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one]
  change 1 + z * ∑ i, ∑ j,
      (rkSDIRK2.b i : ℂ) *
        ((1 - z • (Matrix.of (fun i j => ((rkSDIRK2.A i j : ℝ) : ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ))⁻¹) i j = sdirk2StabilityFn z
  rw [hM]
  have hdet : (!![1 - z * (sdirk2Lambda : ℂ), 0;
                  -(z * (1 - (sdirk2Lambda : ℂ))), 1 - z * (sdirk2Lambda : ℂ)] :
                  Matrix (Fin 2) (Fin 2) ℂ).det = (1 - z * (sdirk2Lambda : ℂ)) ^ 2 := by
    simp [Matrix.det_fin_two_of]; ring
  rw [Matrix.inv_def]
  simp only [Matrix.adjugate_fin_two_of, hdet, Ring.inverse_eq_inv']
  simp only [Fin.sum_univ_two, rkSDIRK2, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.smul_of, Matrix.smul_cons, smul_eq_mul,
             Matrix.cons_val_fin_one, Matrix.of_apply,
             sdirk2StabilityFn, sdirk2Num, sdirk2Denom]
  push_cast
  field_simp
  ring

/-- 2-stage SDIRK is A-stable after the §502 embedding into GLMs. -/
theorem rkSDIRK2_toGLM_isAStable :
    (rkSDIRK2).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkSDIRK2_stabilityFunction_eq z hz]
  exact sdirk2_aStable z hz

/-- Bridge from the canonical GLM-side `stabilityFunction` to the
classical scalar `sdirk3StabilityFn` on the SDIRK3 tableau. -/
theorem rkSDIRK3_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkSDIRK3.stabilityFunction z = sdirk3StabilityFn z := by
  have hl_pos : (0 : ℝ) < sdirk3Lambda := sdirk3Lambda_pos
  have h1ml_ne : (1 - sdirk3Lambda : ℝ) ≠ 0 := one_sub_sdirk3Lambda_ne_zero
  have h1ml_ne_C : (1 - (sdirk3Lambda : ℂ)) ≠ 0 := by exact_mod_cast h1ml_ne
  have hne1 : (1 : ℂ) - z * (sdirk3Lambda : ℝ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hre
    nlinarith [hl_pos, hz]
  have hne1' : (1 : ℂ) - z * (sdirk3Lambda : ℂ) ≠ 0 := by exact_mod_cast hne1
  rw [ButcherTableau.stabilityFunction]
  have hM :
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) - z •
          (Matrix.of (fun i j => ((rkSDIRK3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ)) =
      !![1 - z * (sdirk3Lambda : ℂ), 0, 0;
         -(z * ((1 - (sdirk3Lambda : ℂ)) / 2)), 1 - z * (sdirk3Lambda : ℂ), 0;
         -(z * ((sdirk3Lambda : ℂ) * (2 - (sdirk3Lambda : ℂ)) / (1 - (sdirk3Lambda : ℂ)))),
         -(z * ((2 * (sdirk3Lambda : ℂ) ^ 2 - 4 * (sdirk3Lambda : ℂ) + 1) /
                  (1 - (sdirk3Lambda : ℂ)))),
         1 - z * (sdirk3Lambda : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rkSDIRK3, Matrix.one_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one]
  change 1 + z * ∑ i, ∑ j,
      (rkSDIRK3.b i : ℂ) *
        ((1 - z • (Matrix.of (fun i j => ((rkSDIRK3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ))⁻¹) i j = sdirk3StabilityFn z
  rw [hM]
  have hdet :
      (!![1 - z * (sdirk3Lambda : ℂ), 0, 0;
          -(z * ((1 - (sdirk3Lambda : ℂ)) / 2)), 1 - z * (sdirk3Lambda : ℂ), 0;
          -(z * ((sdirk3Lambda : ℂ) * (2 - (sdirk3Lambda : ℂ)) / (1 - (sdirk3Lambda : ℂ)))),
          -(z * ((2 * (sdirk3Lambda : ℂ) ^ 2 - 4 * (sdirk3Lambda : ℂ) + 1) /
                   (1 - (sdirk3Lambda : ℂ)))),
          1 - z * (sdirk3Lambda : ℂ)] :
            Matrix (Fin 3) (Fin 3) ℂ).det = (1 - z * (sdirk3Lambda : ℂ)) ^ 3 := by
    rw [Matrix.det_fin_three]
    simp; ring
  rw [Matrix.inv_def]
  simp only [Matrix.adjugate_fin_three_of, hdet, Ring.inverse_eq_inv']
  simp only [Fin.sum_univ_three, rkSDIRK3, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.smul_of, Matrix.smul_cons, smul_eq_mul,
             Matrix.cons_val_fin_one, Matrix.of_apply,
             sdirk3StabilityFn, sdirk3Num, sdirk3Denom]
  push_cast
  field_simp
  ring

/-- 3-stage SDIRK (Alexander) is A-stable after the §502 embedding into GLMs. -/
theorem rkSDIRK3_toGLM_isAStable :
    (rkSDIRK3).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkSDIRK3_stabilityFunction_eq z hz]
  exact sdirk3_aStable z hz

/-- Bridge from the canonical GLM-side `stabilityFunction` to the
classical scalar `radauIIA3StabilityFn` on the Radau IIA tableau. -/
theorem rkRadauIIA3_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkRadauIIA3.stabilityFunction z = radauIIA3StabilityFn z := by
  let s : ℂ := ((Real.sqrt 6 : ℝ) : ℂ)
  have hs6_R : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)
  have hs6_C : s ^ 2 = 6 := by
    dsimp [s]
    exact_mod_cast hs6_R
  have hD : radauIIA3Denom z ≠ 0 := radauIIA3_denom_ne_zero z hz
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
      !![1 - z * ((88 - 7 * s) / 360),
         -(z * ((296 - 169 * s) / 1800)),
         -(z * ((-2 + 3 * s) / 225));
         -(z * ((296 + 169 * s) / 1800)),
         1 - z * ((88 + 7 * s) / 360),
         -(z * ((-2 - 3 * s) / 225));
         -(z * ((16 - s) / 36)),
         -(z * ((16 + s) / 36)),
         1 - z * ((1 : ℂ) / 9)]
  rw [ButcherTableau.stabilityFunction]
  have hM :
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) - z •
          (Matrix.of (fun i j => ((rkRadauIIA3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ)) = M := by
    subst M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rkRadauIIA3, s, Matrix.cons_val_zero, Matrix.cons_val_one]
  change 1 + z * ∑ i, ∑ j,
      (rkRadauIIA3.b i : ℂ) *
        ((1 - z • (Matrix.of (fun i j => ((rkRadauIIA3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ))⁻¹) i j = radauIIA3StabilityFn z
  rw [hM]
  have hdet : M.det = radauIIA3Denom z := by
    subst M
    rw [Matrix.det_fin_three]
    unfold radauIIA3Denom
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (norm := ring_nf) (-z ^ 2 * (93 * z - 413) / 45000) * hs6_C
  have hsum :
      ∑ i, ∑ j, (rkRadauIIA3.b i : ℂ) * M.adjugate i j =
        (93 * s ^ 2 * z ^ 2 + 250 * s ^ 2 * z + 192 * z ^ 2 - 6000 * z + 45000) /
          45000 := by
    subst M
    simp [Fin.sum_univ_three, rkRadauIIA3, Matrix.adjugate_fin_three_of,
          Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ((Real.sqrt 6 : ℝ) : ℂ) = s from rfl]
    ring_nf
  have hsumInv :
      ∑ i, ∑ j, (rkRadauIIA3.b i : ℂ) *
          ((radauIIA3Denom z)⁻¹ * M.adjugate i j) =
        (radauIIA3Denom z)⁻¹ *
          ((93 * s ^ 2 * z ^ 2 + 250 * s ^ 2 * z + 192 * z ^ 2 - 6000 * z + 45000) /
            45000) := by
    rw [← hsum]
    simp only [Fin.sum_univ_three]
    ring
  rw [Matrix.inv_def]
  simp only [hdet, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hsumInv]
  have hnum :
      radauIIA3Denom z +
          z * ((93 * s ^ 2 * z ^ 2 + 250 * s ^ 2 * z + 192 * z ^ 2 - 6000 * z + 45000) /
            45000) =
        radauIIA3Num z := by
    unfold radauIIA3Denom radauIIA3Num
    linear_combination (norm := ring_nf) (z ^ 2 * (93 * z + 250) / 45000) * hs6_C
  calc
    1 + z * ((radauIIA3Denom z)⁻¹ *
        ((93 * s ^ 2 * z ^ 2 + 250 * s ^ 2 * z + 192 * z ^ 2 - 6000 * z + 45000) /
          45000)) =
        (radauIIA3Denom z)⁻¹ *
          (radauIIA3Denom z + z *
            ((93 * s ^ 2 * z ^ 2 + 250 * s ^ 2 * z + 192 * z ^ 2 - 6000 * z + 45000) /
              45000)) := by
      rw [mul_add]
      rw [inv_mul_cancel₀ hD]
      ring
    _ = (radauIIA3Denom z)⁻¹ * radauIIA3Num z := by rw [hnum]
    _ = radauIIA3StabilityFn z := by
      unfold radauIIA3StabilityFn
      rw [div_eq_mul_inv]
      ring

/-- 3-stage Radau IIA is A-stable after the §502 embedding into GLMs. -/
theorem rkRadauIIA3_toGLM_isAStable :
    (rkRadauIIA3).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkRadauIIA3_stabilityFunction_eq z hz]
  exact radauIIA3_aStable z hz

/-- Bridge from the canonical GLM-side `stabilityFunction` to the
classical scalar `gl3StabilityFn` on the Gauss--Legendre 3-stage tableau. -/
theorem rkGaussLegendre3_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkGaussLegendre3.stabilityFunction z = gl3StabilityFn z := by
  let s : ℂ := ((Real.sqrt 15 : ℝ) : ℂ)
  have hs15_R : Real.sqrt 15 ^ 2 = 15 :=
    Real.sq_sqrt (by norm_num : (15 : ℝ) ≥ 0)
  have hs15_C : s ^ 2 = 15 := by
    dsimp [s]
    exact_mod_cast hs15_R
  have hD : gl3Q z ≠ 0 := gl3_Q_ne_zero z hz
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
      !![1 - z * (5 / 36),
         -(z * (2 / 9 - s / 15)),
         -(z * (5 / 36 - s / 30));
         -(z * (5 / 36 + s / 24)),
         1 - z * (2 / 9),
         -(z * (5 / 36 - s / 24));
         -(z * (5 / 36 + s / 30)),
         -(z * (2 / 9 + s / 15)),
         1 - z * (5 / 36)]
  rw [ButcherTableau.stabilityFunction]
  have hM :
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) - z •
          (Matrix.of (fun i j => ((rkGaussLegendre3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ)) = M := by
    subst M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rkGaussLegendre3, s, Matrix.cons_val_zero, Matrix.cons_val_one]
  change 1 + z * ∑ i, ∑ j,
      (rkGaussLegendre3.b i : ℂ) *
        ((1 - z • (Matrix.of (fun i j => ((rkGaussLegendre3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ))⁻¹) i j = gl3StabilityFn z
  rw [hM]
  have hdet : M.det = gl3Q z / 120 := by
    subst M
    rw [Matrix.det_fin_three]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, gl3Q]
    linear_combination (norm := ring_nf) (z ^ 2 * (12 - z) / 1800) * hs15_C
  have hsum :
      ∑ i, ∑ j, (rkGaussLegendre3.b i : ℂ) * M.adjugate i j =
        (60 + z ^ 2) / 60 := by
    subst M
    simp [Fin.sum_univ_three, rkGaussLegendre3, Matrix.adjugate_fin_three_of,
          Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (norm := ring_nf) (z ^ 2 / 900) * hs15_C
  have hsumInv :
      ∑ i, ∑ j, (rkGaussLegendre3.b i : ℂ) *
          ((gl3Q z / 120)⁻¹ * M.adjugate i j) =
        (gl3Q z / 120)⁻¹ * ((60 + z ^ 2) / 60) := by
    rw [← hsum]
    simp only [Fin.sum_univ_three]
    ring
  rw [Matrix.inv_def]
  simp only [hdet, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hsumInv]
  have hPsub : gl3P z - gl3Q z = 2 * z * (60 + z ^ 2) := gl3_P_sub_Q z
  have hnum : gl3Q z + z * 2 * (60 + z ^ 2) = gl3P z := by linear_combination -hPsub
  have h_inv_div : ((gl3Q z) / 120)⁻¹ = 120 * (gl3Q z)⁻¹ := by
    rw [inv_div]
    ring
  calc
    1 + z * ((gl3Q z / 120)⁻¹ * ((60 + z ^ 2) / 60)) =
        (gl3Q z)⁻¹ * (gl3Q z + z * 2 * (60 + z ^ 2)) := by
      rw [h_inv_div, mul_add, inv_mul_cancel₀ hD]
      ring
    _ = (gl3Q z)⁻¹ * gl3P z := by rw [hnum]
    _ = gl3StabilityFn z := by
      unfold gl3StabilityFn
      rw [div_eq_mul_inv]
      ring

/-- 3-stage Gauss--Legendre is A-stable after the §502 embedding into GLMs. -/
theorem rkGaussLegendre3_toGLM_isAStable :
    (rkGaussLegendre3).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkGaussLegendre3_stabilityFunction_eq z hz]
  exact gl3_aStable z hz

/-- Bridge from the canonical GLM-side `stabilityFunction` to the
classical scalar `lobIIIAStabilityFn` on the Lobatto IIIA 2-stage tableau. -/
theorem rkLobattoIIIA2_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkLobattoIIIA2.stabilityFunction z = lobIIIAStabilityFn z := by
  have hne1 : (1 : ℂ) - z * (1/2 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hre
    nlinarith [hz]
  have hD : (2 : ℂ) - z ≠ 0 := by
    intro h
    apply hne1
    calc
      (1 : ℂ) - z * (1/2 : ℂ) = ((2 : ℂ) - z) / 2 := by ring
      _ = 0 := by simp [h]
  rw [ButcherTableau.stabilityFunction]
  have hM :
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - z •
          (Matrix.of (fun i j => ((rkLobattoIIIA2.A i j : ℝ) : ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ)) =
      !![1, 0; -(z * (1/2 : ℂ)), 1 - z * (1/2 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rkLobattoIIIA2, Matrix.cons_val_zero, Matrix.cons_val_one]
  change 1 + z * ∑ i, ∑ j,
      (rkLobattoIIIA2.b i : ℂ) *
        ((1 - z • (Matrix.of (fun i j => ((rkLobattoIIIA2.A i j : ℝ) : ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ))⁻¹) i j = lobIIIAStabilityFn z
  rw [hM]
  have hdet : (!![1, 0; -(z * (1/2 : ℂ)), 1 - z * (1/2 : ℂ)] :
                  Matrix (Fin 2) (Fin 2) ℂ).det = 1 - z * (1/2 : ℂ) := by
    simp [Matrix.det_fin_two_of]
  rw [Matrix.inv_def]
  simp only [Matrix.adjugate_fin_two_of, hdet, Ring.inverse_eq_inv']
  simp only [Fin.sum_univ_two, rkLobattoIIIA2,
             Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.smul_of, Matrix.smul_cons, smul_eq_mul,
             Matrix.cons_val_fin_one, Matrix.of_apply,
             lobIIIAStabilityFn, lobIIIANum, lobIIIADenom]
  push_cast
  field_simp [hne1, hD]
  ring

/-- Lobatto IIIA 2-stage is A-stable after the §502 embedding into GLMs. -/
theorem rkLobattoIIIA2_toGLM_isAStable :
    (rkLobattoIIIA2).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkLobattoIIIA2_stabilityFunction_eq z hz]
  exact lobIIIA_aStable z hz

/-- Bridge from the canonical GLM-side `stabilityFunction` to the
classical scalar `lobIIICStabilityFn` on the Lobatto IIIC 2-stage tableau. -/
theorem rkLobattoIIIC2_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkLobattoIIIC2.stabilityFunction z = lobIIICStabilityFn z := by
  have hD : lobIIICDenom z ≠ 0 := lobIIIC_denom_ne_zero z hz
  let M : Matrix (Fin 2) (Fin 2) ℂ :=
      !![1 - z * (1/2 : ℂ), z * (1/2 : ℂ);
         -(z * (1/2 : ℂ)), 1 - z * (1/2 : ℂ)]
  rw [ButcherTableau.stabilityFunction]
  have hM :
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - z •
          (Matrix.of (fun i j => ((rkLobattoIIIC2.A i j : ℝ) : ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ)) = M := by
    subst M
    ext i j
    fin_cases i <;> fin_cases j
    · simp [rkLobattoIIIC2, Matrix.cons_val_zero]
    · simp [rkLobattoIIIC2, Matrix.cons_val_one]
      ring
    · simp [rkLobattoIIIC2, Matrix.cons_val_one]
    · simp [rkLobattoIIIC2, Matrix.cons_val_one]
  change 1 + z * ∑ i, ∑ j,
      (rkLobattoIIIC2.b i : ℂ) *
        ((1 - z • (Matrix.of (fun i j => ((rkLobattoIIIC2.A i j : ℝ) : ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ))⁻¹) i j = lobIIICStabilityFn z
  rw [hM]
  have hdet : M.det = lobIIICDenom z / 2 := by
    subst M
    simp [Matrix.det_fin_two_of, lobIIICDenom]
    ring
  have hsum :
      ∑ i, ∑ j, (rkLobattoIIIC2.b i : ℂ) * M.adjugate i j =
        1 - z * (1/2 : ℂ) := by
    subst M
    simp [Fin.sum_univ_two, rkLobattoIIIC2, Matrix.adjugate_fin_two_of,
          Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hsumInv :
      ∑ i, ∑ j, (rkLobattoIIIC2.b i : ℂ) *
          ((lobIIICDenom z / 2)⁻¹ * M.adjugate i j) =
        (lobIIICDenom z / 2)⁻¹ * (1 - z * (1/2 : ℂ)) := by
    rw [← hsum]
    simp only [Fin.sum_univ_two]
    ring
  rw [Matrix.inv_def]
  simp only [hdet, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hsumInv]
  have hnum : lobIIICDenom z + z * (2 - z) = 2 := by
    unfold lobIIICDenom
    ring
  have h_inv_div : (lobIIICDenom z / 2)⁻¹ = 2 * (lobIIICDenom z)⁻¹ := by
    rw [inv_div]
    ring
  calc
    1 + z * ((lobIIICDenom z / 2)⁻¹ * (1 - z * (1/2 : ℂ))) =
        (lobIIICDenom z)⁻¹ * (lobIIICDenom z + z * (2 - z)) := by
      rw [h_inv_div, mul_add, inv_mul_cancel₀ hD]
      ring
    _ = (lobIIICDenom z)⁻¹ * 2 := by rw [hnum]
    _ = lobIIICStabilityFn z := by
      unfold lobIIICStabilityFn
      rw [div_eq_mul_inv]
      ring

/-- Lobatto IIIC 2-stage is A-stable after the §502 embedding into GLMs. -/
theorem rkLobattoIIIC2_toGLM_isAStable :
    (rkLobattoIIIC2).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkLobattoIIIC2_stabilityFunction_eq z hz]
  exact lobIIIC_aStable z hz

/-- Bridge from the canonical GLM-side `stabilityFunction` to the
classical scalar `lobIIIAStabilityFn` on the Lobatto IIIB 2-stage tableau.
Lobatto IIIB shares the IIIA stability function `(2 + z) / (2 - z)`. -/
theorem rkLobattoIIIB2_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkLobattoIIIB2.stabilityFunction z = lobIIIAStabilityFn z := by
  have hne1 : (1 : ℂ) - z * (1/2 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hre
    nlinarith [hz]
  have hD : (2 : ℂ) - z ≠ 0 := by
    intro h
    apply hne1
    calc
      (1 : ℂ) - z * (1/2 : ℂ) = ((2 : ℂ) - z) / 2 := by ring
      _ = 0 := by simp [h]
  rw [ButcherTableau.stabilityFunction]
  have hM :
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - z •
          (Matrix.of (fun i j => ((rkLobattoIIIB2.A i j : ℝ) : ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ)) =
      !![1 - z * (1/2 : ℂ), 0; -(z * (1/2 : ℂ)), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rkLobattoIIIB2, Matrix.cons_val_zero, Matrix.cons_val_one]
  change 1 + z * ∑ i, ∑ j,
      (rkLobattoIIIB2.b i : ℂ) *
        ((1 - z • (Matrix.of (fun i j => ((rkLobattoIIIB2.A i j : ℝ) : ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ))⁻¹) i j = lobIIIAStabilityFn z
  rw [hM]
  have hdet : (!![1 - z * (1/2 : ℂ), 0; -(z * (1/2 : ℂ)), 1] :
                  Matrix (Fin 2) (Fin 2) ℂ).det = 1 - z * (1/2 : ℂ) := by
    simp [Matrix.det_fin_two_of]
  rw [Matrix.inv_def]
  simp only [Matrix.adjugate_fin_two_of, hdet, Ring.inverse_eq_inv']
  simp only [Fin.sum_univ_two, rkLobattoIIIB2,
             Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.smul_of, Matrix.smul_cons, smul_eq_mul,
             Matrix.cons_val_fin_one, Matrix.of_apply,
             lobIIIAStabilityFn, lobIIIANum, lobIIIADenom]
  push_cast
  field_simp [hne1, hD]
  ring

/-- Lobatto IIIB 2-stage is A-stable after the §502 embedding into GLMs. -/
theorem rkLobattoIIIB2_toGLM_isAStable :
    (rkLobattoIIIB2).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkLobattoIIIB2_stabilityFunction_eq z hz]
  exact lobIIIB_aStable z hz

/-- Bridge from the canonical GLM-side `stabilityFunction` to the
classical scalar `gl2StabilityFn` on the Lobatto IIIA 3-stage tableau. -/
theorem rkLobattoIIIA3_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkLobattoIIIA3.stabilityFunction z = gl2StabilityFn z := by
  have hD : gl2Denom z ≠ 0 := gl2_denom_ne_zero z hz
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
      !![1, 0, 0;
         -(z * (5/24)), 1 - z * (1/3), -(z * (-1/24));
         -(z * (1/6)), -(z * (2/3)), 1 - z * (1/6)]
  rw [ButcherTableau.stabilityFunction]
  have hM :
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) - z •
          (Matrix.of (fun i j => ((rkLobattoIIIA3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ)) = M := by
    subst M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rkLobattoIIIA3, Matrix.cons_val_zero, Matrix.cons_val_one]
  change 1 + z * ∑ i, ∑ j,
      (rkLobattoIIIA3.b i : ℂ) *
        ((1 - z • (Matrix.of (fun i j => ((rkLobattoIIIA3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ))⁻¹) i j = gl2StabilityFn z
  rw [hM]
  have hdet : M.det = gl2Denom z := by
    subst M
    rw [Matrix.det_fin_three]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, gl2Denom]
    ring
  have hsum :
      ∑ i, ∑ j, (rkLobattoIIIA3.b i : ℂ) * M.adjugate i j = 1 := by
    subst M
    simp [Fin.sum_univ_three, rkLobattoIIIA3, Matrix.adjugate_fin_three_of,
          Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hsumInv :
      ∑ i, ∑ j, (rkLobattoIIIA3.b i : ℂ) *
          ((gl2Denom z)⁻¹ * M.adjugate i j) =
        (gl2Denom z)⁻¹ := by
    calc
      ∑ i, ∑ j, (rkLobattoIIIA3.b i : ℂ) *
          ((gl2Denom z)⁻¹ * M.adjugate i j) =
        (gl2Denom z)⁻¹ *
          (∑ i, ∑ j, (rkLobattoIIIA3.b i : ℂ) * M.adjugate i j) := by
        simp only [Fin.sum_univ_three]
        ring
      _ = (gl2Denom z)⁻¹ := by rw [hsum]; ring
  rw [Matrix.inv_def]
  simp only [hdet, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hsumInv]
  have hnum : gl2Denom z + z = gl2Num z := by
    unfold gl2Denom gl2Num
    ring
  calc
    1 + z * (gl2Denom z)⁻¹ =
        (gl2Denom z)⁻¹ * (gl2Denom z + z) := by
      rw [mul_add, inv_mul_cancel₀ hD]
      ring
    _ = (gl2Denom z)⁻¹ * gl2Num z := by rw [hnum]
    _ = gl2StabilityFn z := by
      unfold gl2StabilityFn
      rw [div_eq_mul_inv]
      ring

/-- Lobatto IIIA 3-stage is A-stable after the §502 embedding into GLMs. -/
theorem rkLobattoIIIA3_toGLM_isAStable :
    (rkLobattoIIIA3).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkLobattoIIIA3_stabilityFunction_eq z hz]
  exact lobIIIA3_aStable z hz

/-- Bridge from the canonical GLM-side `stabilityFunction` to the
classical scalar `lobIIIC3StabilityFn` on the Lobatto IIIC 3-stage tableau. -/
theorem rkLobattoIIIC3_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkLobattoIIIC3.stabilityFunction z = lobIIIC3StabilityFn z := by
  have hD : lobIIIC3Denom z ≠ 0 := lobIIIC3_denom_ne_zero z hz
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
      !![1 - z * (1/6), -(z * (-1/3)), -(z * (1/6));
         -(z * (1/6)), 1 - z * (5/12), -(z * (-1/12));
         -(z * (1/6)), -(z * (2/3)), 1 - z * (1/6)]
  rw [ButcherTableau.stabilityFunction]
  have hM :
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) - z •
          (Matrix.of (fun i j => ((rkLobattoIIIC3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ)) = M := by
    subst M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rkLobattoIIIC3, Matrix.cons_val_zero, Matrix.cons_val_one]
  change 1 + z * ∑ i, ∑ j,
      (rkLobattoIIIC3.b i : ℂ) *
        ((1 - z • (Matrix.of (fun i j => ((rkLobattoIIIC3.A i j : ℝ) : ℂ)) :
            Matrix (Fin 3) (Fin 3) ℂ))⁻¹) i j = lobIIIC3StabilityFn z
  rw [hM]
  have hdet : M.det = lobIIIC3Denom z / 24 := by
    subst M
    rw [Matrix.det_fin_three]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, lobIIIC3Denom]
    ring
  have hsum :
      ∑ i, ∑ j, (rkLobattoIIIC3.b i : ℂ) * M.adjugate i j =
        (z ^ 2 - 6 * z + 24) / 24 := by
    subst M
    simp [Fin.sum_univ_three, rkLobattoIIIC3, Matrix.adjugate_fin_three_of,
          Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hsumInv :
      ∑ i, ∑ j, (rkLobattoIIIC3.b i : ℂ) *
          ((lobIIIC3Denom z / 24)⁻¹ * M.adjugate i j) =
        (lobIIIC3Denom z / 24)⁻¹ * ((z ^ 2 - 6 * z + 24) / 24) := by
    rw [← hsum]
    simp only [Fin.sum_univ_three]
    ring
  rw [Matrix.inv_def]
  simp only [hdet, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hsumInv]
  have hnum : lobIIIC3Denom z + z * (z ^ 2 - 6 * z + 24) = lobIIIC3Num z := by
    unfold lobIIIC3Denom lobIIIC3Num
    ring
  have h_inv_div : ((lobIIIC3Denom z) / 24)⁻¹ = 24 * (lobIIIC3Denom z)⁻¹ := by
    rw [inv_div]
    ring
  calc
    1 + z * ((lobIIIC3Denom z / 24)⁻¹ * ((z ^ 2 - 6 * z + 24) / 24)) =
        (lobIIIC3Denom z)⁻¹ *
          (lobIIIC3Denom z + z * (z ^ 2 - 6 * z + 24)) := by
      rw [h_inv_div, mul_add, inv_mul_cancel₀ hD]
      ring
    _ = (lobIIIC3Denom z)⁻¹ * lobIIIC3Num z := by rw [hnum]
    _ = lobIIIC3StabilityFn z := by
      unfold lobIIIC3StabilityFn
      rw [div_eq_mul_inv]
      ring

/-- Lobatto IIIC 3-stage is A-stable after the §502 embedding into GLMs. -/
theorem rkLobattoIIIC3_toGLM_isAStable :
    (rkLobattoIIIC3).toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkLobattoIIIC3_stabilityFunction_eq z hz]
  exact lobIIIC3_aStable z hz

/-- §530 sanity — Gauss–Legendre 3-stage has order 6 (≥ 5) and so
embeds as a GLM of order ≥ 5. -/
theorem rkGaussLegendre3_toGLM_hasOrderGe5 :
    rkGaussLegendre3.toGLM.HasOrderGe5 :=
  rkGaussLegendre3.toGLM_hasOrderGe5
    rkGaussLegendre3_order5 rkGaussLegendre3_consistent

/-- §530 sanity — Radau IIA 3-stage has order 5 and so embeds as a
GLM of order ≥ 5. -/
theorem rkRadauIIA3_toGLM_hasOrderGe5 :
    rkRadauIIA3.toGLM.HasOrderGe5 :=
  rkRadauIIA3.toGLM_hasOrderGe5
    rkRadauIIA3_order5 rkRadauIIA3_consistent

/-- §530 sanity — Radau IA 3-stage has order 5 and so embeds as a
GLM of order ≥ 5. -/
theorem rkRadauIA3_toGLM_hasOrderGe5 :
    rkRadauIA3.toGLM.HasOrderGe5 :=
  rkRadauIA3.toGLM_hasOrderGe5
    rkRadauIA3_order5 rkRadauIA3_consistent

/-- §530 sanity — Gauss–Legendre 3-stage has order 6 (= 2s for s = 3,
the maximum possible for any s-stage RK method) and so embeds as a
GLM of order ≥ 6. This is the unique RK witness in the codebase for
order 6. -/
theorem rkGaussLegendre3_toGLM_hasOrderGe6 :
    rkGaussLegendre3.toGLM.HasOrderGe6 :=
  rkGaussLegendre3.toGLM_hasOrderGe6
    rkGaussLegendre3_order6 rkGaussLegendre3_consistent
