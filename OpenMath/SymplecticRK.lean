import OpenMath.RungeKutta
import OpenMath.GaussLegendre3
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Symplectic Runge–Kutta Methods (Butcher §37)

A Runge–Kutta method is **symplectic** when the Cooper matrix
`M_{ij} := b_i a_{ij} + b_j a_{ji} - b_i b_j` vanishes identically.
Symplectic methods preserve all quadratic invariants of the ODE, in particular
the symplectic 2-form for Hamiltonian systems.

Reference: Butcher, *Numerical Methods for Ordinary Differential Equations*
(2nd ed.), §370–§371.
-/

open Finset Real Matrix

namespace ButcherTableau

variable {s : ℕ}

/-- The **symplecticity defect** at indices `(i, j)`:
`M_{ij} = b_i · a_{ij} + b_j · a_{ji} − b_i · b_j` (Cooper, 1987). -/
def symplecticDefect (t : ButcherTableau s) (i j : Fin s) : ℝ :=
  t.b i * t.A i j + t.b j * t.A j i - t.b i * t.b j

/-- A Butcher tableau is **symplectic** when the defect `M` vanishes identically. -/
def IsSymplectic (t : ButcherTableau s) : Prop :=
  ∀ i j : Fin s, t.symplecticDefect i j = 0

/-! ## §370A — Symplectic methods preserve quadratic invariants -/

/-- For a symmetric matrix `S`, the bilinear form `(v, w) ↦ vᵀ S w` is symmetric. -/
theorem dotProduct_mulVec_symm {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.IsSymm) (v w : Fin n → ℝ) :
    v ⬝ᵥ S *ᵥ w = w ⬝ᵥ S *ᵥ v := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hS.apply]; ring

/-- **§370A — Cooper's theorem**. A symplectic Runge–Kutta method preserves every
quadratic invariant of the underlying ODE. Concretely, if `S` is a symmetric matrix
and `f : ℝⁿ → ℝⁿ` satisfies `f(y)ᵀ S y + yᵀ S f(y) = 0` (so that `yᵀ S y` is conserved
along solutions of `y' = f(y)`), then for any stage solution `Y` and one-step update
`y₁ = y₀ + h ∑ᵢ bᵢ • f(Yᵢ)` of a symplectic RK method, `y₁ᵀ S y₁ = y₀ᵀ S y₀`. -/
theorem IsSymplectic.preserves_quadInv {s n : ℕ} {t : ButcherTableau s}
    (hSymp : t.IsSymplectic)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.IsSymm)
    {f : (Fin n → ℝ) → (Fin n → ℝ)}
    (hf : ∀ y, f y ⬝ᵥ S *ᵥ y + y ⬝ᵥ S *ᵥ (f y) = 0)
    (y0 : Fin n → ℝ) (h : ℝ)
    (Y : Fin s → (Fin n → ℝ))
    (hY : ∀ i, Y i = y0 + h • ∑ j, t.A i j • f (Y j)) :
    (y0 + h • ∑ i, t.b i • f (Y i)) ⬝ᵥ S *ᵥ (y0 + h • ∑ i, t.b i • f (Y i))
      = y0 ⬝ᵥ S *ᵥ y0 := by
  -- Local abbreviation for the bilinear form B(u,v) = uᵀ S v
  set B : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun u v => u ⬝ᵥ S *ᵥ v with hB_def
  -- Symmetry of B
  have hB_symm : ∀ u v, B u v = B v u :=
    fun u v => dotProduct_mulVec_symm hS u v
  -- Bilinear properties
  have hB_add_left : ∀ u₁ u₂ v, B (u₁ + u₂) v = B u₁ v + B u₂ v := by
    intro u₁ u₂ v; simp [hB_def, add_dotProduct]
  have hB_add_right : ∀ u v₁ v₂, B u (v₁ + v₂) = B u v₁ + B u v₂ := by
    intro u v₁ v₂; simp [hB_def, Matrix.mulVec_add, dotProduct_add]
  have hB_smul_left : ∀ (c : ℝ) u v, B (c • u) v = c * B u v := by
    intro c u v
    simp [hB_def, smul_dotProduct]
  have hB_smul_right : ∀ (c : ℝ) u v, B u (c • v) = c * B u v := by
    intro c u v
    simp [hB_def, Matrix.mulVec_smul, dotProduct_smul]
  have hB_sum_left : ∀ {ι : Type} (T : Finset ι) (u : ι → (Fin n → ℝ)) (v : Fin n → ℝ),
      B (∑ i ∈ T, u i) v = ∑ i ∈ T, B (u i) v := by
    intro ι T u v
    simp only [hB_def]
    exact sum_dotProduct T u (S *ᵥ v)
  have hB_sum_right : ∀ {ι : Type} (T : Finset ι) (u : Fin n → ℝ) (w : ι → (Fin n → ℝ)),
      B u (∑ j ∈ T, w j) = ∑ j ∈ T, B u (w j) := by
    intro ι T u w
    simp only [hB_def]
    rw [Matrix.mulVec_sum]
    exact dotProduct_sum u T (fun j => S *ᵥ w j)
  -- Per-stage: B(f(Yᵢ), Yᵢ) = 0
  have hF_diag : ∀ i, B (f (Y i)) (Y i) = 0 := by
    intro i
    have hkey : B (f (Y i)) (Y i) + B (Y i) (f (Y i)) = 0 := hf (Y i)
    have hsymm := hB_symm (Y i) (f (Y i))
    -- B is symmetric so B(Yᵢ, fᵢ) = B(fᵢ, Yᵢ); thus 2 B(fᵢ, Yᵢ) = 0
    rw [hsymm] at hkey
    linarith
  -- y0 = Yᵢ - h • ∑ⱼ Aᵢⱼ • f(Yⱼ)
  have hY0_eq : ∀ i, y0 = Y i - h • ∑ j, t.A i j • f (Y j) := by
    intro i; rw [hY i]; abel
  -- B(f(Yᵢ), y0) = -h ∑ⱼ Aᵢⱼ B(f(Yᵢ), f(Yⱼ))
  have hB_f_y0 : ∀ i, B (f (Y i)) y0
      = - (h * ∑ j, t.A i j * B (f (Y i)) (f (Y j))) := by
    intro i
    have hrew : y0 = Y i + (-h) • ∑ j, t.A i j • f (Y j) := by
      rw [hY0_eq i]; simp [sub_eq_add_neg, neg_smul]
    rw [hrew]
    rw [hB_add_right, hB_smul_right, hB_sum_right Finset.univ]
    rw [hF_diag i]
    have step : ∀ j : Fin s,
        B (f (Y i)) (t.A i j • f (Y j)) = t.A i j * B (f (Y i)) (f (Y j)) :=
      fun j => hB_smul_right (t.A i j) (f (Y i)) (f (Y j))
    rw [Finset.sum_congr rfl (fun j _ => step j)]
    ring
  -- Set Δ = h • ∑ᵢ bᵢ • f(Yᵢ)
  set Δ : Fin n → ℝ := h • ∑ i, t.b i • f (Y i) with hΔ_def
  -- B(y0+Δ, y0+Δ) = B(y0,y0) + 2 B(Δ, y0) + B(Δ, Δ)  (using B symmetric)
  have hExpand : B (y0 + Δ) (y0 + Δ) = B y0 y0 + 2 * B Δ y0 + B Δ Δ := by
    rw [hB_add_left, hB_add_right, hB_add_right]
    rw [hB_symm y0 Δ]; ring
  -- Compute B(Δ, y0)
  have hΔ_y0 : B Δ y0 = h * ∑ i, t.b i * B (f (Y i)) y0 := by
    rw [hΔ_def]
    rw [hB_smul_left, hB_sum_left]
    have : ∀ i : Fin s, B (t.b i • f (Y i)) y0 = t.b i * B (f (Y i)) y0 :=
      fun i => hB_smul_left (t.b i) (f (Y i)) y0
    rw [Finset.sum_congr rfl (fun i _ => this i)]
  -- Compute B(Δ, Δ)
  have hΔ_Δ : B Δ Δ
      = h * h * ∑ i, ∑ j, t.b i * t.b j * B (f (Y i)) (f (Y j)) := by
    rw [hΔ_def]
    rw [hB_smul_left, hB_smul_right, hB_sum_left]
    have inner : ∀ i : Fin s,
        B (t.b i • f (Y i)) (∑ j, t.b j • f (Y j))
          = ∑ j, t.b i * t.b j * B (f (Y i)) (f (Y j)) := by
      intro i
      rw [hB_smul_left, hB_sum_right]
      have step : ∀ j : Fin s,
          B (f (Y i)) (t.b j • f (Y j)) = t.b j * B (f (Y i)) (f (Y j)) :=
        fun j => hB_smul_right (t.b j) (f (Y i)) (f (Y j))
      rw [Finset.sum_congr rfl (fun j _ => step j), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
    rw [Finset.sum_congr rfl (fun i _ => inner i)]
    rw [show (h * (h * ∑ i, ∑ j, t.b i * t.b j * B (f (Y i)) (f (Y j))))
            = h * h * ∑ i, ∑ j, t.b i * t.b j * B (f (Y i)) (f (Y j)) from by ring]
  -- Substitute hB_f_y0 into hΔ_y0; rearrange to a clean double sum.
  -- Key intermediate: h · ∑ᵢ tᵢ B(fᵢ, y0) = -h² · ∑ᵢⱼ bᵢ Aᵢⱼ B(fᵢ, fⱼ).
  have hΔ_y0' : B Δ y0
      = - (h * h * ∑ i, ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j))) := by
    rw [hΔ_y0]
    -- Rewrite each `t.b i * B (f (Y i)) y0` using hB_f_y0
    have step : (∑ i, t.b i * B (f (Y i)) y0)
        = -(h * ∑ i, ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j))) := by
      have eq1 : (∑ i, t.b i * B (f (Y i)) y0)
          = ∑ i, t.b i * -(h * ∑ j, t.A i j * B (f (Y i)) (f (Y j))) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hB_f_y0 i]
      rw [eq1]
      -- Now distribute and interchange
      have eq2 : (∑ i, t.b i * -(h * ∑ j, t.A i j * B (f (Y i)) (f (Y j))))
          = -(h * ∑ i, ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j))) := by
        rw [Finset.mul_sum (s := Finset.univ)
              (f := fun i => ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j))) (a := h)]
        rw [show (-(∑ i : Fin s, h * ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j))))
              = ∑ i : Fin s, -(h * ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j))) from
            (Finset.sum_neg_distrib (s := Finset.univ)
              (f := fun i => h * ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j)))).symm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum (s := Finset.univ)
              (f := fun j => t.b i * t.A i j * B (f (Y i)) (f (Y j))) (a := h)]
        rw [Finset.mul_sum (s := Finset.univ)
              (f := fun j => t.A i j * B (f (Y i)) (f (Y j))) (a := h)]
        rw [show t.b i * -∑ j, h * (t.A i j * B (f (Y i)) (f (Y j)))
              = -(t.b i * ∑ j, h * (t.A i j * B (f (Y i)) (f (Y j)))) from by ring]
        rw [Finset.mul_sum (s := Finset.univ)
              (f := fun j => h * (t.A i j * B (f (Y i)) (f (Y j)))) (a := t.b i)]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      exact eq2
    rw [step]; ring
  -- Reindexing identity for the cross sum
  have hReindex :
      2 * ∑ i, ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j))
        = ∑ i, ∑ j, (t.b i * t.A i j + t.b j * t.A j i) * B (f (Y i)) (f (Y j)) := by
    have hswap :
        ∑ i, ∑ j, t.b j * t.A j i * B (f (Y i)) (f (Y j))
          = ∑ i, ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hB_symm]
    have hsplit :
        ∑ i, ∑ j, (t.b i * t.A i j + t.b j * t.A j i) * B (f (Y i)) (f (Y j))
          = (∑ i, ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j)))
            + (∑ i, ∑ j, t.b j * t.A j i * B (f (Y i)) (f (Y j))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hsplit, hswap]; ring
  -- Final assembly: defect kills the bilinear remainder
  have hDefectKill :
      ∑ i, ∑ j, (t.b i * t.A i j + t.b j * t.A j i - t.b i * t.b j)
        * B (f (Y i)) (f (Y j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hd := hSymp i j
    simp only [symplecticDefect] at hd
    rw [hd]; ring
  -- Split that double sum into the two pieces
  have hSplit :
      ∑ i, ∑ j, (t.b i * t.A i j + t.b j * t.A j i - t.b i * t.b j)
        * B (f (Y i)) (f (Y j))
        = (∑ i, ∑ j, (t.b i * t.A i j + t.b j * t.A j i)
             * B (f (Y i)) (f (Y j)))
          - (∑ i, ∑ j, t.b i * t.b j * B (f (Y i)) (f (Y j))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- Combine: the expanded difference equals 0
  have hAC :
      ∑ i, ∑ j, (t.b i * t.A i j + t.b j * t.A j i)
        * B (f (Y i)) (f (Y j))
        = ∑ i, ∑ j, t.b i * t.b j * B (f (Y i)) (f (Y j)) := by
    have := hDefectKill
    rw [hSplit] at this
    linarith
  -- Now finish
  have hgoal : B (y0 + Δ) (y0 + Δ) - B y0 y0 = 0 := by
    rw [hExpand]
    rw [hΔ_y0', hΔ_Δ]
    -- Want: 2*(-h²·X) + h²·Y = 0 where X = ∑bᵢAᵢⱼB and Y = ∑bᵢbⱼB
    -- Using hReindex: 2X = ∑(bᵢAᵢⱼ + bⱼAⱼᵢ) B = (by hAC) Y
    -- So 2*(-h²·X) + h²·Y = -h²·(2X) + h²·Y = -h²·Y + h²·Y = 0
    set X : ℝ := ∑ i, ∑ j, t.b i * t.A i j * B (f (Y i)) (f (Y j)) with hX_def
    set Y' : ℝ := ∑ i, ∑ j, (t.b i * t.A i j + t.b j * t.A j i)
                  * B (f (Y i)) (f (Y j)) with hY'_def
    set Z : ℝ := ∑ i, ∑ j, t.b i * t.b j * B (f (Y i)) (f (Y j)) with hZ_def
    -- hReindex: 2 * X = Y'
    -- hAC: Y' = Z
    -- Goal after rewriting: B y0 y0 + 2 * (-(h*h*X)) + h*h*Z - B y0 y0 = 0
    nlinarith [hReindex, hAC]
  linarith [hgoal]

/-! ## §371 — Examples: Gauss–Legendre methods are symplectic -/

/-- The 1-stage Gauss–Legendre method (= implicit midpoint rule). -/
noncomputable def rkGaussLegendre1 : ButcherTableau 1 where
  A := !![1/2]
  b := ![1]
  c := ![1/2]

theorem rkGaussLegendre1_consistent : rkGaussLegendre1.IsConsistent where
  weights_sum := by simp [rkGaussLegendre1]
  row_sum := by intro i; fin_cases i; simp [rkGaussLegendre1]

/-- **§371**: The implicit midpoint (1-stage Gauss–Legendre) method is symplectic. -/
theorem rkGaussLegendre1_isSymplectic : rkGaussLegendre1.IsSymplectic := by
  intro i j
  fin_cases i; fin_cases j
  simp [symplecticDefect, rkGaussLegendre1]; ring

private theorem sqrt3_sq' : Real.sqrt 3 ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)

/-- **§371**: The 2-stage Gauss–Legendre method is symplectic. -/
theorem rkGaussLegendre2_isSymplectic : rkGaussLegendre2.IsSymplectic := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticDefect, rkGaussLegendre2] <;> nlinarith [sqrt3_sq']

private theorem sqrt15_sq' : Real.sqrt 15 ^ 2 = 15 :=
  Real.sq_sqrt (by norm_num : (15 : ℝ) ≥ 0)

/-- **§371**: The 3-stage Gauss–Legendre method is symplectic. -/
theorem rkGaussLegendre3_isSymplectic : rkGaussLegendre3.IsSymplectic := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticDefect, rkGaussLegendre3] <;> nlinarith [sqrt15_sq']

end ButcherTableau
