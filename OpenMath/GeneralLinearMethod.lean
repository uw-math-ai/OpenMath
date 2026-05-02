import Mathlib

/-!
# General Linear Methods

Butcher §500 introduces general linear methods as multivalue,
multistage methods determined by four coefficient blocks `(A, U, B, V)`.
This file records the scalar autonomous step equations and the basic
contraction criterion for solving the stage equations.

Reference: J. C. Butcher, *Numerical Methods for Ordinary Differential
Equations*, 2nd ed., §500.
-/

open Finset Real
open scoped NNReal

/-- A **general linear method** with `s` stages and `r` input/output
quantities carried between steps.

The four coefficient blocks are those of Butcher §500:
`A` couples stages to stages, `U` couples input quantities to stages,
`B` couples stages to output quantities, and `V` propagates input
quantities to output quantities. -/
structure GeneralLinearMethod (s r : ℕ) where
  /-- The `s × s` stage-to-stage block. Here `s` is the number of stages. -/
  A : Matrix (Fin s) (Fin s) ℝ
  /-- The `s × r` input-to-stage block. Here `r` is the number of input
  quantities carried between steps. -/
  U : Matrix (Fin s) (Fin r) ℝ
  /-- The `r × s` stage-to-output block. Here `s` is the number of stages. -/
  B : Matrix (Fin r) (Fin s) ℝ
  /-- The `r × r` input-to-output block. Here `r` is the number of input
  quantities carried between steps. -/
  V : Matrix (Fin r) (Fin r) ℝ

namespace GeneralLinearMethod

variable {s r : ℕ}

/-! ## §500 — Scalar Stage and Step Equations -/

/-- One-step output for a scalar autonomous ODE `y' = f y`, using a given
stage vector `Y`. Stage existence is handled separately by the fixed-point
criterion below. -/
def step (m : GeneralLinearMethod s r)
    (f : ℝ → ℝ) (h : ℝ) (yIn : Fin r → ℝ) (Y : Fin s → ℝ) :
    Fin r → ℝ :=
  fun k => h * ∑ j, m.B k j * f (Y j) + ∑ l, m.V k l * yIn l

@[simp] theorem step_apply (m : GeneralLinearMethod s r)
    (f : ℝ → ℝ) (h : ℝ) (yIn : Fin r → ℝ) (Y : Fin s → ℝ) (k : Fin r) :
    m.step f h yIn Y k =
      h * ∑ j, m.B k j * f (Y j) + ∑ l, m.V k l * yIn l := rfl

/-- Stage residual for the scalar autonomous GLM stage equations. Zeros of
this residual are exactly solutions of
`Y_i = h * ∑_j A_ij * f (Y_j) + ∑_k U_ik * yIn_k`. -/
def stageResidual (m : GeneralLinearMethod s r)
    (f : ℝ → ℝ) (h : ℝ) (yIn : Fin r → ℝ) (Y : Fin s → ℝ) :
    Fin s → ℝ :=
  fun i => Y i - h * ∑ j, m.A i j * f (Y j) - ∑ k, m.U i k * yIn k

@[simp] theorem stageResidual_apply (m : GeneralLinearMethod s r)
    (f : ℝ → ℝ) (h : ℝ) (yIn : Fin r → ℝ) (Y : Fin s → ℝ) (i : Fin s) :
    m.stageResidual f h yIn Y i =
      Y i - h * ∑ j, m.A i j * f (Y j) - ∑ k, m.U i k * yIn k := rfl

/-! ## Explicit Methods -/

/-- A GLM is explicit when the stage matrix `A` is strictly lower
triangular: `A i j = 0` for `j ≥ i`. -/
def IsExplicit (m : GeneralLinearMethod s r) : Prop :=
  ∀ i j : Fin s, j.val ≥ i.val → m.A i j = 0

theorem IsExplicit.A_diag_zero (m : GeneralLinearMethod s r)
    (hm : m.IsExplicit) : ∀ i : Fin s, m.A i i = 0 := by
  intro i
  exact hm i i le_rfl

/-! ## §510 — Preconsistency, Consistency, and Stability -/

/-- Butcher §510 — consistency. A general linear method is **consistent**
if there exist input vectors `q, q' : Fin r → ℝ` with
* `q` a preconsistency witness (`V q = q`, `U q = 𝟙`), and
* `q'` satisfying the first-derivative compatibility
  `(B 𝟙_s) + V q' = q + q'`,
where `(B 𝟙_s) k := ∑ j, m.B k j` is the input action of the `B` block
on the all-ones stage vector. The interpretation is that `q` carries
the `y_n` content of each input quantity and `q'` carries the
`h · y'_n` content; the third clause is exactly Butcher's §510
condition for the GLM applied to a linear test trajectory.

For the §502 RK embedding (`r = 1`, `U = 𝟙`, `V = 1`, `B = b row`),
this collapses to the standard RK consistency condition `∑ j, b j = 1`
(witnesses `q ≡ 1`, `q' ≡ 0`). -/
def IsConsistent (m : GeneralLinearMethod s r) : Prop :=
  ∃ q q' : Fin r → ℝ,
    (∀ k : Fin r, ∑ l, m.V k l * q l = q k) ∧
    (∀ i : Fin s, ∑ k, m.U i k * q k = 1) ∧
    (∀ k : Fin r, (∑ j, m.B k j) + ∑ l, m.V k l * q' l = q k + q' k)

/-- Butcher §510 — preconsistency. A general linear method is
preconsistent if there is an input-vector decomposition `q : Fin r → ℝ`
that is a fixed point of `V` and is sent by `U` to the all-ones stage
vector. The vector `q` interprets each input quantity as carrying a
copy of `y(x_n)`. -/
def IsPreconsistent (m : GeneralLinearMethod s r) : Prop :=
  ∃ q : Fin r → ℝ,
    (∀ k : Fin r, ∑ l, m.V k l * q l = q k) ∧
    (∀ i : Fin s, ∑ k, m.U i k * q k = 1)

/-- Butcher §510 — stability. The iterated propagation of any bounded
input by `V` stays uniformly bounded. We phrase this in elementary
terms (no `Matrix.pow` unfolding) by iterating the explicit-sum
`mulVec`. -/
def IsStable (m : GeneralLinearMethod s r) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (q : Fin r → ℝ),
    (∀ k, |q k| ≤ 1) →
    ∀ k, |((fun v => fun k' => ∑ l, m.V k' l * v l)^[n] q) k| ≤ M

/-! ## §520 — Stability Matrix -/

/-- Complex lift of the `A` block. -/
def Aℂ (m : GeneralLinearMethod s r) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => (m.A i j : ℂ)

/-- Complex lift of the `U` block. -/
def Uℂ (m : GeneralLinearMethod s r) : Matrix (Fin s) (Fin r) ℂ :=
  fun i k => (m.U i k : ℂ)

/-- Complex lift of the `B` block. -/
def Bℂ (m : GeneralLinearMethod s r) : Matrix (Fin r) (Fin s) ℂ :=
  fun k j => (m.B k j : ℂ)

/-- Complex lift of the `V` block. -/
def Vℂ (m : GeneralLinearMethod s r) : Matrix (Fin r) (Fin r) ℂ :=
  fun k l => (m.V k l : ℂ)

/-- Butcher §520 — stability matrix `M(z) = V + z B (I - z A)⁻¹ U`.
Uses the total `Matrix.inv`, so the function is defined for every `z`.
Invertibility hypotheses belong on downstream theorems, not this
definition. -/
noncomputable def stabilityMatrix
    (m : GeneralLinearMethod s r) (z : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  m.Vℂ + z • (m.Bℂ * ((1 : Matrix (Fin s) (Fin s) ℂ) - z • m.Aℂ)⁻¹ * m.Uℂ)

@[simp] theorem stabilityMatrix_apply (m : GeneralLinearMethod s r)
    (z : ℂ) (k l : Fin r) :
    m.stabilityMatrix z k l =
      m.Vℂ k l +
        z * ∑ i, ∑ j,
          m.Bℂ k i *
            ((1 : Matrix (Fin s) (Fin s) ℂ) - z • m.Aℂ)⁻¹ i j *
            m.Uℂ j l := by
  simp [stabilityMatrix, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem stabilityMatrix_zero (m : GeneralLinearMethod s r) :
    m.stabilityMatrix 0 = m.Vℂ := by
  simp [stabilityMatrix]

/-! ## §521 — Stability Order

A method has stability order `p` if `M(z)` agrees with `exp(z) • V` to
order `p + 1` near `z = 0`: there exist `C ≥ 0` and `δ > 0` such that
`‖M(z) - Complex.exp z • V‖ ≤ C * ‖z‖ ^ (p + 1)` for all `‖z‖ < δ`.

For RK methods (where `V = 1`) this collapses to the standard scalar
stability-order condition `R(z) - exp z = O(z^{p+1})`. -/

attribute [local instance] Matrix.normedAddCommGroup

/-- Butcher §521 — matrix-level stability order. -/
def IsStabilityOrder (m : GeneralLinearMethod s r) (p : ℕ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ 0 ≤ C ∧
    ∀ z : ℂ, ‖z‖ < δ →
      ‖m.stabilityMatrix z - Complex.exp z • m.Vℂ‖ ≤ C * ‖z‖ ^ (p + 1)

/-- Stability order is monotone in `p`: a higher-order method
satisfies every weaker order condition. The proof shrinks `δ` to
`min δ 1` so `‖z‖ ^ (p+1) ≤ ‖z‖ ^ (q+1)` for `q ≤ p`. -/
theorem IsStabilityOrder.mono (m : GeneralLinearMethod s r)
    {p q : ℕ} (hpq : q ≤ p) (hp : m.IsStabilityOrder p) :
    m.IsStabilityOrder q := by
  obtain ⟨C, δ, hδ, hC, hbound⟩ := hp
  refine ⟨C, min δ 1, lt_min hδ one_pos, hC, ?_⟩
  intro z hz
  have hz_lt_δ : ‖z‖ < δ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz_le_one : ‖z‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hz (min_le_right _ _))
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg _
  have hpow : ‖z‖ ^ (p + 1) ≤ ‖z‖ ^ (q + 1) :=
    pow_le_pow_of_le_one hz_nn hz_le_one (Nat.add_le_add_right hpq 1)
  exact (hbound z hz_lt_δ).trans
    (mul_le_mul_of_nonneg_left hpow hC)

/-- Sanity: every GLM has stability order `0`. The matrix
`g z := m.stabilityMatrix z - exp z • m.Vℂ` is complex-analytic in
`z` near `0` and vanishes at `z = 0`, hence is `O(z)`. -/
theorem isStabilityOrder_zero (m : GeneralLinearMethod s r) :
    m.IsStabilityOrder 0 := by
  sorry

/-! ## Stage Solvability by Contraction -/

/-- The scalar GLM stage self-map. Fixed points are stage vectors satisfying
Butcher's §500 stage equations. -/
def stageMap (m : GeneralLinearMethod s r)
    (f : ℝ → ℝ) (h : ℝ) (yIn : Fin r → ℝ) (Y : Fin s → ℝ) :
    Fin s → ℝ :=
  fun i => h * ∑ j, m.A i j * f (Y j) + ∑ k, m.U i k * yIn k

@[simp] theorem stageMap_apply (m : GeneralLinearMethod s r)
    (f : ℝ → ℝ) (h : ℝ) (yIn : Fin r → ℝ) (Y : Fin s → ℝ) (i : Fin s) :
    m.stageMap f h yIn Y i =
      h * ∑ j, m.A i j * f (Y j) + ∑ k, m.U i k * yIn k := rfl

/-- The maximum row-`ℓ¹` norm of `A`, `max_i ∑_j |A i j|`. Equals `0` in
the vacuous case `s = 0`. -/
noncomputable def rowAbsSumMax (m : GeneralLinearMethod s r) : ℝ :=
  if h : 0 < s then
    Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
      (fun i : Fin s => ∑ j, |m.A i j|)
  else 0

theorem rowAbsSumMax_nonneg (m : GeneralLinearMethod s r) :
    0 ≤ m.rowAbsSumMax := by
  unfold rowAbsSumMax
  split_ifs with hs
  · refine Finset.le_sup'_of_le _ (Finset.mem_univ (⟨0, hs⟩ : Fin s)) ?_
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · rfl

/-- Each row sum `∑_j |A i j|` is bounded by `rowAbsSumMax`. -/
theorem row_absSum_le_rowAbsSumMax (m : GeneralLinearMethod s r) (i : Fin s) :
    (∑ j, |m.A i j|) ≤ m.rowAbsSumMax := by
  have hpos : 0 < s := lt_of_le_of_lt (Nat.zero_le _) i.is_lt
  unfold rowAbsSumMax
  rw [dif_pos hpos]
  exact Finset.le_sup' (fun i : Fin s => ∑ j, |m.A i j|) (Finset.mem_univ i)

/-- Pointwise distance bound for the GLM stage self-map. -/
theorem stageMap_dist_le (m : GeneralLinearMethod s r) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {h : ℝ} (hh : 0 ≤ h) (yIn : Fin r → ℝ)
    (Y Y' : Fin s → ℝ) :
    dist (m.stageMap f h yIn Y) (m.stageMap f h yIn Y') ≤
      (h * L * m.rowAbsSumMax) * dist Y Y' := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hRow : 0 ≤ m.rowAbsSumMax := m.rowAbsSumMax_nonneg
  have hdY : 0 ≤ dist Y Y' := dist_nonneg
  have hRHS : 0 ≤ (h * L * m.rowAbsSumMax) * dist Y Y' := by positivity
  refine (dist_pi_le_iff hRHS).mpr ?_
  intro i
  have hdist_inner :
      dist (m.stageMap f h yIn Y i) (m.stageMap f h yIn Y' i)
        = h * |∑ j, m.A i j * (f (Y j) - f (Y' j))| := by
    simp only [stageMap_apply]
    have hsum :
        (∑ j, m.A i j * f (Y j)) - (∑ j, m.A i j * f (Y' j))
          = ∑ j, m.A i j * (f (Y j) - f (Y' j)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have heq :
        (h * ∑ j, m.A i j * f (Y j) + ∑ k, m.U i k * yIn k) -
            (h * ∑ j, m.A i j * f (Y' j) + ∑ k, m.U i k * yIn k)
          = h * ∑ j, m.A i j * (f (Y j) - f (Y' j)) := by
      linear_combination h * hsum
    rw [Real.dist_eq, heq, abs_mul, abs_of_nonneg hh]
  have habs_le :
      |∑ j, m.A i j * (f (Y j) - f (Y' j))|
        ≤ (∑ j, |m.A i j|) * ((L : ℝ) * dist Y Y') := by
    have h1 :
        |∑ j, m.A i j * (f (Y j) - f (Y' j))|
          ≤ ∑ j, |m.A i j * (f (Y j) - f (Y' j))| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 :
        ∑ j, |m.A i j * (f (Y j) - f (Y' j))|
          ≤ ∑ j, |m.A i j| * ((L : ℝ) * dist Y Y') := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hcoord : |f (Y j) - f (Y' j)| ≤ (L : ℝ) * dist Y Y' := by
        calc |f (Y j) - f (Y' j)|
            = dist (f (Y j)) (f (Y' j)) := by rw [Real.dist_eq]
          _ ≤ (L : ℝ) * dist (Y j) (Y' j) := hf.dist_le_mul _ _
          _ ≤ (L : ℝ) * dist Y Y' :=
            mul_le_mul_of_nonneg_left (dist_le_pi_dist Y Y' j) hL
      exact mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)
    have h3 :
        (∑ j, |m.A i j| * ((L : ℝ) * dist Y Y'))
          = (∑ j, |m.A i j|) * ((L : ℝ) * dist Y Y') := by
      rw [← Finset.sum_mul]
    linarith
  have hrow := m.row_absSum_le_rowAbsSumMax i
  have hLDist : 0 ≤ (L : ℝ) * dist Y Y' := mul_nonneg hL hdY
  have hbnd :
      (∑ j, |m.A i j|) * ((L : ℝ) * dist Y Y') ≤
        m.rowAbsSumMax * ((L : ℝ) * dist Y Y') :=
    mul_le_mul_of_nonneg_right hrow hLDist
  have hstep_a :
      h * |∑ j, m.A i j * (f (Y j) - f (Y' j))|
        ≤ h * ((∑ j, |m.A i j|) * ((L : ℝ) * dist Y Y')) :=
    mul_le_mul_of_nonneg_left habs_le hh
  have hstep_b :
      h * ((∑ j, |m.A i j|) * ((L : ℝ) * dist Y Y'))
        ≤ h * (m.rowAbsSumMax * ((L : ℝ) * dist Y Y')) :=
    mul_le_mul_of_nonneg_left hbnd hh
  have hfinal :
      dist (m.stageMap f h yIn Y i) (m.stageMap f h yIn Y' i)
        ≤ h * (m.rowAbsSumMax * ((L : ℝ) * dist Y Y')) := by
    calc dist (m.stageMap f h yIn Y i) (m.stageMap f h yIn Y' i)
        = h * |∑ j, m.A i j * (f (Y j) - f (Y' j))| := hdist_inner
      _ ≤ h * (m.rowAbsSumMax * ((L : ℝ) * dist Y Y')) :=
        le_trans hstep_a hstep_b
  have hreorg :
      h * (m.rowAbsSumMax * ((L : ℝ) * dist Y Y'))
        = h * (L : ℝ) * m.rowAbsSumMax * dist Y Y' := by ring
  rw [hreorg] at hfinal
  exact hfinal

/-- The GLM stage self-map is `(h · L · rowAbsSumMax)`-Lipschitz in the
supremum metric on `Fin s → ℝ`, given `h ≥ 0` and `f` `L`-Lipschitz. -/
theorem stageMap_lipschitzWith
    (m : GeneralLinearMethod s r) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {h : ℝ} (hh : 0 ≤ h) (yIn : Fin r → ℝ) :
    LipschitzWith
      (Real.toNNReal h * L * Real.toNNReal m.rowAbsSumMax)
      (m.stageMap f h yIn) := by
  apply LipschitzWith.of_dist_le_mul
  intro Y Y'
  have hbound := stageMap_dist_le m hf hh yIn Y Y'
  have hcoe :
      ((Real.toNNReal h * L * Real.toNNReal m.rowAbsSumMax : ℝ≥0) : ℝ)
        = h * (L : ℝ) * m.rowAbsSumMax := by
    rw [NNReal.coe_mul, NNReal.coe_mul,
        Real.coe_toNNReal h hh,
        Real.coe_toNNReal _ m.rowAbsSumMax_nonneg]
  rw [hcoe]
  exact hbound

/-- **Butcher §500 / §341 template.** If `f` is `L`-Lipschitz and the
step size is small enough that `h · L · rowAbsSumMax < 1`, the scalar
GLM stage equations have a unique solution. -/
theorem stageEquations_unique_solution
    (m : GeneralLinearMethod s r) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {h : ℝ} (hh : 0 ≤ h) (yIn : Fin r → ℝ)
    (hsmall : h * (L : ℝ) * m.rowAbsSumMax < 1) :
    ∃! Y : Fin s → ℝ, Y = m.stageMap f h yIn Y := by
  set Ylip : ℝ≥0 :=
    Real.toNNReal h * L * Real.toNNReal m.rowAbsSumMax with hYlip
  have hlip : LipschitzWith Ylip (m.stageMap f h yIn) :=
    m.stageMap_lipschitzWith hf hh yIn
  have hYlt : Ylip < 1 := by
    have hcoe : (Ylip : ℝ) = h * (L : ℝ) * m.rowAbsSumMax := by
      simp [hYlip, NNReal.coe_mul, Real.coe_toNNReal _ hh,
            Real.coe_toNNReal _ m.rowAbsSumMax_nonneg]
    have h_lt : (Ylip : ℝ) < 1 := by rw [hcoe]; exact_mod_cast hsmall
    exact_mod_cast h_lt
  have hcontr : ContractingWith Ylip (m.stageMap f h yIn) := ⟨hYlt, hlip⟩
  haveI : Nonempty (Fin s → ℝ) := ⟨fun _ => 0⟩
  obtain ⟨Y, hY_fix, _⟩ :=
    hcontr.exists_fixedPoint (0 : Fin s → ℝ) (edist_ne_top _ _)
  refine ⟨Y, hY_fix.symm, ?_⟩
  intro Y' hY'_fix
  have h1 : Y' = ContractingWith.fixedPoint (m.stageMap f h yIn) hcontr :=
    hcontr.fixedPoint_unique hY'_fix.symm
  have h2 : Y = ContractingWith.fixedPoint (m.stageMap f h yIn) hcontr :=
    hcontr.fixedPoint_unique hY_fix
  rw [h1, ← h2]

end GeneralLinearMethod
