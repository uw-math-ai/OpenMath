import OpenMath.StiffEquations

/-!
# Theorem 356C: AN-stability necessary conditions

An implicit Runge–Kutta method is AN-stable only if:
1. `bⱼ ≥ 0` for all `j`
2. The matrix `M = diag(b)A + Aᵀdiag(b) − bbᵀ` is positive semidefinite

Equivalently, AN-stability implies algebraic stability.

Reference: Iserles, *A First Course in the Numerical Analysis of Differential
Equations*, Theorem 356C, p. 268.
-/

open Finset

noncomputable section

namespace ButcherTableau

variable {s : ℕ}

/-! ## Definitions -/

/-- The Butcher coefficient matrix `A` cast to `ℂ`. -/
def Aℂ (t : ButcherTableau s) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => (t.A i j : ℂ)

/-- The weight vector `b` cast to `ℂ`. -/
def bℂ (t : ButcherTableau s) (i : Fin s) : ℂ := (t.b i : ℂ)

/-- The matrix stability function `R(z₁,…,zₛ)` for an `s`-stage RK method
with diagonal matrix argument `Z = diag(z)`:
  `R(z) = 1 + bᵀ · diag(z) · (I − A·diag(z))⁻¹ · 𝟙`
This is the amplification factor for the test system `y' = Zy`.
Reference: Iserles, Section 3.5. -/
def stabilityFnDiag (t : ButcherTableau s) (z : Fin s → ℂ) : ℂ :=
  let Z := Matrix.diagonal z
  let W := Z * (1 - t.Aℂ * Z)⁻¹
  1 + ∑ i : Fin s, t.bℂ i * (W.mulVec (fun _ => (1 : ℂ))) i

/-- An `s`-stage RK method is **AN-stable** if `|R(Z)| ≤ 1` for every
diagonal `Z = diag(z₁,…,zₛ)` with `Re(zⱼ) ≤ 0`, whenever `I − AZ`
is invertible.
Reference: Iserles, Definition 356B. -/
def IsANStable (t : ButcherTableau s) : Prop :=
  ∀ z : Fin s → ℂ,
    (∀ i, (z i).re ≤ 0) →
    (1 - t.Aℂ * Matrix.diagonal z).det ≠ 0 →
    ‖t.stabilityFnDiag z‖ ≤ 1

/-! ## Part 1: AN-stable ⟹ bⱼ ≥ 0

Choose `Z = −τ Eⱼⱼ` for small `τ > 0`. The matrix `I − AZ` has a
rank-1 perturbation from the identity, so:
  `det(I − AZ) = 1 + τ Aⱼⱼ`
  `R(Z) = (1 + τ(Aⱼⱼ − bⱼ)) / (1 + τ Aⱼⱼ)`
If `bⱼ < 0`, then `R > 1` for small `τ`, contradicting AN-stability.
-/

/-- Diagonal vector: `−τ` at position `j`, `0` elsewhere. -/
private def negTauBasis (j : Fin s) (τ : ℝ) : Fin s → ℂ :=
  fun i => if i = j then ((-τ : ℝ) : ℂ) else 0

private lemma negTauBasis_re_le {j : Fin s} {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ i, (negTauBasis j τ i).re ≤ 0 := by
  intro i; simp only [negTauBasis]
  split_ifs with h
  · simp only [Complex.ofReal_neg, Complex.neg_re, Complex.ofReal_re]; linarith
  · simp

/-- For `Z = −τ Eⱼⱼ`, `det(I − AZ) = 1 + τ Aⱼⱼ`. -/
lemma det_negTauBasis (t : ButcherTableau s) (j : Fin s) (τ : ℝ) :
    (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)).det =
      1 + (τ : ℂ) * (t.A j j : ℂ) := by
  have heq : 1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ) =
      1 + Matrix.replicateCol (Fin 1) (fun i => (τ : ℂ) * t.Aℂ i j) *
          Matrix.replicateRow (Fin 1) (fun k => if k = j then (1 : ℂ) else 0) := by
    ext i k
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.add_apply,
      Matrix.mul_diagonal, negTauBasis, Aℂ]
    simp only [Matrix.replicateCol, Matrix.replicateRow, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_one]
    split_ifs <;> simp_all <;> ring
  rw [heq, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1; simp only [dotProduct, ite_mul, zero_mul, one_mul]
  rw [Finset.sum_ite_eq']; simp [Finset.mem_univ, Aℂ]

/-- For `Z = −τ Eⱼⱼ` with `1 + τ Aⱼⱼ ≠ 0`, the stability function equals
`(1 + τ(Aⱼⱼ − bⱼ)) / (1 + τ Aⱼⱼ)`. -/
lemma stabilityFn_negTauBasis (t : ButcherTableau s) (j : Fin s) (τ : ℝ)
    (hdet : 1 + (τ : ℂ) * (t.A j j : ℂ) ≠ 0) :
    t.stabilityFnDiag (negTauBasis j τ) =
      (1 + (τ : ℂ) * ((t.A j j : ℂ) - (t.b j : ℂ))) /
      (1 + (τ : ℂ) * (t.A j j : ℂ)) := by
  have hdet' : (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)).det ≠ 0 := by
    rw [det_negTauBasis]; exact hdet
  set M := (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)) with hM_def
  -- x = M⁻¹ · 𝟙
  set x := M⁻¹.mulVec (fun _ => (1 : ℂ)) with hx_def
  -- Step 1: M · x = 𝟙
  have hMx : M.mulVec x = fun _ => 1 := by
    have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet'.isUnit
    rw [hx_def, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  -- Step 2: (1 + τ A_jj) * x_j = 1 from the j-th row of M · x = 𝟙
  have hxj : (1 + (τ : ℂ) * (t.A j j : ℂ)) * x j = 1 := by
    have h := congr_fun hMx j
    simp only [Matrix.mulVec, dotProduct] at h
    rw [Finset.sum_eq_single j] at h
    · -- k = j term: M_jj * x_j = (1 + τ A_jj) * x_j
      simp only [hM_def, Matrix.sub_apply, Matrix.one_apply,
        Matrix.mul_diagonal, negTauBasis, Aℂ, Complex.ofReal_neg, ite_true] at h
      convert h using 1; ring
    · -- k ≠ j terms vanish
      intro k _ hk
      have hjk : j ≠ k := hk.symm
      simp only [hM_def, Matrix.sub_apply, Matrix.one_apply, hjk, if_false,
        Matrix.mul_diagonal, negTauBasis, if_neg hk, Aℂ, mul_zero, sub_zero,
        zero_mul]
    · exact absurd (Finset.mem_univ j)
  -- Step 3: Unfold stabilityFnDiag
  simp only [stabilityFnDiag, ← hM_def]
  -- Rewrite each term: (Z * M⁻¹ · 𝟙)_i = z_i * x_i
  have hW : (Matrix.diagonal (negTauBasis j τ) * M⁻¹).mulVec (fun _ => (1 : ℂ)) =
      fun i => negTauBasis j τ i * x i := by
    have : (Matrix.diagonal (negTauBasis j τ) * M⁻¹).mulVec (fun _ => (1 : ℂ)) =
        (Matrix.diagonal (negTauBasis j τ)).mulVec x := by
      rw [← Matrix.mulVec_mulVec]
    rw [this]; ext i; exact Matrix.mulVec_diagonal _ _ _
  simp_rw [hW]
  -- Step 4: The sum collapses to b_j * (-τ) * x_j
  simp only [negTauBasis, bℂ, ite_mul, zero_mul, mul_ite, mul_zero, Complex.ofReal_neg]
  rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, if_true]
  -- Goal: 1 + b_j * (-τ * x_j) = (1 + τ(A_jj - b_j)) / (1 + τ A_jj)
  rw [eq_div_iff hdet]
  linear_combination -(↑τ : ℂ) * (↑(t.b j) : ℂ) * hxj

/-- If `bⱼ < 0` and `τ > 0` is small enough, then `R(−τ Eⱼⱼ) > 1`. -/
lemma norm_stabilityFn_negTauBasis_gt_one (t : ButcherTableau s) (j : Fin s)
    (hbj : t.b j < 0) :
    ∃ τ : ℝ, 0 < τ ∧
      (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)).det ≠ 0 ∧
      1 < ‖t.stabilityFnDiag (negTauBasis j τ)‖ := by
  -- Choose τ = 1/(2 + 2|A_jj|)
  set τ := 1 / (2 + 2 * |t.A j j|) with hτ_def
  have hτ_pos : 0 < τ := by positivity
  -- det(I - AZ) = 1 + τ A_jj
  have hdet_eq : (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)).det =
      1 + (τ : ℂ) * (t.A j j : ℂ) := det_negTauBasis t j τ
  -- 1 + τ A_jj > 0 (real), hence ≠ 0 (complex)
  have hone_plus_pos : (0 : ℝ) < 1 + τ * t.A j j := by
    have habs : τ * |t.A j j| < 1 := by
      rw [hτ_def, div_mul_eq_mul_div, one_mul]
      rw [div_lt_one (by positivity : (0 : ℝ) < 2 + 2 * |t.A j j|)]
      linarith [abs_nonneg (t.A j j)]
    have := neg_abs_le (t.A j j)
    nlinarith
  have hdet_ne : (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)).det ≠ 0 := by
    rw [hdet_eq]
    exact_mod_cast ne_of_gt hone_plus_pos
  have hR_eq := stabilityFn_negTauBasis t j τ (by rwa [← hdet_eq])
  refine ⟨τ, hτ_pos, hdet_ne, ?_⟩
  rw [hR_eq]
  -- R = (1 + τ(A_jj - b_j)) / (1 + τ A_jj), b_j < 0, so num > denom > 0
  have hnum_real : (1 : ℂ) + ↑τ * (↑(t.A j j) - ↑(t.b j)) =
    ((1 + τ * (t.A j j - t.b j) : ℝ) : ℂ) := by push_cast; ring
  have hden_real : (1 : ℂ) + ↑τ * ↑(t.A j j) =
    ((1 + τ * t.A j j : ℝ) : ℂ) := by push_cast; ring
  rw [hnum_real, hden_real, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (by nlinarith) hone_plus_pos), one_lt_div₀ hone_plus_pos]
  nlinarith

/-- **AN-stable implies non-negative weights**: `bⱼ ≥ 0` for all `j`. -/
theorem IsANStable.hasNonNegWeights {t : ButcherTableau s} (h : t.IsANStable) :
    t.HasNonNegWeights := by
  intro j; by_contra hbj; push_neg at hbj
  obtain ⟨τ, hτ, hdet, hgt⟩ := norm_stabilityFn_negTauBasis_gt_one t j hbj
  exact absurd (h _ (negTauBasis_re_le hτ.le) hdet) (not_le.mpr hgt)

/-! ## Part 2: AN-stable ⟹ M positive semidefinite

Choose `zⱼ = i·τ·vⱼ` (purely imaginary). Then:
  `|R(Z)|² = 1 − τ² vᵀMv + O(τ³)`
If `vᵀMv < 0`, then `|R| > 1` for small `τ > 0`.
-/

/-- Purely imaginary diagonal vector: `i·τ·vⱼ`. -/
private def imagBasis (v : Fin s → ℝ) (τ : ℝ) : Fin s → ℂ :=
  fun i => Complex.I * (τ : ℂ) * (v i : ℂ)

private lemma imagBasis_re_le (v : Fin s → ℝ) {τ : ℝ} (_hτ : 0 ≤ τ) :
    ∀ i, (imagBasis v τ i).re ≤ 0 := by
  intro i; simp only [imagBasis]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf; simp

/-- If `vᵀMv < 0` and `τ > 0` is small enough, then `|R(iτ·diag(v))| > 1`. -/
lemma norm_stabilityFn_imagBasis_gt_one (t : ButcherTableau s) (v : Fin s → ℝ)
    (hv : ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j < 0) :
    ∃ τ : ℝ, 0 < τ ∧
      (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ)).det ≠ 0 ∧
      1 < ‖t.stabilityFnDiag (imagBasis v τ)‖ := by
  sorry

/-- **AN-stable implies M is positive semidefinite.** -/
theorem IsANStable.algStabMatrix_psd {t : ButcherTableau s} (h : t.IsANStable) :
    ∀ v : Fin s → ℝ,
      0 ≤ ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j := by
  intro v; by_contra hv; push_neg at hv
  obtain ⟨τ, hτ, hdet, hgt⟩ := norm_stabilityFn_imagBasis_gt_one t v hv
  exact absurd (h _ (imagBasis_re_le v hτ.le) hdet) (not_le.mpr hgt)

/-! ## Main theorem -/

/-- **Theorem 356C** (Iserles): AN-stability implies algebraic stability.

An `s`-stage implicit RK method `(A, b, c)` is AN-stable only if
`bⱼ ≥ 0` for all `j` and the matrix `M_{ij} = bᵢaᵢⱼ + bⱼaⱼᵢ − bᵢbⱼ`
is positive semidefinite.

Reference: Iserles, *A First Course in the Numerical Analysis of Differential
Equations*, Theorem 356C, p. 268. -/
theorem an_stable_implies_alg_stable {t : ButcherTableau s} (h : t.IsANStable) :
    t.IsAlgStable where
  nonneg_weights := h.hasNonNegWeights
  posdef_M := h.algStabMatrix_psd

end ButcherTableau
