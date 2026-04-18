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

def Aℂ (t : ButcherTableau s) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => (t.A i j : ℂ)

def bℂ (t : ButcherTableau s) (i : Fin s) : ℂ := (t.b i : ℂ)

def stabilityFnDiag (t : ButcherTableau s) (z : Fin s → ℂ) : ℂ :=
  let Z := Matrix.diagonal z
  let W := Z * (1 - t.Aℂ * Z)⁻¹
  1 + ∑ i : Fin s, t.bℂ i * (W.mulVec (fun _ => (1 : ℂ))) i

def IsANStable (t : ButcherTableau s) : Prop :=
  ∀ z : Fin s → ℂ,
    (∀ i, (z i).re ≤ 0) →
    (1 - t.Aℂ * Matrix.diagonal z).det ≠ 0 →
    ‖t.stabilityFnDiag z‖ ≤ 1

/-! ## Part 1: AN-stable ⟹ bⱼ ≥ 0 -/

private def negTauBasis (j : Fin s) (τ : ℝ) : Fin s → ℂ :=
  fun i => if i = j then ((-τ : ℝ) : ℂ) else 0

private lemma negTauBasis_re_le {j : Fin s} {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ i, (negTauBasis j τ i).re ≤ 0 := by
  intro i; simp only [negTauBasis]
  split_ifs with h
  · simp only [Complex.ofReal_neg, Complex.neg_re, Complex.ofReal_re]; linarith
  · simp

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

lemma stabilityFn_negTauBasis (t : ButcherTableau s) (j : Fin s) (τ : ℝ)
    (hdet : 1 + (τ : ℂ) * (t.A j j : ℂ) ≠ 0) :
    t.stabilityFnDiag (negTauBasis j τ) =
      (1 + (τ : ℂ) * ((t.A j j : ℂ) - (t.b j : ℂ))) /
      (1 + (τ : ℂ) * (t.A j j : ℂ)) := by
  have hdet' : (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)).det ≠ 0 := by
    rw [det_negTauBasis]; exact hdet
  set M := (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)) with hM_def
  set x := M⁻¹.mulVec (fun _ => (1 : ℂ)) with hx_def
  have hMx : M.mulVec x = fun _ => 1 := by
    have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet'.isUnit
    rw [hx_def, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hxj : (1 + (τ : ℂ) * (t.A j j : ℂ)) * x j = 1 := by
    have h := congr_fun hMx j
    simp only [Matrix.mulVec, dotProduct] at h
    rw [Finset.sum_eq_single j] at h
    · simp only [hM_def, Matrix.sub_apply, Matrix.one_apply,
        Matrix.mul_diagonal, negTauBasis, Aℂ, Complex.ofReal_neg, ite_true] at h
      convert h using 1; ring
    · intro k _ hk
      have hjk : j ≠ k := hk.symm
      simp only [hM_def, Matrix.sub_apply, Matrix.one_apply, hjk, if_false,
        Matrix.mul_diagonal, negTauBasis, if_neg hk, Aℂ, mul_zero, sub_zero,
        zero_mul]
    · exact absurd (Finset.mem_univ j)
  simp only [stabilityFnDiag, ← hM_def]
  have hW : (Matrix.diagonal (negTauBasis j τ) * M⁻¹).mulVec (fun _ => (1 : ℂ)) =
      fun i => negTauBasis j τ i * x i := by
    have : (Matrix.diagonal (negTauBasis j τ) * M⁻¹).mulVec (fun _ => (1 : ℂ)) =
        (Matrix.diagonal (negTauBasis j τ)).mulVec x := by
      rw [← Matrix.mulVec_mulVec]
    rw [this]; ext i; exact Matrix.mulVec_diagonal _ _ _
  simp_rw [hW]
  simp only [negTauBasis, bℂ, ite_mul, zero_mul, mul_ite, mul_zero, Complex.ofReal_neg]
  rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, if_true]
  rw [eq_div_iff hdet]
  linear_combination -(↑τ : ℂ) * (↑(t.b j) : ℂ) * hxj

lemma norm_stabilityFn_negTauBasis_gt_one (t : ButcherTableau s) (j : Fin s)
    (hbj : t.b j < 0) :
    ∃ τ : ℝ, 0 < τ ∧
      (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)).det ≠ 0 ∧
      1 < ‖t.stabilityFnDiag (negTauBasis j τ)‖ := by
  set τ := 1 / (2 + 2 * |t.A j j|) with hτ_def
  have hτ_pos : 0 < τ := by positivity
  have hdet_eq : (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)).det =
      1 + (τ : ℂ) * (t.A j j : ℂ) := det_negTauBasis t j τ
  have hone_plus_pos : (0 : ℝ) < 1 + τ * t.A j j := by
    have habs : τ * |t.A j j| < 1 := by
      rw [hτ_def, div_mul_eq_mul_div, one_mul]
      rw [div_lt_one (by positivity : (0 : ℝ) < 2 + 2 * |t.A j j|)]
      linarith [abs_nonneg (t.A j j)]
    have := neg_abs_le (t.A j j)
    nlinarith
  have hdet_ne : (1 - t.Aℂ * Matrix.diagonal (negTauBasis j τ)).det ≠ 0 := by
    rw [hdet_eq]; exact_mod_cast ne_of_gt hone_plus_pos
  have hR_eq := stabilityFn_negTauBasis t j τ (by rwa [← hdet_eq])
  refine ⟨τ, hτ_pos, hdet_ne, ?_⟩
  rw [hR_eq]
  have hnum_real : (1 : ℂ) + ↑τ * (↑(t.A j j) - ↑(t.b j)) =
    ((1 + τ * (t.A j j - t.b j) : ℝ) : ℂ) := by push_cast; ring
  have hden_real : (1 : ℂ) + ↑τ * ↑(t.A j j) =
    ((1 + τ * t.A j j : ℝ) : ℂ) := by push_cast; ring
  rw [hnum_real, hden_real, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (by nlinarith) hone_plus_pos), one_lt_div₀ hone_plus_pos]
  nlinarith

theorem IsANStable.hasNonNegWeights {t : ButcherTableau s} (h : t.IsANStable) :
    t.HasNonNegWeights := by
  intro j; by_contra hbj; push_neg at hbj
  obtain ⟨τ, hτ, hdet, hgt⟩ := norm_stabilityFn_negTauBasis_gt_one t j hbj
  exact absurd (h _ (negTauBasis_re_le hτ.le) hdet) (not_le.mpr hgt)

/-! ## Part 2: AN-stable ⟹ M positive semidefinite -/

private def imagBasis (v : Fin s → ℝ) (τ : ℝ) : Fin s → ℂ :=
  fun i => Complex.I * (τ : ℂ) * (v i : ℂ)

private lemma imagBasis_re_le (v : Fin s → ℝ) {τ : ℝ} (_hτ : 0 ≤ τ) :
    ∀ i, (imagBasis v τ i).re ≤ 0 := by
  intro i; simp only [imagBasis, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring_nf; simp only [le_refl]

private lemma algStabMatrix_quadForm_eq (t : ButcherTableau s) (v : Fin s → ℝ) :
    ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j =
      2 * (∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j) -
        (∑ i : Fin s, t.b i * v i) ^ 2 := by
  have h_expand : ∀ i j : Fin s, v i * t.algStabMatrix i j * v j =
      t.b i * v i * t.A i j * v j + t.b j * v j * t.A j i * v i -
        t.b i * v i * t.b j * v j := by
    intro i j; rw [algStabMatrix]; ring
  simp_rw [h_expand, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have h_sq : ∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.b j * v j =
      (∑ i : Fin s, t.b i * v i) ^ 2 := by
    have : ∀ i j : Fin s, t.b i * v i * t.b j * v j = (t.b i * v i) * (t.b j * v j) := by
      intros; ring
    simp_rw [this, sq, ← Finset.sum_mul_sum]
  have h_sym : ∑ i : Fin s, ∑ j : Fin s, t.b j * v j * t.A j i * v i =
      ∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j := Finset.sum_comm
  linarith [h_sq, h_sym]

private lemma imagBasis_zero (v : Fin s → ℝ) : imagBasis v 0 = 0 := by
  ext i; simp [imagBasis]

private lemma continuous_det_imagBasis (t : ButcherTableau s) (v : Fin s → ℝ) :
    Continuous (fun τ : ℝ => (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ)).det) := by
  unfold imagBasis Aℂ; fun_prop

private lemma det_imagBasis_zero (t : ButcherTableau s) (v : Fin s → ℝ) :
    (1 - t.Aℂ * Matrix.diagonal (imagBasis v 0)).det = 1 := by
  rw [imagBasis_zero]; simp

private lemma exists_det_ne_zero_ball (t : ButcherTableau s) (v : Fin s → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, |τ| < δ →
      (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ)).det ≠ 0 := by
  have hcont : ContinuousAt
      (fun τ : ℝ => (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ)).det) 0 :=
    (continuous_det_imagBasis t v).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont 1 one_pos
  refine ⟨δ, hδ, fun τ hτ => ?_⟩
  have hmem : dist τ 0 < δ := by rwa [Real.dist_eq, sub_zero]
  have hdist := hball hmem
  rw [det_imagBasis_zero] at hdist
  intro heq; rw [heq] at hdist; simp at hdist

private lemma stabilityFnDiag_imagBasis_eq (t : ButcherTableau s) (v : Fin s → ℝ) (τ : ℝ)
    (_hdet : (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ)).det ≠ 0) :
    t.stabilityFnDiag (imagBasis v τ) =
      1 + Complex.I * (τ : ℂ) *
        ∑ i : Fin s, (t.b i : ℂ) * (v i : ℂ) *
          ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) i := by
  unfold ButcherTableau.stabilityFnDiag
  norm_num [Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm]
  unfold ButcherTableau.bℂ imagBasis; simp +decide [mul_assoc, mul_comm, mul_left_comm]

private lemma sum_bv_decomp (t : ButcherTableau s) (v : Fin s → ℝ) (τ : ℝ)
    (hdet : (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ)).det ≠ 0) :
    let x := (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)
    ∑ i : Fin s, (t.b i : ℂ) * (v i : ℂ) * x i =
      (∑ i : Fin s, (t.b i : ℂ) * (v i : ℂ)) +
      Complex.I * (τ : ℂ) *
        ∑ i : Fin s, ∑ j : Fin s,
          (t.b i : ℂ) * (v i : ℂ) * (t.Aℂ i j) * (v j : ℂ) * x j := by
  -- By definition of $x$, we know that $x_i = 1 + \sum_j A_{ij} z_j x_j$.
  have hx_def : ∀ i, ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) i = 1 + ∑ j, t.Aℂ i j * (imagBasis v τ j) * ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) j := by
    intro i
    have := congr_fun ( show (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ)).mulVec ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) = fun _ => 1 from by
                          simp +decide [hdet, isUnit_iff_ne_zero] ) i
    simp [Matrix.mulVec] at this
    exact (by
    simp +decide [ dotProduct, Finset.sum_sub_distrib, sub_mul ] at this ⊢;
    simp +decide [ Matrix.one_apply ] at this ⊢ ; linear_combination this);
  convert Finset.sum_congr rfl fun i _ => congr_arg ( fun x : ℂ => ( t.b i : ℂ ) * v i * x ) ( hx_def i ) using 1;
  simp +decide [mul_add, Finset.sum_add_distrib, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, imagBasis]

private lemma continuousAt_imagBasis_inv (t : ButcherTableau s) (v : Fin s → ℝ) :
    ContinuousAt (fun τ : ℝ => (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹) 0 := by
  refine' ContinuousAt.comp ( show ContinuousAt ( fun m : Matrix ( Fin s ) ( Fin s ) ℂ => m⁻¹ ) _ from _ ) _;
  · simp_all +decide [ Matrix.inv_def ];
    refine' ContinuousAt.smul _ _;
    · exact ContinuousAt.inv₀ ( Continuous.continuousAt ( by exact Continuous.matrix_det continuous_id' ) ) ( by simp [ imagBasis_zero ] );
    · exact Continuous.continuousAt ( by exact Continuous.matrix_adjugate continuous_id' );
  · refine' Continuous.continuousAt _;
    refine' continuous_const.sub _;
    exact continuous_pi_iff.mpr fun i => continuous_pi_iff.mpr fun j => by by_cases hi : i = j <;> continuity

lemma norm_stabilityFn_imagBasis_gt_one (t : ButcherTableau s) (v : Fin s → ℝ)
    (hv : ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j < 0) :
    ∃ τ : ℝ, 0 < τ ∧
      (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ)).det ≠ 0 ∧
      1 < ‖t.stabilityFnDiag (imagBasis v τ)‖ := by
  obtain ⟨δ, hδ_pos, hδ_det⟩ : ∃ δ > 0, ∀ τ : ℝ, |τ| < δ → (1 - t.Aℂ * Matrix.diagonal (imagBasis v τ)).det ≠ 0 := exists_det_ne_zero_ball t v;
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ε ≤ δ ∧ ∀ τ : ℝ, 0 < τ ∧ τ < ε → (∑ i : Fin s, t.b i * v i) ^ 2 - 2 * Complex.re (∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j * ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) j) - 2 * τ * (∑ i : Fin s, t.b i * v i) * Complex.im (∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j * ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) j) + τ ^ 2 * ‖∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j * ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) j‖ ^ 2 > 0 := by
    have h_cont : ContinuousAt (fun τ : ℝ => (∑ i : Fin s, t.b i * v i) ^ 2 - 2 * Complex.re (∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j * ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) j) - 2 * τ * (∑ i : Fin s, t.b i * v i) * Complex.im (∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j * ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) j) + τ ^ 2 * ‖∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j * ((1 - t.Aℂ * Matrix.diagonal (imagBasis v τ))⁻¹.mulVec (fun _ => 1)) j‖ ^ 2) 0 := by
      have h_cont_adj := continuousAt_imagBasis_inv t v
      fun_prop (disch := norm_num);
    have h_pos : (∑ i : Fin s, t.b i * v i) ^ 2 - 2 * (∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j) > 0 := by
      have := algStabMatrix_quadForm_eq t v; norm_num [ ButcherTableau.algStabMatrix ] at *; linarith;
    obtain ⟨ ε, hε₁, hε₂ ⟩ := Metric.mem_nhds_iff.mp ( h_cont.eventually ( lt_mem_nhds <| show ( ∑ i : Fin s, t.b i * v i ) ^ 2 - 2 * ( ∑ i : Fin s, ∑ j : Fin s, ↑ ( t.b i ) * ↑ ( v i ) * ↑ ( t.A i j ) * ↑ ( v j ) * ( 1 - t.Aℂ * Matrix.diagonal ( imagBasis v 0 ) ) ⁻¹.mulVec ( fun x => 1 ) j ).re - ( 2 * 0 * ∑ i : Fin s, t.b i * v i ) * ( ∑ i : Fin s, ∑ j : Fin s, ↑ ( t.b i ) * ↑ ( v i ) * ↑ ( t.A i j ) * ↑ ( v j ) * ( 1 - t.Aℂ * Matrix.diagonal ( imagBasis v 0 ) ) ⁻¹.mulVec ( fun x => 1 ) j ).im + 0 ^ 2 * ‖∑ i : Fin s, ∑ j : Fin s, ↑ ( t.b i ) * ↑ ( v i ) * ↑ ( t.A i j ) * ↑ ( v j ) * ( 1 - t.Aℂ * Matrix.diagonal ( imagBasis v 0 ) ) ⁻¹.mulVec ( fun x => 1 ) j‖ ^ 2 > 0 from by
                                                                                            convert h_pos using 1 ; norm_cast ; norm_num [ imagBasis_zero ] ) );
    exact ⟨ Min.min ε δ, lt_min hε₁ hδ_pos, min_le_right _ _, fun τ hτ => hε₂ <| mem_ball_zero_iff.mpr <| abs_lt.mpr ⟨ by linarith [ min_le_left ε δ ], by linarith [ min_le_left ε δ ] ⟩ ⟩;
  refine' ⟨ ε / 2, half_pos hε_pos, hδ_det _ ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ), _ ⟩;
  -- By definition of $R$, we have $R = 1 + iτα - τ²S$.
  have hR : t.stabilityFnDiag (imagBasis v (ε / 2)) = 1 + Complex.I * (ε / 2) * (∑ i : Fin s, t.b i * v i) - (ε / 2) ^ 2 * ∑ i : Fin s, ∑ j : Fin s, t.b i * v i * t.A i j * v j * ((1 - t.Aℂ * Matrix.diagonal (imagBasis v (ε / 2)))⁻¹.mulVec (fun _ => 1)) j := by
    rw [ stabilityFnDiag_imagBasis_eq, sum_bv_decomp ];
    · norm_num [ Complex.ext_iff, sq ] ; ring_nf;
      norm_num [ ButcherTableau.Aℂ ];
    · exact hδ_det _ ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ );
    · exact hδ_det _ ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ );
  norm_num [ Complex.normSq, Complex.norm_def, hR ];
  refine' Real.lt_sqrt_of_sq_lt _;
  norm_cast at *;
  have := hε.2 ( ε / 2 ) ⟨ by linarith, by linarith ⟩ ; norm_num [ Complex.normSq, Complex.sq_norm ] at * ; nlinarith [ pow_pos hε_pos 3 ] ;

theorem IsANStable.algStabMatrix_psd {t : ButcherTableau s} (h : t.IsANStable) :
    ∀ v : Fin s → ℝ,
      0 ≤ ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j := by
  intro v; by_contra hv; push_neg at hv
  obtain ⟨τ, hτ, hdet, hgt⟩ := norm_stabilityFn_imagBasis_gt_one t v hv
  exact absurd (h _ (imagBasis_re_le v hτ.le) hdet) (not_le.mpr hgt)

/-! ## Main theorem -/

theorem an_stable_implies_alg_stable {t : ButcherTableau s} (h : t.IsANStable) :
    t.IsAlgStable where
  nonneg_weights := h.hasNonNegWeights
  posdef_M := h.algStabMatrix_psd

end ButcherTableau