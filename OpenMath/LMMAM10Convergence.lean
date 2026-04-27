import OpenMath.LMMTruncationOp
import OpenMath.LMMAB11Convergence
import OpenMath.AdamsMethods

/-! ## Adams--Moulton 10-step Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit Adams--Moulton
10-step method.  This extends the AM2--AM9 scalar ladder using the public
twelfth-order Taylor helpers from `OpenMath.LMMAB11Convergence`.

The AM10 coefficients are obtained by integrating the Lagrange basis on
nodes 0,...,10 over `[9, 10]`; over the common denominator `479001600` they
are `[-3250433, 36284876, -184776195, 567450984, -1170597042, 1710774528,
-1823311566, 1446205080, -890175549, 656185652, 134211265]`, summing to
`479001600`.

The absolute-weight sum is `862322317/47900160`, so after division by the
implicit new-point factor the growth is slackened to `37L`.  The exact
twelfth-order residual coefficient is approximately `5044.91`, slackened to
`5045`. -/

namespace LMM

/-- AM10 coefficients as a compact reusable finite vector. -/
noncomputable def am10Coeff : Fin 11 → ℝ :=
  ![-3250433/479001600, 36284876/479001600,
    -184776195/479001600, 567450984/479001600,
    -1170597042/479001600, 1710774528/479001600,
    -1823311566/479001600, 1446205080/479001600,
    -890175549/479001600, 656185652/479001600,
    134211265/479001600]

/-- The ten already-known AM10 coefficients, excluding the implicit new point. -/
noncomputable def am10ExplicitCoeff (j : Fin 10) : ℝ :=
  am10Coeff ⟨j, by omega⟩

/-- Textbook AM10 residual at base point `t`. -/
noncomputable def am10Residual (h t : ℝ) (y : ℝ → ℝ) : ℝ :=
  y (t + 10 * h) - y (t + 9 * h)
    - h * ∑ j : Fin 11, am10Coeff j * deriv y (t + (j : ℕ) * h)

/-- AM10 trajectory predicate:
`y_{n+10} = y_{n+9} + h * sum_j beta_j f(t_n + jh, y_{n+j})`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM10Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 10)
      = y (n + 9)
        + h * ∑ j : Fin 11,
            am10Coeff j * f (t₀ + (n : ℝ) * h + (j : ℕ) * h)
              (y (n + (j : ℕ)))

/-- Scalar pointwise error at an index. -/
noncomputable def am10Err (h t₀ : ℝ) (yseq : ℕ → ℝ) (y : ℝ → ℝ)
    (k : ℕ) : ℝ :=
  |yseq k - y (t₀ + (k : ℝ) * h)|

/-- Rolling AM10 ten-sample window max. -/
noncomputable def am10ErrWindow (h t₀ : ℝ) (yseq : ℕ → ℝ) (y : ℝ → ℝ)
    (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin 10 => am10Err h t₀ yseq y (k + (j : ℕ)))

lemma am10ErrWindow_nonneg (h t₀ : ℝ) (yseq : ℕ → ℝ) (y : ℝ → ℝ)
    (k : ℕ) : 0 ≤ am10ErrWindow h t₀ yseq y k := by
  unfold am10ErrWindow
  exact (abs_nonneg _).trans
    (Finset.le_sup' (b := (0 : Fin 10))
      (f := fun j : Fin 10 => am10Err h t₀ yseq y (k + (j : ℕ)))
      (Finset.mem_univ _))

/-- AM10 local truncation operator reduces to the textbook residual. -/
theorem am10_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsMoulton10.localTruncationError h t y = am10Residual h t y := by
  unfold localTruncationError truncationOp am10Residual
  simp [adamsMoulton10, am10Coeff, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  norm_num
  ring

/-- One-step AM10 Lipschitz inequality before dividing by the implicit
new-point factor. -/
theorem am10_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) (_hL : 0 ≤ L)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM10Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (134211265 / 479001600 : ℝ) * h * L)
        * am10Err h t₀ yseq y (n + 10)
      ≤ am10Err h t₀ yseq y (n + 9)
        + h * L * ∑ j : Fin 10,
            |am10ExplicitCoeff j| * am10Err h t₀ yseq y (n + (j : ℕ))
        + |adamsMoulton10.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  set τ : ℝ := adamsMoulton10.localTruncationError h t y with hτ_def
  set Sa : ℝ := ∑ j : Fin 11,
      am10Coeff j * f (t + (j : ℕ) * h) (yseq (n + (j : ℕ))) with hSa_def
  set Sy : ℝ := ∑ j : Fin 11,
      am10Coeff j * f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)) with hSy_def
  have hstep : yseq (n + 10) = yseq (n + 9) + h * Sa := by
    simpa [hSa_def, ht_def, add_assoc] using hy.recurrence n
  have hτ_alt : τ = y (t + 10 * h) - y (t + 9 * h) - h * Sy := by
    show adamsMoulton10.localTruncationError h t y = _
    rw [am10_localTruncationError_eq]
    unfold am10Residual
    have hcong :
        (fun j : Fin 11 => am10Coeff j * deriv y (t + (j : ℕ) * h))
          = (fun j : Fin 11 =>
              am10Coeff j * f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))) := by
      funext j
      rw [hyf]
    rw [hcong, hSy_def]
  set Sd : ℝ := ∑ j : Fin 11, am10Coeff j
      * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
        - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))) with hSd_def
  have hSa_sub_Sy : Sa - Sy = Sd := by
    rw [hSa_def, hSy_def, hSd_def, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have halg :
      yseq (n + 10) - y (t + 10 * h)
        = (yseq (n + 9) - y (t + 9 * h)) + h * Sd - τ := by
    rw [hstep, hτ_alt, ← hSa_sub_Sy]
    ring
  have hdiff_bound : ∀ j : Fin 11,
      |am10Coeff j
          * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))|
        ≤ |am10Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by
    intro j
    have hLip := hf (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
      (y (t + (j : ℕ) * h))
    rw [abs_mul]
    have hcoeff_nn : 0 ≤ |am10Coeff j| := abs_nonneg _
    calc
      |am10Coeff j| *
          |f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))|
          ≤ |am10Coeff j| *
              (L * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)|) :=
            mul_le_mul_of_nonneg_left hLip hcoeff_nn
      _ = |am10Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by ring
  have hSd_abs :
      |Sd| ≤ ∑ j : Fin 11, |am10Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by
    rw [hSd_def]
    calc
      |∑ j : Fin 11, am10Coeff j
          * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))|
          ≤ ∑ j : Fin 11,
              |am10Coeff j
                * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
                  - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 11, |am10Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| :=
            Finset.sum_le_sum (fun j _ => hdiff_bound j)
  have htri :
      |yseq (n + 10) - y (t + 10 * h)|
        ≤ |yseq (n + 9) - y (t + 9 * h)| + |h * Sd| + |τ| := by
    rw [halg]
    have h1 :
        |(yseq (n + 9) - y (t + 9 * h)) + h * Sd - τ|
          ≤ |(yseq (n + 9) - y (t + 9 * h)) + h * Sd| + |τ| :=
      abs_sub _ _
    have h2 :
        |(yseq (n + 9) - y (t + 9 * h)) + h * Sd|
          ≤ |yseq (n + 9) - y (t + 9 * h)| + |h * Sd| :=
      abs_add_le _ _
    linarith
  have h_hSd :
      |h * Sd| ≤ h * ∑ j : Fin 11, |am10Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by
    rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hSd_abs hh
  have hmain_local :
      |yseq (n + 10) - y (t + 10 * h)|
        ≤ |yseq (n + 9) - y (t + 9 * h)|
          + h * ∑ j : Fin 11, |am10Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)|
          + |τ| := by
    linarith
  have hsplit :
      h * ∑ j : Fin 11, |am10Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)|
        = h * L * ∑ j : Fin 10,
            |am10ExplicitCoeff j| * am10Err h t₀ yseq y (n + (j : ℕ))
          + (134211265 / 479001600 : ℝ) * h * L
              * am10Err h t₀ yseq y (n + 10) := by
    simp [am10Coeff, am10ExplicitCoeff, am10Err, Fin.sum_univ_succ, ht_def]
    ring_nf
  have hmain :
      am10Err h t₀ yseq y (n + 10)
        ≤ am10Err h t₀ yseq y (n + 9)
          + h * L * ∑ j : Fin 10,
            |am10ExplicitCoeff j| * am10Err h t₀ yseq y (n + (j : ℕ))
          + (134211265 / 479001600 : ℝ) * h * L
              * am10Err h t₀ yseq y (n + 10)
          + |adamsMoulton10.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
    have hmain_local' := hmain_local
    rw [hsplit] at hmain_local'
    simpa [am10Err, ht_def, Nat.cast_add, add_mul, add_assoc, add_left_comm,
      add_comm, hτ_def] using hmain_local'
  linarith [hmain]

/-- Divided AM10 one-step error bound at the new point. -/
theorem am10_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (134211265 / 479001600 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM10Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    am10Err h t₀ yseq y (n + 10)
      ≤ (1 + h * (37 * L)) * am10ErrWindow h t₀ yseq y n
        + 2 * |adamsMoulton10.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set E : ℝ := am10ErrWindow h t₀ yseq y n with hE_def
  set τabs : ℝ :=
    |adamsMoulton10.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hE_nn : 0 ≤ E := by
    simpa [hE_def] using am10ErrWindow_nonneg h t₀ yseq y n
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 239500800 / 134211265 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (134211265 / 479001600 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hwin : ∀ j : Fin 10,
      am10Err h t₀ yseq y (n + (j : ℕ)) ≤ E := by
    intro j
    show am10Err h t₀ yseq y (n + (j : ℕ))
        ≤ am10ErrWindow h t₀ yseq y n
    unfold am10ErrWindow
    exact Finset.le_sup' (b := j)
      (f := fun k : Fin 10 => am10Err h t₀ yseq y (n + (k : ℕ)))
      (Finset.mem_univ _)
  have he9_le_E : am10Err h t₀ yseq y (n + 9) ≤ E :=
    hwin ⟨9, by norm_num⟩
  have hsum_le :
      ∑ j : Fin 10, |am10ExplicitCoeff j| * am10Err h t₀ yseq y (n + (j : ℕ))
        ≤ (17149519 / 967680 : ℝ) * E := by
    calc
      ∑ j : Fin 10, |am10ExplicitCoeff j| * am10Err h t₀ yseq y (n + (j : ℕ))
          ≤ ∑ j : Fin 10, |am10ExplicitCoeff j| * E :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (hwin j) (abs_nonneg _))
      _ = (17149519 / 967680 : ℝ) * E := by
        simp [am10ExplicitCoeff, am10Coeff, Fin.sum_univ_succ]
        ring
  have hstep :=
    am10_one_step_lipschitz (h := h) (L := L) hh hL hf t₀ hy y hyf n
  have hR_le :
      am10Err h t₀ yseq y (n + 9)
        + h * L * ∑ j : Fin 10,
            |am10ExplicitCoeff j| * am10Err h t₀ yseq y (n + (j : ℕ))
        + τabs
        ≤ (1 + (17149519 / 967680 : ℝ) * (h * L)) * E + τabs := by
    have hsum_scaled :
        h * L * ∑ j : Fin 10,
            |am10ExplicitCoeff j| * am10Err h t₀ yseq y (n + (j : ℕ))
          ≤ h * L * ((17149519 / 967680 : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hsum_le hx_nn
    have h_alg :
        E + h * L * ((17149519 / 967680 : ℝ) * E) + τabs
          = (1 + (17149519 / 967680 : ℝ) * (h * L)) * E + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (17149519 / 967680 : ℝ) * (h * L)
        ≤ (1 - (134211265 / 479001600 : ℝ) * h * L)
            * (1 + h * (37 * L)) := by
    have hxL_eq :
        (1 - (134211265 / 479001600 : ℝ) * h * L)
            * (1 + h * (37 * L))
          - (1 + (17149519 / 967680 : ℝ) * (h * L))
          = (h * L) / 479001600 * (9099836030 - 4965816805 * (h * L)) := by
      ring
    have hpos : 0 ≤ 9099836030 - 4965816805 * (h * L) := by
      have hbound :
          4965816805 * (h * L)
            ≤ 4965816805 * (239500800 / 134211265 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hx_small (by norm_num)
      have hnum :
          (4965816805 : ℝ) * (239500800 / 134211265) ≤ 9099836030 := by
        norm_num
      exact sub_nonneg.mpr (le_trans hbound hnum)
    have hprod : 0 ≤ (h * L) / 479001600 * (9099836030 - 4965816805 * (h * L)) := by
      exact mul_nonneg (by positivity) hpos
    apply sub_nonneg.mp
    rw [hxL_eq]
    exact hprod
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (134211265 / 479001600 : ℝ) * h * L) * 2 := by
    set x : ℝ := (134211265 / 479001600 : ℝ) * h * L with hx_def
    change (1 : ℝ) ≤ (1 - x) * 2
    have hxle : x ≤ 1 / 2 := by simpa [hx_def] using hsmall
    nlinarith
  have hE_part :
      (1 + (17149519 / 967680 : ℝ) * (h * L)) * E
        ≤ ((1 - (134211265 / 479001600 : ℝ) * h * L)
            * (1 + h * (37 * L))) * E :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (134211265 / 479001600 : ℝ) * h * L) * 2) * τabs := by
    have hraw := mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
    calc
      τabs = (1 : ℝ) * τabs := by ring
      _ ≤ ((1 - (134211265 / 479001600 : ℝ) * h * L) * 2) * τabs := hraw
  have hfactor :
      (1 + (17149519 / 967680 : ℝ) * (h * L)) * E + τabs
        ≤ (1 - (134211265 / 479001600 : ℝ) * h * L)
            * ((1 + h * (37 * L)) * E + 2 * τabs) := by
    let A : ℝ := 1 - (134211265 / 479001600 : ℝ) * h * L
    let B : ℝ := 1 + h * (37 * L)
    let Cg : ℝ := 1 + (17149519 / 967680 : ℝ) * (h * L)
    change Cg * E + τabs ≤ A * (B * E + 2 * τabs)
    have hE_part' : Cg * E ≤ (A * B) * E := hE_part
    have hτ_part' : τabs ≤ (A * 2) * τabs := hτ_part
    calc
      Cg * E + τabs ≤ (A * B) * E + (A * 2) * τabs :=
        add_le_add hE_part' hτ_part'
      _ = A * (B * E + 2 * τabs) := by ring
  have hprod :
      (1 - (134211265 / 479001600 : ℝ) * h * L)
          * am10Err h t₀ yseq y (n + 10)
        ≤ (1 - (134211265 / 479001600 : ℝ) * h * L)
            * ((1 + h * (37 * L)) * E + 2 * τabs) :=
    le_trans hstep (le_trans (by simpa [hτabs_def] using hR_le) hfactor)
  have hcancel :
      am10Err h t₀ yseq y (n + 10)
        ≤ (1 + h * (37 * L)) * E + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  simpa [hE_def, hτabs_def] using hcancel

/-- Max-norm AM10 one-step recurrence on the rolling 10-window. -/
theorem am10_one_step_error_pair_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (134211265 / 479001600 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM10Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    am10ErrWindow h t₀ yseq y (n + 1)
      ≤ (1 + h * (37 * L)) * am10ErrWindow h t₀ yseq y n
        + 2 * |adamsMoulton10.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set E : ℝ := am10ErrWindow h t₀ yseq y n with hE_def
  set τabs : ℝ :=
    |adamsMoulton10.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set R : ℝ := (1 + h * (37 * L)) * E + 2 * τabs with hR_def
  have hE_nn : 0 ≤ E := by
    simpa [hE_def] using am10ErrWindow_nonneg h t₀ yseq y n
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have h37hL_nn : 0 ≤ h * (37 * L) := by positivity
  have hE_le_R : E ≤ R := by
    have hcoef : (1 : ℝ) ≤ 1 + h * (37 * L) :=
      le_add_of_nonneg_right h37hL_nn
    have hgrow : E ≤ (1 + h * (37 * L)) * E := by
      have := mul_le_mul_of_nonneg_right hcoef hE_nn
      simpa using this
    have hplus :
        (1 + h * (37 * L)) * E ≤ R := by
      rw [hR_def]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hτ_nn)
    exact le_trans hgrow hplus
  have hwin : ∀ j : Fin 10,
      am10Err h t₀ yseq y (n + (j : ℕ)) ≤ E := by
    intro j
    show am10Err h t₀ yseq y (n + (j : ℕ))
        ≤ am10ErrWindow h t₀ yseq y n
    unfold am10ErrWindow
    exact Finset.le_sup' (b := j)
      (f := fun k : Fin 10 => am10Err h t₀ yseq y (n + (k : ℕ)))
      (Finset.mem_univ _)
  have hnew :
      am10Err h t₀ yseq y (n + 10) ≤ R := by
    simpa [hE_def, hτabs_def, hR_def] using
      (am10_one_step_error_bound (h := h) (L := L) hh hL hsmall hf t₀ hy y hyf n)
  have h_per : ∀ j : Fin 10,
      am10Err h t₀ yseq y (n + 1 + (j : ℕ)) ≤ R := by
    intro j
    by_cases hj : (j : ℕ) + 1 < 10
    · have hprev := hwin ⟨(j : ℕ) + 1, hj⟩
      have hidx : n + 1 + (j : ℕ) = n + ((j : ℕ) + 1) := by omega
      rw [hidx]
      exact le_trans hprev hE_le_R
    · have hjeq : (j : ℕ) = 9 := by omega
      have hidx : n + 1 + (j : ℕ) = n + 10 := by omega
      rw [hidx]
      exact hnew
  unfold am10ErrWindow
  exact Finset.sup'_le _ _ (fun j _ => by
    simpa [hE_def, hτabs_def, hR_def] using h_per j)

private lemma am10_residual_alg_identity
    (y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 dd ddd dddd ddddd dddddd
      ddddddd dddddddd ddddddddd dddddddddd ddddddddddd h : ℝ) :
    y10 - y9 - h * ((134211265 / 479001600) * d10
                  + (656185652 / 479001600) * d9
                  - (890175549 / 479001600) * d8
                  + (1446205080 / 479001600) * d7
                  - (1823311566 / 479001600) * d6
                  + (1710774528 / 479001600) * d5
                  - (1170597042 / 479001600) * d4
                  + (567450984 / 479001600) * d3
                  - (184776195 / 479001600) * d2
                  + (36284876 / 479001600) * d1
                  - (3250433 / 479001600) * d0)
      =
        (y10 - y0 - (10 * h) * d0
            - (10 * h) ^ 2 / 2 * dd
            - (10 * h) ^ 3 / 6 * ddd
            - (10 * h) ^ 4 / 24 * dddd
            - (10 * h) ^ 5 / 120 * ddddd
            - (10 * h) ^ 6 / 720 * dddddd
            - (10 * h) ^ 7 / 5040 * ddddddd
            - (10 * h) ^ 8 / 40320 * dddddddd
            - (10 * h) ^ 9 / 362880 * ddddddddd
            - (10 * h) ^ 10 / 3628800 * dddddddddd
            - (10 * h) ^ 11 / 39916800 * ddddddddddd)
        - (y9 - y0 - (9 * h) * d0
            - (9 * h) ^ 2 / 2 * dd
            - (9 * h) ^ 3 / 6 * ddd
            - (9 * h) ^ 4 / 24 * dddd
            - (9 * h) ^ 5 / 120 * ddddd
            - (9 * h) ^ 6 / 720 * dddddd
            - (9 * h) ^ 7 / 5040 * ddddddd
            - (9 * h) ^ 8 / 40320 * dddddddd
            - (9 * h) ^ 9 / 362880 * ddddddddd
            - (9 * h) ^ 10 / 3628800 * dddddddddd
            - (9 * h) ^ 11 / 39916800 * ddddddddddd)
        - (134211265 * h / 479001600)
            * (d10 - d0 - (10 * h) * dd
                - (10 * h) ^ 2 / 2 * ddd
                - (10 * h) ^ 3 / 6 * dddd
                - (10 * h) ^ 4 / 24 * ddddd
                - (10 * h) ^ 5 / 120 * dddddd
                - (10 * h) ^ 6 / 720 * ddddddd
                - (10 * h) ^ 7 / 5040 * dddddddd
                - (10 * h) ^ 8 / 40320 * ddddddddd
                - (10 * h) ^ 9 / 362880 * dddddddddd
                - (10 * h) ^ 10 / 3628800 * ddddddddddd)
        - (656185652 * h / 479001600)
            * (d9 - d0 - (9 * h) * dd
                - (9 * h) ^ 2 / 2 * ddd
                - (9 * h) ^ 3 / 6 * dddd
                - (9 * h) ^ 4 / 24 * ddddd
                - (9 * h) ^ 5 / 120 * dddddd
                - (9 * h) ^ 6 / 720 * ddddddd
                - (9 * h) ^ 7 / 5040 * dddddddd
                - (9 * h) ^ 8 / 40320 * ddddddddd
                - (9 * h) ^ 9 / 362880 * dddddddddd
                - (9 * h) ^ 10 / 3628800 * ddddddddddd)
        + (890175549 * h / 479001600)
            * (d8 - d0 - (8 * h) * dd
                - (8 * h) ^ 2 / 2 * ddd
                - (8 * h) ^ 3 / 6 * dddd
                - (8 * h) ^ 4 / 24 * ddddd
                - (8 * h) ^ 5 / 120 * dddddd
                - (8 * h) ^ 6 / 720 * ddddddd
                - (8 * h) ^ 7 / 5040 * dddddddd
                - (8 * h) ^ 8 / 40320 * ddddddddd
                - (8 * h) ^ 9 / 362880 * dddddddddd
                - (8 * h) ^ 10 / 3628800 * ddddddddddd)
        - (1446205080 * h / 479001600)
            * (d7 - d0 - (7 * h) * dd
                - (7 * h) ^ 2 / 2 * ddd
                - (7 * h) ^ 3 / 6 * dddd
                - (7 * h) ^ 4 / 24 * ddddd
                - (7 * h) ^ 5 / 120 * dddddd
                - (7 * h) ^ 6 / 720 * ddddddd
                - (7 * h) ^ 7 / 5040 * dddddddd
                - (7 * h) ^ 8 / 40320 * ddddddddd
                - (7 * h) ^ 9 / 362880 * dddddddddd
                - (7 * h) ^ 10 / 3628800 * ddddddddddd)
        + (1823311566 * h / 479001600)
            * (d6 - d0 - (6 * h) * dd
                - (6 * h) ^ 2 / 2 * ddd
                - (6 * h) ^ 3 / 6 * dddd
                - (6 * h) ^ 4 / 24 * ddddd
                - (6 * h) ^ 5 / 120 * dddddd
                - (6 * h) ^ 6 / 720 * ddddddd
                - (6 * h) ^ 7 / 5040 * dddddddd
                - (6 * h) ^ 8 / 40320 * ddddddddd
                - (6 * h) ^ 9 / 362880 * dddddddddd
                - (6 * h) ^ 10 / 3628800 * ddddddddddd)
        - (1710774528 * h / 479001600)
            * (d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd
                - (5 * h) ^ 6 / 720 * ddddddd
                - (5 * h) ^ 7 / 5040 * dddddddd
                - (5 * h) ^ 8 / 40320 * ddddddddd
                - (5 * h) ^ 9 / 362880 * dddddddddd
                - (5 * h) ^ 10 / 3628800 * ddddddddddd)
        + (1170597042 * h / 479001600)
            * (d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd
                - (4 * h) ^ 6 / 720 * ddddddd
                - (4 * h) ^ 7 / 5040 * dddddddd
                - (4 * h) ^ 8 / 40320 * ddddddddd
                - (4 * h) ^ 9 / 362880 * dddddddddd
                - (4 * h) ^ 10 / 3628800 * ddddddddddd)
        - (567450984 * h / 479001600)
            * (d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd
                - (3 * h) ^ 6 / 720 * ddddddd
                - (3 * h) ^ 7 / 5040 * dddddddd
                - (3 * h) ^ 8 / 40320 * ddddddddd
                - (3 * h) ^ 9 / 362880 * dddddddddd
                - (3 * h) ^ 10 / 3628800 * ddddddddddd)
        + (184776195 * h / 479001600)
            * (d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd
                - (2 * h) ^ 6 / 720 * ddddddd
                - (2 * h) ^ 7 / 5040 * dddddddd
                - (2 * h) ^ 8 / 40320 * ddddddddd
                - (2 * h) ^ 9 / 362880 * dddddddddd
                - (2 * h) ^ 10 / 3628800 * ddddddddddd)
        - (36284876 * h / 479001600)
            * (d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd
                - h ^ 6 / 720 * ddddddd
                - h ^ 7 / 5040 * dddddddd
                - h ^ 8 / 40320 * ddddddddd
                - h ^ 9 / 362880 * dddddddddd
                - h ^ 10 / 3628800 * ddddddddddd) := by
  ring

private lemma am10_residual_bound_alg_identity (M h : ℝ) :
    M / 479001600 * (10 * h) ^ 12 + M / 479001600 * (9 * h) ^ 12
      + (134211265 * h / 479001600) * (M / 39916800 * (10 * h) ^ 11)
      + (656185652 * h / 479001600) * (M / 39916800 * (9 * h) ^ 11)
      + (890175549 * h / 479001600) * (M / 39916800 * (8 * h) ^ 11)
      + (1446205080 * h / 479001600) * (M / 39916800 * (7 * h) ^ 11)
      + (1823311566 * h / 479001600) * (M / 39916800 * (6 * h) ^ 11)
      + (1710774528 * h / 479001600) * (M / 39916800 * (5 * h) ^ 11)
      + (1170597042 * h / 479001600) * (M / 39916800 * (4 * h) ^ 11)
      + (567450984 * h / 479001600) * (M / 39916800 * (3 * h) ^ 11)
      + (184776195 * h / 479001600) * (M / 39916800 * (2 * h) ^ 11)
      + (36284876 * h / 479001600) * (M / 39916800 * h ^ 11)
      = (251196920117213671 / 49792216320000 : ℝ) * M * h ^ 12 := by
  ring

private lemma am10_residual_twelve_term_triangle
    (A B C D E F G H I J K L h : ℝ) (hh : 0 ≤ h) :
    |A - B - (134211265 * h / 479001600) * C - (656185652 * h / 479001600) * D + (890175549 * h / 479001600) * E - (1446205080 * h / 479001600) * F + (1823311566 * h / 479001600) * G - (1710774528 * h / 479001600) * H + (1170597042 * h / 479001600) * I - (567450984 * h / 479001600) * J + (184776195 * h / 479001600) * K - (36284876 * h / 479001600) * L|
      ≤ |A| + |B| + (134211265 * h / 479001600) * |C| + (656185652 * h / 479001600) * |D| + (890175549 * h / 479001600) * |E| + (1446205080 * h / 479001600) * |F| + (1823311566 * h / 479001600) * |G| + (1710774528 * h / 479001600) * |H| + (1170597042 * h / 479001600) * |I| + (567450984 * h / 479001600) * |J| + (184776195 * h / 479001600) * |K| + (36284876 * h / 479001600) * |L| := by
  have hc10_nn : 0 ≤ 134211265 * h / 479001600 := by positivity
  have hc9_nn : 0 ≤ 656185652 * h / 479001600 := by positivity
  have hc8_nn : 0 ≤ 890175549 * h / 479001600 := by positivity
  have hc7_nn : 0 ≤ 1446205080 * h / 479001600 := by positivity
  have hc6_nn : 0 ≤ 1823311566 * h / 479001600 := by positivity
  have hc5_nn : 0 ≤ 1710774528 * h / 479001600 := by positivity
  have hc4_nn : 0 ≤ 1170597042 * h / 479001600 := by positivity
  have hc3_nn : 0 ≤ 567450984 * h / 479001600 := by positivity
  have hc2_nn : 0 ≤ 184776195 * h / 479001600 := by positivity
  have hc1_nn : 0 ≤ 36284876 * h / 479001600 := by positivity
  have haux (A B sC sD sE sF sG sH sI sJ sK sL : ℝ) :
      |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL|
        ≤ |A| + |B| + |sC| + |sD| + |sE| + |sF| + |sG| + |sH|
            + |sI| + |sJ| + |sK| + |sL| := by
    have h1 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL|
        ≤ |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK| + |sL| :=
      abs_sub _ _
    have h2 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK|
        ≤ |A - B - sC - sD + sE - sF + sG - sH + sI - sJ| + |sK| :=
      abs_add_le _ _
    have h3 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ|
        ≤ |A - B - sC - sD + sE - sF + sG - sH + sI| + |sJ| :=
      abs_sub _ _
    have h4 : |A - B - sC - sD + sE - sF + sG - sH + sI|
        ≤ |A - B - sC - sD + sE - sF + sG - sH| + |sI| :=
      abs_add_le _ _
    have h5 : |A - B - sC - sD + sE - sF + sG - sH|
        ≤ |A - B - sC - sD + sE - sF + sG| + |sH| :=
      abs_sub _ _
    have h6 : |A - B - sC - sD + sE - sF + sG|
        ≤ |A - B - sC - sD + sE - sF| + |sG| :=
      abs_add_le _ _
    have h7 : |A - B - sC - sD + sE - sF|
        ≤ |A - B - sC - sD + sE| + |sF| :=
      abs_sub _ _
    have h8 : |A - B - sC - sD + sE|
        ≤ |A - B - sC - sD| + |sE| :=
      abs_add_le _ _
    have h9 : |A - B - sC - sD| ≤ |A - B - sC| + |sD| := abs_sub _ _
    have h10 : |A - B - sC| ≤ |A - B| + |sC| := abs_sub _ _
    have h11 : |A - B| ≤ |A| + |B| := abs_sub _ _
    linarith
  have habsC : |(134211265 * h / 479001600) * C|
      = (134211265 * h / 479001600) * |C| := by
    rw [abs_mul, abs_of_nonneg hc10_nn]
  have habsD : |(656185652 * h / 479001600) * D|
      = (656185652 * h / 479001600) * |D| := by
    rw [abs_mul, abs_of_nonneg hc9_nn]
  have habsE : |(890175549 * h / 479001600) * E|
      = (890175549 * h / 479001600) * |E| := by
    rw [abs_mul, abs_of_nonneg hc8_nn]
  have habsF : |(1446205080 * h / 479001600) * F|
      = (1446205080 * h / 479001600) * |F| := by
    rw [abs_mul, abs_of_nonneg hc7_nn]
  have habsG : |(1823311566 * h / 479001600) * G|
      = (1823311566 * h / 479001600) * |G| := by
    rw [abs_mul, abs_of_nonneg hc6_nn]
  have habsH : |(1710774528 * h / 479001600) * H|
      = (1710774528 * h / 479001600) * |H| := by
    rw [abs_mul, abs_of_nonneg hc5_nn]
  have habsI : |(1170597042 * h / 479001600) * I|
      = (1170597042 * h / 479001600) * |I| := by
    rw [abs_mul, abs_of_nonneg hc4_nn]
  have habsJ : |(567450984 * h / 479001600) * J|
      = (567450984 * h / 479001600) * |J| := by
    rw [abs_mul, abs_of_nonneg hc3_nn]
  have habsK : |(184776195 * h / 479001600) * K|
      = (184776195 * h / 479001600) * |K| := by
    rw [abs_mul, abs_of_nonneg hc2_nn]
  have habsL : |(36284876 * h / 479001600) * L|
      = (36284876 * h / 479001600) * |L| := by
    rw [abs_mul, abs_of_nonneg hc1_nn]
  have htri := haux A B
    ((134211265 * h / 479001600) * C)
    ((656185652 * h / 479001600) * D)
    ((890175549 * h / 479001600) * E)
    ((1446205080 * h / 479001600) * F)
    ((1823311566 * h / 479001600) * G)
    ((1710774528 * h / 479001600) * H)
    ((1170597042 * h / 479001600) * I)
    ((567450984 * h / 479001600) * J)
    ((184776195 * h / 479001600) * K)
    ((36284876 * h / 479001600) * L)
  rw [habsC, habsD, habsE, habsF, habsG, habsH, habsI, habsJ, habsK, habsL] at htri
  exact htri

private lemma am10_residual_combine
    {M h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D E F G H I J K L : ℝ)
    (htri : |A - B - (134211265 * h / 479001600) * C - (656185652 * h / 479001600) * D + (890175549 * h / 479001600) * E - (1446205080 * h / 479001600) * F + (1823311566 * h / 479001600) * G - (1710774528 * h / 479001600) * H + (1170597042 * h / 479001600) * I - (567450984 * h / 479001600) * J + (184776195 * h / 479001600) * K - (36284876 * h / 479001600) * L| ≤ |A| + |B| + (134211265 * h / 479001600) * |C| + (656185652 * h / 479001600) * |D| + (890175549 * h / 479001600) * |E| + (1446205080 * h / 479001600) * |F| + (1823311566 * h / 479001600) * |G| + (1710774528 * h / 479001600) * |H| + (1170597042 * h / 479001600) * |I| + (567450984 * h / 479001600) * |J| + (184776195 * h / 479001600) * |K| + (36284876 * h / 479001600) * |L|)
    (hA_bd : |A| ≤ M / 479001600 * (10 * h) ^ 12)
    (hB_bd : |B| ≤ M / 479001600 * (9 * h) ^ 12)
    (hC_bd : |C| ≤ M / 39916800 * (10 * h) ^ 11)
    (hD_bd : |D| ≤ M / 39916800 * (9 * h) ^ 11)
    (hE_bd : |E| ≤ M / 39916800 * (8 * h) ^ 11)
    (hF_bd : |F| ≤ M / 39916800 * (7 * h) ^ 11)
    (hG_bd : |G| ≤ M / 39916800 * (6 * h) ^ 11)
    (hH_bd : |H| ≤ M / 39916800 * (5 * h) ^ 11)
    (hI_bd : |I| ≤ M / 39916800 * (4 * h) ^ 11)
    (hJ_bd : |J| ≤ M / 39916800 * (3 * h) ^ 11)
    (hK_bd : |K| ≤ M / 39916800 * (2 * h) ^ 11)
    (hL_bd : |L| ≤ M / 39916800 * h ^ 11) :
    |A - B - (134211265 * h / 479001600) * C - (656185652 * h / 479001600) * D + (890175549 * h / 479001600) * E - (1446205080 * h / 479001600) * F + (1823311566 * h / 479001600) * G - (1710774528 * h / 479001600) * H + (1170597042 * h / 479001600) * I - (567450984 * h / 479001600) * J + (184776195 * h / 479001600) * K - (36284876 * h / 479001600) * L| ≤ (5045 : ℝ) * M * h ^ 12 := by
  have hc10_nn : 0 ≤ 134211265 * h / 479001600 := by positivity
  have hc9_nn : 0 ≤ 656185652 * h / 479001600 := by positivity
  have hc8_nn : 0 ≤ 890175549 * h / 479001600 := by positivity
  have hc7_nn : 0 ≤ 1446205080 * h / 479001600 := by positivity
  have hc6_nn : 0 ≤ 1823311566 * h / 479001600 := by positivity
  have hc5_nn : 0 ≤ 1710774528 * h / 479001600 := by positivity
  have hc4_nn : 0 ≤ 1170597042 * h / 479001600 := by positivity
  have hc3_nn : 0 ≤ 567450984 * h / 479001600 := by positivity
  have hc2_nn : 0 ≤ 184776195 * h / 479001600 := by positivity
  have hc1_nn : 0 ≤ 36284876 * h / 479001600 := by positivity
  have hCbd_s : (134211265 * h / 479001600) * |C|
      ≤ (134211265 * h / 479001600) * (M / 39916800 * (10 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hC_bd hc10_nn
  have hDbd_s : (656185652 * h / 479001600) * |D|
      ≤ (656185652 * h / 479001600) * (M / 39916800 * (9 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hD_bd hc9_nn
  have hEbd_s : (890175549 * h / 479001600) * |E|
      ≤ (890175549 * h / 479001600) * (M / 39916800 * (8 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hE_bd hc8_nn
  have hFbd_s : (1446205080 * h / 479001600) * |F|
      ≤ (1446205080 * h / 479001600) * (M / 39916800 * (7 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hF_bd hc7_nn
  have hGbd_s : (1823311566 * h / 479001600) * |G|
      ≤ (1823311566 * h / 479001600) * (M / 39916800 * (6 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hG_bd hc6_nn
  have hHbd_s : (1710774528 * h / 479001600) * |H|
      ≤ (1710774528 * h / 479001600) * (M / 39916800 * (5 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hH_bd hc5_nn
  have hIbd_s : (1170597042 * h / 479001600) * |I|
      ≤ (1170597042 * h / 479001600) * (M / 39916800 * (4 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hI_bd hc4_nn
  have hJbd_s : (567450984 * h / 479001600) * |J|
      ≤ (567450984 * h / 479001600) * (M / 39916800 * (3 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hJ_bd hc3_nn
  have hKbd_s : (184776195 * h / 479001600) * |K|
      ≤ (184776195 * h / 479001600) * (M / 39916800 * (2 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hK_bd hc2_nn
  have hLbd_s : (36284876 * h / 479001600) * |L|
      ≤ (36284876 * h / 479001600) * (M / 39916800 * h ^ 11) :=
    mul_le_mul_of_nonneg_left hL_bd hc1_nn
  have hbound_alg := am10_residual_bound_alg_identity M h
  have hh12_nn : 0 ≤ h ^ 12 := by positivity
  have hMh12_nn : 0 ≤ M * h ^ 12 := mul_nonneg hMnn hh12_nn
  have hslack : (251196920117213671 / 49792216320000 : ℝ) * M * h ^ 12
      ≤ 5045 * M * h ^ 12 := by
    rw [mul_assoc, mul_assoc (5045 : ℝ)]
    have hle : (251196920117213671 / 49792216320000 : ℝ) ≤ 5045 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh12_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hEbd_s,
    hFbd_s, hGbd_s, hHbd_s, hIbd_s, hJbd_s, hKbd_s, hLbd_s]

/-- Pointwise AM10 truncation residual bound. -/
theorem am10_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 12 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 12 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (ht8h : t + 8 * h ∈ Set.Icc a b)
    (ht9h : t + 9 * h ∈ Set.Icc a b)
    (ht10h : t + 10 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 10 * h) - y (t + 9 * h)
        - h * ((134211265 / 479001600) * deriv y (t + 10 * h)
              + (656185652 / 479001600) * deriv y (t + 9 * h)
              - (890175549 / 479001600) * deriv y (t + 8 * h)
              + (1446205080 / 479001600) * deriv y (t + 7 * h)
              - (1823311566 / 479001600) * deriv y (t + 6 * h)
              + (1710774528 / 479001600) * deriv y (t + 5 * h)
              - (1170597042 / 479001600) * deriv y (t + 4 * h)
              + (567450984 / 479001600) * deriv y (t + 3 * h)
              - (184776195 / 479001600) * deriv y (t + 2 * h)
              + (36284876 / 479001600) * deriv y (t + h)
              - (3250433 / 479001600) * deriv y t)|
      ≤ (5045 : ℝ) * M * h ^ 12 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have h9h : 0 ≤ 9 * h := by linarith
  have h10h : 0 ≤ 10 * h := by linarith
  have hRy9 :=
    y_twelfth_order_taylor_remainder hy hbnd ht ht9h h9h
  have hRy10 :=
    y_twelfth_order_taylor_remainder hy hbnd ht ht10h h10h
  have hRyp1 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht ht9h h9h
  have hRyp10 :=
    derivY_eleventh_order_taylor_remainder hy hbnd ht ht10h h10h
  set y0 := y t with hy0_def
  set y9 := y (t + 9 * h) with hy9_def
  set y10 := y (t + 10 * h) with hy10_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set d6 := deriv y (t + 6 * h) with hd6_def
  set d7 := deriv y (t + 7 * h) with hd7_def
  set d8 := deriv y (t + 8 * h) with hd8_def
  set d9 := deriv y (t + 9 * h) with hd9_def
  set d10 := deriv y (t + 10 * h) with hd10_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd := iteratedDeriv 8 y t with hdddddddd_def
  set ddddddddd := iteratedDeriv 9 y t with hddddddddd_def
  set dddddddddd := iteratedDeriv 10 y t with hdddddddddd_def
  set ddddddddddd := iteratedDeriv 11 y t with hddddddddddd_def
  have hLTE_eq :=
    am10_residual_alg_identity y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
      dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd dddddddddd
      ddddddddddd h
  rw [hLTE_eq]
  set R0 := y10 - y0 - (10 * h) * d0
            - (10 * h) ^ 2 / 2 * dd
            - (10 * h) ^ 3 / 6 * ddd
            - (10 * h) ^ 4 / 24 * dddd
            - (10 * h) ^ 5 / 120 * ddddd
            - (10 * h) ^ 6 / 720 * dddddd
            - (10 * h) ^ 7 / 5040 * ddddddd
            - (10 * h) ^ 8 / 40320 * dddddddd
            - (10 * h) ^ 9 / 362880 * ddddddddd
            - (10 * h) ^ 10 / 3628800 * dddddddddd
            - (10 * h) ^ 11 / 39916800 * ddddddddddd with hR0_def
  set R1 := y9 - y0 - (9 * h) * d0
            - (9 * h) ^ 2 / 2 * dd
            - (9 * h) ^ 3 / 6 * ddd
            - (9 * h) ^ 4 / 24 * dddd
            - (9 * h) ^ 5 / 120 * ddddd
            - (9 * h) ^ 6 / 720 * dddddd
            - (9 * h) ^ 7 / 5040 * ddddddd
            - (9 * h) ^ 8 / 40320 * dddddddd
            - (9 * h) ^ 9 / 362880 * ddddddddd
            - (9 * h) ^ 10 / 3628800 * dddddddddd
            - (9 * h) ^ 11 / 39916800 * ddddddddddd with hR1_def
  set R2 := d10 - d0 - (10 * h) * dd
                - (10 * h) ^ 2 / 2 * ddd
                - (10 * h) ^ 3 / 6 * dddd
                - (10 * h) ^ 4 / 24 * ddddd
                - (10 * h) ^ 5 / 120 * dddddd
                - (10 * h) ^ 6 / 720 * ddddddd
                - (10 * h) ^ 7 / 5040 * dddddddd
                - (10 * h) ^ 8 / 40320 * ddddddddd
                - (10 * h) ^ 9 / 362880 * dddddddddd
                - (10 * h) ^ 10 / 3628800 * ddddddddddd with hR2_def
  set R3 := d9 - d0 - (9 * h) * dd
                - (9 * h) ^ 2 / 2 * ddd
                - (9 * h) ^ 3 / 6 * dddd
                - (9 * h) ^ 4 / 24 * ddddd
                - (9 * h) ^ 5 / 120 * dddddd
                - (9 * h) ^ 6 / 720 * ddddddd
                - (9 * h) ^ 7 / 5040 * dddddddd
                - (9 * h) ^ 8 / 40320 * ddddddddd
                - (9 * h) ^ 9 / 362880 * dddddddddd
                - (9 * h) ^ 10 / 3628800 * ddddddddddd with hR3_def
  set R4 := d8 - d0 - (8 * h) * dd
                - (8 * h) ^ 2 / 2 * ddd
                - (8 * h) ^ 3 / 6 * dddd
                - (8 * h) ^ 4 / 24 * ddddd
                - (8 * h) ^ 5 / 120 * dddddd
                - (8 * h) ^ 6 / 720 * ddddddd
                - (8 * h) ^ 7 / 5040 * dddddddd
                - (8 * h) ^ 8 / 40320 * ddddddddd
                - (8 * h) ^ 9 / 362880 * dddddddddd
                - (8 * h) ^ 10 / 3628800 * ddddddddddd with hR4_def
  set R5 := d7 - d0 - (7 * h) * dd
                - (7 * h) ^ 2 / 2 * ddd
                - (7 * h) ^ 3 / 6 * dddd
                - (7 * h) ^ 4 / 24 * ddddd
                - (7 * h) ^ 5 / 120 * dddddd
                - (7 * h) ^ 6 / 720 * ddddddd
                - (7 * h) ^ 7 / 5040 * dddddddd
                - (7 * h) ^ 8 / 40320 * ddddddddd
                - (7 * h) ^ 9 / 362880 * dddddddddd
                - (7 * h) ^ 10 / 3628800 * ddddddddddd with hR5_def
  set R6 := d6 - d0 - (6 * h) * dd
                - (6 * h) ^ 2 / 2 * ddd
                - (6 * h) ^ 3 / 6 * dddd
                - (6 * h) ^ 4 / 24 * ddddd
                - (6 * h) ^ 5 / 120 * dddddd
                - (6 * h) ^ 6 / 720 * ddddddd
                - (6 * h) ^ 7 / 5040 * dddddddd
                - (6 * h) ^ 8 / 40320 * ddddddddd
                - (6 * h) ^ 9 / 362880 * dddddddddd
                - (6 * h) ^ 10 / 3628800 * ddddddddddd with hR6_def
  set R7 := d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd
                - (5 * h) ^ 6 / 720 * ddddddd
                - (5 * h) ^ 7 / 5040 * dddddddd
                - (5 * h) ^ 8 / 40320 * ddddddddd
                - (5 * h) ^ 9 / 362880 * dddddddddd
                - (5 * h) ^ 10 / 3628800 * ddddddddddd with hR7_def
  set R8 := d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd
                - (4 * h) ^ 6 / 720 * ddddddd
                - (4 * h) ^ 7 / 5040 * dddddddd
                - (4 * h) ^ 8 / 40320 * ddddddddd
                - (4 * h) ^ 9 / 362880 * dddddddddd
                - (4 * h) ^ 10 / 3628800 * ddddddddddd with hR8_def
  set R9 := d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd
                - (3 * h) ^ 6 / 720 * ddddddd
                - (3 * h) ^ 7 / 5040 * dddddddd
                - (3 * h) ^ 8 / 40320 * ddddddddd
                - (3 * h) ^ 9 / 362880 * dddddddddd
                - (3 * h) ^ 10 / 3628800 * ddddddddddd with hR9_def
  set R10 := d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd
                - (2 * h) ^ 6 / 720 * ddddddd
                - (2 * h) ^ 7 / 5040 * dddddddd
                - (2 * h) ^ 8 / 40320 * ddddddddd
                - (2 * h) ^ 9 / 362880 * dddddddddd
                - (2 * h) ^ 10 / 3628800 * ddddddddddd with hR10_def
  set R11 := d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd
                - h ^ 6 / 720 * ddddddd
                - h ^ 7 / 5040 * dddddddd
                - h ^ 8 / 40320 * ddddddddd
                - h ^ 9 / 362880 * dddddddddd
                - h ^ 10 / 3628800 * ddddddddddd with hR11_def
  clear_value R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11
  have htri := am10_residual_twelve_term_triangle
    R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 h hh
  have hR0_bd : |R0| ≤ M / 479001600 * (10 * h) ^ 12 := hRy10
  have hR1_bd : |R1| ≤ M / 479001600 * (9 * h) ^ 12 := hRy9
  have hR2_bd : |R2| ≤ M / 39916800 * (10 * h) ^ 11 := hRyp10
  have hR3_bd : |R3| ≤ M / 39916800 * (9 * h) ^ 11 := hRyp9
  have hR4_bd : |R4| ≤ M / 39916800 * (8 * h) ^ 11 := hRyp8
  have hR5_bd : |R5| ≤ M / 39916800 * (7 * h) ^ 11 := hRyp7
  have hR6_bd : |R6| ≤ M / 39916800 * (6 * h) ^ 11 := hRyp6
  have hR7_bd : |R7| ≤ M / 39916800 * (5 * h) ^ 11 := hRyp5
  have hR8_bd : |R8| ≤ M / 39916800 * (4 * h) ^ 11 := hRyp4
  have hR9_bd : |R9| ≤ M / 39916800 * (3 * h) ^ 11 := hRyp3
  have hR10_bd : |R10| ≤ M / 39916800 * (2 * h) ^ 11 := hRyp2
  have hR11_bd : |R11| ≤ M / 39916800 * h ^ 11 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact am10_residual_combine hh hMnn R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11
    htri hR0_bd hR1_bd hR2_bd hR3_bd hR4_bd hR5_bd hR6_bd hR7_bd hR8_bd
    hR9_bd hR10_bd hR11_bd

/-- Uniform bound on the AM10 one-step truncation residual on a finite
horizon, given a `C^12` exact solution. -/
theorem am10_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 12 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 10) * h ≤ T →
        |adamsMoulton10.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 12 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_twelve_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(5045 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 10) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 9 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht10h_mem : t + 10 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 10 * h = ((n : ℝ) + 10) * h := by ring
    linarith
  have hpoint :=
    am10_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem
      ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem ht10h_mem hh.le
  rw [am10_localTruncationError_eq]
  have hres_eq :
      am10Residual h t y =
        y (t + 10 * h) - y (t + 9 * h)
          - h * ((134211265 / 479001600) * deriv y (t + 10 * h)
                + (656185652 / 479001600) * deriv y (t + 9 * h)
                - (890175549 / 479001600) * deriv y (t + 8 * h)
                + (1446205080 / 479001600) * deriv y (t + 7 * h)
                - (1823311566 / 479001600) * deriv y (t + 6 * h)
                + (1710774528 / 479001600) * deriv y (t + 5 * h)
                - (1170597042 / 479001600) * deriv y (t + 4 * h)
                + (567450984 / 479001600) * deriv y (t + 3 * h)
                - (184776195 / 479001600) * deriv y (t + 2 * h)
                + (36284876 / 479001600) * deriv y (t + h)
                - (3250433 / 479001600) * deriv y t) := by
    unfold am10Residual
    simp [am10Coeff, Fin.sum_univ_succ]
    ring_nf
    simp
  rw [hres_eq]
  exact hpoint

/-- Headline AM10 global error bound. -/
theorem am10_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 12 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (134211265 / 479001600 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsAM10Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      |yseq 2 - y (t₀ + 2 * h)| ≤ ε₀ →
      |yseq 3 - y (t₀ + 3 * h)| ≤ ε₀ →
      |yseq 4 - y (t₀ + 4 * h)| ≤ ε₀ →
      |yseq 5 - y (t₀ + 5 * h)| ≤ ε₀ →
      |yseq 6 - y (t₀ + 6 * h)| ≤ ε₀ →
      |yseq 7 - y (t₀ + 7 * h)| ≤ ε₀ →
      |yseq 8 - y (t₀ + 8 * h)| ≤ ε₀ →
      |yseq 9 - y (t₀ + 9 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 9) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((37 * L) * T) * ε₀ + K * h ^ 10 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am10_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((37 * L) * T) * (2 * C), min δ 1, ?_,
    lt_min hδ_pos (by norm_num), ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδg_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd N hNh
  have hδ_le : h ≤ δ := le_trans hδg_le (min_le_left δ 1)
  have h_le_one : h ≤ 1 := le_trans hδg_le (min_le_right δ 1)
  set EN : ℕ → ℝ := fun k => am10ErrWindow h t₀ yseq y k with hEN_def
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k => by
    simpa [hEN_def] using am10ErrWindow_nonneg h t₀ yseq y k
  have hEN0_le : EN 0 ≤ ε₀ := by
    unfold EN
    unfold am10ErrWindow
    apply Finset.sup'_le
    intro j _
    fin_cases j
    · simpa [am10Err] using he0_bd
    · simpa [am10Err] using he1_bd
    · simpa [am10Err] using he2_bd
    · simpa [am10Err] using he3_bd
    · simpa [am10Err] using he4_bd
    · simpa [am10Err] using he5_bd
    · simpa [am10Err] using he6_bd
    · simpa [am10Err] using he7_bd
    · simpa [am10Err] using he8_bd
    · simpa [am10Err] using he9_bd
  have h37L_nn : (0 : ℝ) ≤ 37 * L := by linarith
  have hh11_le_hh10 : h ^ 12 ≤ h ^ 11 := by
    calc
      h ^ 12 = h ^ 11 * h := by ring
      _ ≤ h ^ 11 * 1 :=
        mul_le_mul_of_nonneg_left h_le_one (by positivity)
      _ = h ^ 11 := by ring
  have hstep_general : ∀ n : ℕ, n < N →
      EN (n + 1) ≤ (1 + h * (37 * L)) * EN n + (2 * C) * h ^ 11 := by
    intro n hn_lt
    have hres_arg : ((n : ℝ) + 10) * h ≤ T := by
      have hnat : n + 10 ≤ N + 9 := by omega
      have hreal : (n : ℝ) + 10 ≤ (N : ℝ) + 9 := by
        exact_mod_cast hnat
      have hle : ((n : ℝ) + 10) * h ≤ ((N : ℝ) + 9) * h :=
        mul_le_mul_of_nonneg_right hreal hh.le
      exact le_trans hle hNh
    have honestep :=
      am10_one_step_error_pair_bound (h := h) (L := L) hh.le hL hsmall
        hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hres_arg
    have h2τ : 2 * |adamsMoulton10.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (2 * C) * h ^ 11 := by
      have h2res : 2 * |adamsMoulton10.localTruncationError h
          (t₀ + (n : ℝ) * h) y| ≤ 2 * (C * h ^ 12) :=
        mul_le_mul_of_nonneg_left hres (by norm_num)
      have hweak : 2 * (C * h ^ 12) ≤ (2 * C) * h ^ 11 := by
        have hC2_nn : 0 ≤ 2 * C := by positivity
        have := mul_le_mul_of_nonneg_left hh11_le_hh10 hC2_nn
        linarith
      exact le_trans h2res hweak
    show EN (n + 1) ≤ (1 + h * (37 * L)) * EN n + (2 * C) * h ^ 11
    simpa [hEN_def] using le_trans honestep (by linarith)
  have hNh_base : (N : ℝ) * h ≤ T := by
    have hle : (N : ℝ) * h ≤ ((N : ℝ) + 9) * h :=
      mul_le_mul_of_nonneg_right (by linarith) hh.le
    exact le_trans hle hNh
  have hgronwall :=
    lmm_error_bound_from_local_truncation
      (h := h) (L := 37 * L) (C := 2 * C) (T := T) (p := 10) (e := EN)
      (N := N) hh.le h37L_nn (by positivity) (hEN_nn 0) hstep_general
      N le_rfl hNh_base
  have hexp_nn : 0 ≤ Real.exp ((37 * L) * T) := Real.exp_nonneg _
  have hstart_chain :
      Real.exp ((37 * L) * T) * EN 0
        ≤ Real.exp ((37 * L) * T) * ε₀ :=
    mul_le_mul_of_nonneg_left hEN0_le hexp_nn
  have hEN_bound :
      EN N ≤ Real.exp ((37 * L) * T) * ε₀
        + T * Real.exp ((37 * L) * T) * (2 * C) * h ^ 10 := by
    linarith
  have hpoint_le_window : am10Err h t₀ yseq y N ≤ EN N := by
    show am10Err h t₀ yseq y N ≤ am10ErrWindow h t₀ yseq y N
    unfold am10ErrWindow
    have hsup := Finset.le_sup' (b := (0 : Fin 10))
      (f := fun j : Fin 10 => am10Err h t₀ yseq y (N + (j : ℕ)))
      (Finset.mem_univ _)
    simpa using hsup
  calc
    |yseq N - y (t₀ + (N : ℝ) * h)|
        = am10Err h t₀ yseq y N := rfl
    _ ≤ EN N := hpoint_le_window
    _ ≤ Real.exp ((37 * L) * T) * ε₀
        + T * Real.exp ((37 * L) * T) * (2 * C) * h ^ 10 := hEN_bound

end LMM
