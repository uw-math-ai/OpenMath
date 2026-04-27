import OpenMath.LMMTruncationOp
import OpenMath.LMMAB12Convergence
import OpenMath.AdamsMethods

/-! ## Adams--Moulton 11-step Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit Adams--Moulton
11-step method.  This extends the AM11 scalar ladder using the public
thirteenth-order Taylor helpers from `OpenMath.LMMAB12Convergence`.

The AM11 coefficients are obtained by integrating the Lagrange basis on
nodes 0,...,11 over `[10, 11]`; over the common denominator `958003200` they
are `[5675265, -68928781, 384709327, -1305971115, 3007739418,
-4963166514, 6043521486, -5519460582, 3828828885, -2092490673,
1374799219, 262747265]`, summing to `958003200`.

The absolute-weight sum is `2885803853/95800320`.  With the standard
implicit smallness assumption `β₁₁ h L ≤ 1/2`, division by the implicit
new-point factor requires the growth slack `61L`.  The exact thirteenth-order
residual coefficient is approximately `14002.02`, slackened to `14003`. -/

namespace LMM

/-- AM11 coefficients as a compact reusable finite vector. -/
noncomputable def am11Coeff : Fin 12 → ℝ :=
  ![5675265/958003200, -68928781/958003200,
    384709327/958003200, -1305971115/958003200,
    3007739418/958003200, -4963166514/958003200,
    6043521486/958003200, -5519460582/958003200,
    3828828885/958003200, -2092490673/958003200,
    1374799219/958003200, 262747265/958003200]

/-- The eleven already-known AM11 coefficients, excluding the implicit new point. -/
noncomputable def am11ExplicitCoeff (j : Fin 11) : ℝ :=
  am11Coeff ⟨j, by omega⟩

/-- Textbook AM11 residual at base point `t`. -/
noncomputable def am11Residual (h t : ℝ) (y : ℝ → ℝ) : ℝ :=
  y (t + 11 * h) - y (t + 10 * h)
    - h * ∑ j : Fin 12, am11Coeff j * deriv y (t + (j : ℕ) * h)

/-- AM11 trajectory predicate:
`y_{n+10} = y_{n+9} + h * sum_j beta_j f(t_n + jh, y_{n+j})`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM11Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 11)
      = y (n + 10)
        + h * ∑ j : Fin 12,
            am11Coeff j * f (t₀ + (n : ℝ) * h + (j : ℕ) * h)
              (y (n + (j : ℕ)))

/-- Scalar pointwise error at an index. -/
noncomputable def am11Err (h t₀ : ℝ) (yseq : ℕ → ℝ) (y : ℝ → ℝ)
    (k : ℕ) : ℝ :=
  |yseq k - y (t₀ + (k : ℝ) * h)|

/-- Rolling AM11 eleven-sample window max. -/
noncomputable def am11ErrWindow (h t₀ : ℝ) (yseq : ℕ → ℝ) (y : ℝ → ℝ)
    (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin 11 => am11Err h t₀ yseq y (k + (j : ℕ)))

lemma am11ErrWindow_nonneg (h t₀ : ℝ) (yseq : ℕ → ℝ) (y : ℝ → ℝ)
    (k : ℕ) : 0 ≤ am11ErrWindow h t₀ yseq y k := by
  unfold am11ErrWindow
  exact (abs_nonneg _).trans
    (Finset.le_sup' (b := (0 : Fin 11))
      (f := fun j : Fin 11 => am11Err h t₀ yseq y (k + (j : ℕ)))
      (Finset.mem_univ _))

/-- AM11 local truncation operator reduces to the textbook residual. -/
theorem am11_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsMoulton11.localTruncationError h t y = am11Residual h t y := by
  unfold localTruncationError truncationOp am11Residual
  simp [adamsMoulton11, am11Coeff, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  norm_num
  ring

/-- One-step AM11 Lipschitz inequality before dividing by the implicit
new-point factor. -/
theorem am11_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) (_hL : 0 ≤ L)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM11Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (262747265 / 958003200 : ℝ) * h * L)
        * am11Err h t₀ yseq y (n + 11)
      ≤ am11Err h t₀ yseq y (n + 10)
        + h * L * ∑ j : Fin 11,
            |am11ExplicitCoeff j| * am11Err h t₀ yseq y (n + (j : ℕ))
        + |adamsMoulton11.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  set τ : ℝ := adamsMoulton11.localTruncationError h t y with hτ_def
  set Sa : ℝ := ∑ j : Fin 12,
      am11Coeff j * f (t + (j : ℕ) * h) (yseq (n + (j : ℕ))) with hSa_def
  set Sy : ℝ := ∑ j : Fin 12,
      am11Coeff j * f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)) with hSy_def
  have hstep : yseq (n + 11) = yseq (n + 10) + h * Sa := by
    simpa [hSa_def, ht_def, add_assoc] using hy.recurrence n
  have hτ_alt : τ = y (t + 11 * h) - y (t + 10 * h) - h * Sy := by
    show adamsMoulton11.localTruncationError h t y = _
    rw [am11_localTruncationError_eq]
    unfold am11Residual
    have hcong :
        (fun j : Fin 12 => am11Coeff j * deriv y (t + (j : ℕ) * h))
          = (fun j : Fin 12 =>
              am11Coeff j * f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))) := by
      funext j
      rw [hyf]
    rw [hcong, hSy_def]
  set Sd : ℝ := ∑ j : Fin 12, am11Coeff j
      * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
        - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))) with hSd_def
  have hSa_sub_Sy : Sa - Sy = Sd := by
    rw [hSa_def, hSy_def, hSd_def, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have halg :
      yseq (n + 11) - y (t + 11 * h)
        = (yseq (n + 10) - y (t + 10 * h)) + h * Sd - τ := by
    rw [hstep, hτ_alt, ← hSa_sub_Sy]
    ring
  have hdiff_bound : ∀ j : Fin 12,
      |am11Coeff j
          * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))|
        ≤ |am11Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by
    intro j
    have hLip := hf (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
      (y (t + (j : ℕ) * h))
    rw [abs_mul]
    have hcoeff_nn : 0 ≤ |am11Coeff j| := abs_nonneg _
    calc
      |am11Coeff j| *
          |f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))|
          ≤ |am11Coeff j| *
              (L * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)|) :=
            mul_le_mul_of_nonneg_left hLip hcoeff_nn
      _ = |am11Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by ring
  have hSd_abs :
      |Sd| ≤ ∑ j : Fin 12, |am11Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by
    rw [hSd_def]
    calc
      |∑ j : Fin 12, am11Coeff j
          * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))|
          ≤ ∑ j : Fin 12,
              |am11Coeff j
                * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
                  - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 12, |am11Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| :=
            Finset.sum_le_sum (fun j _ => hdiff_bound j)
  have htri :
      |yseq (n + 11) - y (t + 11 * h)|
        ≤ |yseq (n + 10) - y (t + 10 * h)| + |h * Sd| + |τ| := by
    rw [halg]
    have h1 :
        |(yseq (n + 10) - y (t + 10 * h)) + h * Sd - τ|
          ≤ |(yseq (n + 10) - y (t + 10 * h)) + h * Sd| + |τ| :=
      abs_sub _ _
    have h2 :
        |(yseq (n + 10) - y (t + 10 * h)) + h * Sd|
          ≤ |yseq (n + 10) - y (t + 10 * h)| + |h * Sd| :=
      abs_add_le _ _
    linarith
  have h_hSd :
      |h * Sd| ≤ h * ∑ j : Fin 12, |am11Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by
    rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hSd_abs hh
  have hmain_local :
      |yseq (n + 11) - y (t + 11 * h)|
        ≤ |yseq (n + 10) - y (t + 10 * h)|
          + h * ∑ j : Fin 12, |am11Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)|
          + |τ| := by
    linarith
  have hsplit :
      h * ∑ j : Fin 12, |am11Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)|
        = h * L * ∑ j : Fin 11,
            |am11ExplicitCoeff j| * am11Err h t₀ yseq y (n + (j : ℕ))
          + (262747265 / 958003200 : ℝ) * h * L
              * am11Err h t₀ yseq y (n + 11) := by
    simp [am11Coeff, am11ExplicitCoeff, am11Err, Fin.sum_univ_succ, ht_def]
    ring_nf
  have hmain :
      am11Err h t₀ yseq y (n + 11)
        ≤ am11Err h t₀ yseq y (n + 10)
          + h * L * ∑ j : Fin 11,
            |am11ExplicitCoeff j| * am11Err h t₀ yseq y (n + (j : ℕ))
          + (262747265 / 958003200 : ℝ) * h * L
              * am11Err h t₀ yseq y (n + 11)
          + |adamsMoulton11.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
    have hmain_local' := hmain_local
    rw [hsplit] at hmain_local'
    simpa [am11Err, ht_def, Nat.cast_add, add_mul, add_assoc, add_left_comm,
      add_comm, hτ_def] using hmain_local'
  linarith [hmain]

/-- Divided AM11 one-step error bound at the new point. -/
theorem am11_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (262747265 / 958003200 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM11Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    am11Err h t₀ yseq y (n + 11)
      ≤ (1 + h * (61 * L)) * am11ErrWindow h t₀ yseq y n
        + 2 * |adamsMoulton11.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set E : ℝ := am11ErrWindow h t₀ yseq y n with hE_def
  set τabs : ℝ :=
    |adamsMoulton11.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hE_nn : 0 ≤ E := by
    simpa [hE_def] using am11ErrWindow_nonneg h t₀ yseq y n
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 479001600 / 262747265 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (262747265 / 958003200 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hwin : ∀ j : Fin 11,
      am11Err h t₀ yseq y (n + (j : ℕ)) ≤ E := by
    intro j
    show am11Err h t₀ yseq y (n + (j : ℕ))
        ≤ am11ErrWindow h t₀ yseq y n
    unfold am11ErrWindow
    exact Finset.le_sup' (b := j)
      (f := fun k : Fin 11 => am11Err h t₀ yseq y (n + (k : ℕ)))
      (Finset.mem_univ _)
  have he9_le_E : am11Err h t₀ yseq y (n + 10) ≤ E :=
    hwin ⟨10, by norm_num⟩
  have hsum_le :
      ∑ j : Fin 11, |am11ExplicitCoeff j| * am11Err h t₀ yseq y (n + (j : ℕ))
        ≤ (635450917 / 21288960 : ℝ) * E := by
    calc
      ∑ j : Fin 11, |am11ExplicitCoeff j| * am11Err h t₀ yseq y (n + (j : ℕ))
          ≤ ∑ j : Fin 11, |am11ExplicitCoeff j| * E :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (hwin j) (abs_nonneg _))
      _ = (635450917 / 21288960 : ℝ) * E := by
        simp [am11ExplicitCoeff, am11Coeff, Fin.sum_univ_succ]
        ring
  have hstep :=
    am11_one_step_lipschitz (h := h) (L := L) hh hL hf t₀ hy y hyf n
  have hR_le :
      am11Err h t₀ yseq y (n + 10)
        + h * L * ∑ j : Fin 11,
            |am11ExplicitCoeff j| * am11Err h t₀ yseq y (n + (j : ℕ))
        + τabs
        ≤ (1 + (635450917 / 21288960 : ℝ) * (h * L)) * E + τabs := by
    have hsum_scaled :
        h * L * ∑ j : Fin 11,
            |am11ExplicitCoeff j| * am11Err h t₀ yseq y (n + (j : ℕ))
          ≤ h * L * ((635450917 / 21288960 : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hsum_le hx_nn
    have h_alg :
        E + h * L * ((635450917 / 21288960 : ℝ) * E) + τabs
          = (1 + (635450917 / 21288960 : ℝ) * (h * L)) * E + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (635450917 / 21288960 : ℝ) * (h * L)
        ≤ (1 - (262747265 / 958003200 : ℝ) * h * L)
            * (1 + h * (61 * L)) := by
    have hxL_eq :
        (1 - (262747265 / 958003200 : ℝ) * h * L)
            * (1 + h * (61 * L))
          - (1 + (635450917 / 21288960 : ℝ) * (h * L))
          = (h * L) / 958003200 * (29580156670 - 16027583165 * (h * L)) := by
      ring
    have hpos : 0 ≤ 29580156670 - 16027583165 * (h * L) := by
      have hbound :
          16027583165 * (h * L)
            ≤ 16027583165 * (479001600 / 262747265 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hx_small (by norm_num)
      have hnum :
          (16027583165 : ℝ) * (479001600 / 262747265) ≤ 29580156670 := by
        norm_num
      exact sub_nonneg.mpr (le_trans hbound hnum)
    have hprod : 0 ≤ (h * L) / 958003200 * (29580156670 - 16027583165 * (h * L)) := by
      exact mul_nonneg (by positivity) hpos
    apply sub_nonneg.mp
    rw [hxL_eq]
    exact hprod
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (262747265 / 958003200 : ℝ) * h * L) * 2 := by
    set x : ℝ := (262747265 / 958003200 : ℝ) * h * L with hx_def
    change (1 : ℝ) ≤ (1 - x) * 2
    have hxle : x ≤ 1 / 2 := by simpa [hx_def] using hsmall
    nlinarith
  have hE_part :
      (1 + (635450917 / 21288960 : ℝ) * (h * L)) * E
        ≤ ((1 - (262747265 / 958003200 : ℝ) * h * L)
            * (1 + h * (61 * L))) * E :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (262747265 / 958003200 : ℝ) * h * L) * 2) * τabs := by
    have hraw := mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
    calc
      τabs = (1 : ℝ) * τabs := by ring
      _ ≤ ((1 - (262747265 / 958003200 : ℝ) * h * L) * 2) * τabs := hraw
  have hfactor :
      (1 + (635450917 / 21288960 : ℝ) * (h * L)) * E + τabs
        ≤ (1 - (262747265 / 958003200 : ℝ) * h * L)
            * ((1 + h * (61 * L)) * E + 2 * τabs) := by
    let A : ℝ := 1 - (262747265 / 958003200 : ℝ) * h * L
    let B : ℝ := 1 + h * (61 * L)
    let Cg : ℝ := 1 + (635450917 / 21288960 : ℝ) * (h * L)
    change Cg * E + τabs ≤ A * (B * E + 2 * τabs)
    have hE_part' : Cg * E ≤ (A * B) * E := hE_part
    have hτ_part' : τabs ≤ (A * 2) * τabs := hτ_part
    calc
      Cg * E + τabs ≤ (A * B) * E + (A * 2) * τabs :=
        add_le_add hE_part' hτ_part'
      _ = A * (B * E + 2 * τabs) := by ring
  have hprod :
      (1 - (262747265 / 958003200 : ℝ) * h * L)
          * am11Err h t₀ yseq y (n + 11)
        ≤ (1 - (262747265 / 958003200 : ℝ) * h * L)
            * ((1 + h * (61 * L)) * E + 2 * τabs) :=
    le_trans hstep (le_trans (by simpa [hτabs_def] using hR_le) hfactor)
  have hcancel :
      am11Err h t₀ yseq y (n + 11)
        ≤ (1 + h * (61 * L)) * E + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  simpa [hE_def, hτabs_def] using hcancel

/-- Max-norm AM11 one-step recurrence on the rolling 10-window. -/
theorem am11_one_step_error_pair_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (262747265 / 958003200 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM11Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    am11ErrWindow h t₀ yseq y (n + 1)
      ≤ (1 + h * (61 * L)) * am11ErrWindow h t₀ yseq y n
        + 2 * |adamsMoulton11.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set E : ℝ := am11ErrWindow h t₀ yseq y n with hE_def
  set τabs : ℝ :=
    |adamsMoulton11.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set R : ℝ := (1 + h * (61 * L)) * E + 2 * τabs with hR_def
  have hE_nn : 0 ≤ E := by
    simpa [hE_def] using am11ErrWindow_nonneg h t₀ yseq y n
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have h37hL_nn : 0 ≤ h * (61 * L) := by positivity
  have hE_le_R : E ≤ R := by
    have hcoef : (1 : ℝ) ≤ 1 + h * (61 * L) :=
      le_add_of_nonneg_right h37hL_nn
    have hgrow : E ≤ (1 + h * (61 * L)) * E := by
      have := mul_le_mul_of_nonneg_right hcoef hE_nn
      simpa using this
    have hplus :
        (1 + h * (61 * L)) * E ≤ R := by
      rw [hR_def]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hτ_nn)
    exact le_trans hgrow hplus
  have hwin : ∀ j : Fin 11,
      am11Err h t₀ yseq y (n + (j : ℕ)) ≤ E := by
    intro j
    show am11Err h t₀ yseq y (n + (j : ℕ))
        ≤ am11ErrWindow h t₀ yseq y n
    unfold am11ErrWindow
    exact Finset.le_sup' (b := j)
      (f := fun k : Fin 11 => am11Err h t₀ yseq y (n + (k : ℕ)))
      (Finset.mem_univ _)
  have hnew :
      am11Err h t₀ yseq y (n + 11) ≤ R := by
    simpa [hE_def, hτabs_def, hR_def] using
      (am11_one_step_error_bound (h := h) (L := L) hh hL hsmall hf t₀ hy y hyf n)
  have h_per : ∀ j : Fin 11,
      am11Err h t₀ yseq y (n + 1 + (j : ℕ)) ≤ R := by
    intro j
    by_cases hj : (j : ℕ) + 1 < 11
    · have hprev := hwin ⟨(j : ℕ) + 1, hj⟩
      have hidx : n + 1 + (j : ℕ) = n + ((j : ℕ) + 1) := by omega
      rw [hidx]
      exact le_trans hprev hE_le_R
    · have hjeq : (j : ℕ) = 10 := by omega
      have hidx : n + 1 + (j : ℕ) = n + 11 := by omega
      rw [hidx]
      exact hnew
  unfold am11ErrWindow
  exact Finset.sup'_le _ _ (fun j _ => by
    simpa [hE_def, hτabs_def, hR_def] using h_per j)

private lemma am11_residual_alg_identity
    (y0 y10 y11 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
      d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t h : ℝ)
    (A B C D E F G H I J K L M : ℝ)
    (hA : A = y11 - y0 - (11 * h) * d0
            - (11 * h) ^ 2 / 2 * d2t
            - (11 * h) ^ 3 / 6 * d3t
            - (11 * h) ^ 4 / 24 * d4t
            - (11 * h) ^ 5 / 120 * d5t
            - (11 * h) ^ 6 / 720 * d6t
            - (11 * h) ^ 7 / 5040 * d7t
            - (11 * h) ^ 8 / 40320 * d8t
            - (11 * h) ^ 9 / 362880 * d9t
            - (11 * h) ^ 10 / 3628800 * d10t
            - (11 * h) ^ 11 / 39916800 * d11t
            - (11 * h) ^ 12 / 479001600 * d12t)
    (hB : B = y10 - y0 - (10 * h) * d0
            - (10 * h) ^ 2 / 2 * d2t
            - (10 * h) ^ 3 / 6 * d3t
            - (10 * h) ^ 4 / 24 * d4t
            - (10 * h) ^ 5 / 120 * d5t
            - (10 * h) ^ 6 / 720 * d6t
            - (10 * h) ^ 7 / 5040 * d7t
            - (10 * h) ^ 8 / 40320 * d8t
            - (10 * h) ^ 9 / 362880 * d9t
            - (10 * h) ^ 10 / 3628800 * d10t
            - (10 * h) ^ 11 / 39916800 * d11t
            - (10 * h) ^ 12 / 479001600 * d12t)
    (hC : C = d11 - d0 - (11 * h) * d2t
                - (11 * h) ^ 2 / 2 * d3t
                - (11 * h) ^ 3 / 6 * d4t
                - (11 * h) ^ 4 / 24 * d5t
                - (11 * h) ^ 5 / 120 * d6t
                - (11 * h) ^ 6 / 720 * d7t
                - (11 * h) ^ 7 / 5040 * d8t
                - (11 * h) ^ 8 / 40320 * d9t
                - (11 * h) ^ 9 / 362880 * d10t
                - (11 * h) ^ 10 / 3628800 * d11t
                - (11 * h) ^ 11 / 39916800 * d12t)
    (hD : D = d10 - d0 - (10 * h) * d2t
                - (10 * h) ^ 2 / 2 * d3t
                - (10 * h) ^ 3 / 6 * d4t
                - (10 * h) ^ 4 / 24 * d5t
                - (10 * h) ^ 5 / 120 * d6t
                - (10 * h) ^ 6 / 720 * d7t
                - (10 * h) ^ 7 / 5040 * d8t
                - (10 * h) ^ 8 / 40320 * d9t
                - (10 * h) ^ 9 / 362880 * d10t
                - (10 * h) ^ 10 / 3628800 * d11t
                - (10 * h) ^ 11 / 39916800 * d12t)
    (hE : E = d9 - d0 - (9 * h) * d2t
                - (9 * h) ^ 2 / 2 * d3t
                - (9 * h) ^ 3 / 6 * d4t
                - (9 * h) ^ 4 / 24 * d5t
                - (9 * h) ^ 5 / 120 * d6t
                - (9 * h) ^ 6 / 720 * d7t
                - (9 * h) ^ 7 / 5040 * d8t
                - (9 * h) ^ 8 / 40320 * d9t
                - (9 * h) ^ 9 / 362880 * d10t
                - (9 * h) ^ 10 / 3628800 * d11t
                - (9 * h) ^ 11 / 39916800 * d12t)
    (hF : F = d8 - d0 - (8 * h) * d2t
                - (8 * h) ^ 2 / 2 * d3t
                - (8 * h) ^ 3 / 6 * d4t
                - (8 * h) ^ 4 / 24 * d5t
                - (8 * h) ^ 5 / 120 * d6t
                - (8 * h) ^ 6 / 720 * d7t
                - (8 * h) ^ 7 / 5040 * d8t
                - (8 * h) ^ 8 / 40320 * d9t
                - (8 * h) ^ 9 / 362880 * d10t
                - (8 * h) ^ 10 / 3628800 * d11t
                - (8 * h) ^ 11 / 39916800 * d12t)
    (hG : G = d7 - d0 - (7 * h) * d2t
                - (7 * h) ^ 2 / 2 * d3t
                - (7 * h) ^ 3 / 6 * d4t
                - (7 * h) ^ 4 / 24 * d5t
                - (7 * h) ^ 5 / 120 * d6t
                - (7 * h) ^ 6 / 720 * d7t
                - (7 * h) ^ 7 / 5040 * d8t
                - (7 * h) ^ 8 / 40320 * d9t
                - (7 * h) ^ 9 / 362880 * d10t
                - (7 * h) ^ 10 / 3628800 * d11t
                - (7 * h) ^ 11 / 39916800 * d12t)
    (hH : H = d6 - d0 - (6 * h) * d2t
                - (6 * h) ^ 2 / 2 * d3t
                - (6 * h) ^ 3 / 6 * d4t
                - (6 * h) ^ 4 / 24 * d5t
                - (6 * h) ^ 5 / 120 * d6t
                - (6 * h) ^ 6 / 720 * d7t
                - (6 * h) ^ 7 / 5040 * d8t
                - (6 * h) ^ 8 / 40320 * d9t
                - (6 * h) ^ 9 / 362880 * d10t
                - (6 * h) ^ 10 / 3628800 * d11t
                - (6 * h) ^ 11 / 39916800 * d12t)
    (hI : I = d5 - d0 - (5 * h) * d2t
                - (5 * h) ^ 2 / 2 * d3t
                - (5 * h) ^ 3 / 6 * d4t
                - (5 * h) ^ 4 / 24 * d5t
                - (5 * h) ^ 5 / 120 * d6t
                - (5 * h) ^ 6 / 720 * d7t
                - (5 * h) ^ 7 / 5040 * d8t
                - (5 * h) ^ 8 / 40320 * d9t
                - (5 * h) ^ 9 / 362880 * d10t
                - (5 * h) ^ 10 / 3628800 * d11t
                - (5 * h) ^ 11 / 39916800 * d12t)
    (hJ : J = d4 - d0 - (4 * h) * d2t
                - (4 * h) ^ 2 / 2 * d3t
                - (4 * h) ^ 3 / 6 * d4t
                - (4 * h) ^ 4 / 24 * d5t
                - (4 * h) ^ 5 / 120 * d6t
                - (4 * h) ^ 6 / 720 * d7t
                - (4 * h) ^ 7 / 5040 * d8t
                - (4 * h) ^ 8 / 40320 * d9t
                - (4 * h) ^ 9 / 362880 * d10t
                - (4 * h) ^ 10 / 3628800 * d11t
                - (4 * h) ^ 11 / 39916800 * d12t)
    (hK : K = d3 - d0 - (3 * h) * d2t
                - (3 * h) ^ 2 / 2 * d3t
                - (3 * h) ^ 3 / 6 * d4t
                - (3 * h) ^ 4 / 24 * d5t
                - (3 * h) ^ 5 / 120 * d6t
                - (3 * h) ^ 6 / 720 * d7t
                - (3 * h) ^ 7 / 5040 * d8t
                - (3 * h) ^ 8 / 40320 * d9t
                - (3 * h) ^ 9 / 362880 * d10t
                - (3 * h) ^ 10 / 3628800 * d11t
                - (3 * h) ^ 11 / 39916800 * d12t)
    (hL : L = d2 - d0 - (2 * h) * d2t
                - (2 * h) ^ 2 / 2 * d3t
                - (2 * h) ^ 3 / 6 * d4t
                - (2 * h) ^ 4 / 24 * d5t
                - (2 * h) ^ 5 / 120 * d6t
                - (2 * h) ^ 6 / 720 * d7t
                - (2 * h) ^ 7 / 5040 * d8t
                - (2 * h) ^ 8 / 40320 * d9t
                - (2 * h) ^ 9 / 362880 * d10t
                - (2 * h) ^ 10 / 3628800 * d11t
                - (2 * h) ^ 11 / 39916800 * d12t)
    (hM : M = d1 - d0 - h * d2t
                - h ^ 2 / 2 * d3t
                - h ^ 3 / 6 * d4t
                - h ^ 4 / 24 * d5t
                - h ^ 5 / 120 * d6t
                - h ^ 6 / 720 * d7t
                - h ^ 7 / 5040 * d8t
                - h ^ 8 / 40320 * d9t
                - h ^ 9 / 362880 * d10t
                - h ^ 10 / 3628800 * d11t
                - h ^ 11 / 39916800 * d12t) :
    y11 - y10 - h * ((262747265 / 958003200) * d11
                  + (1374799219 / 958003200) * d10
                  - (2092490673 / 958003200) * d9
                  + (3828828885 / 958003200) * d8
                  - (5519460582 / 958003200) * d7
                  + (6043521486 / 958003200) * d6
                  - (4963166514 / 958003200) * d5
                  + (3007739418 / 958003200) * d4
                  - (1305971115 / 958003200) * d3
                  + (384709327 / 958003200) * d2
                  - (68928781 / 958003200) * d1
                  + (5675265 / 958003200) * d0)
      = A - B
        - (262747265 * h / 958003200) * C
        - (1374799219 * h / 958003200) * D
        + (2092490673 * h / 958003200) * E
        - (3828828885 * h / 958003200) * F
        + (5519460582 * h / 958003200) * G
        - (6043521486 * h / 958003200) * H
        + (4963166514 * h / 958003200) * I
        - (3007739418 * h / 958003200) * J
        + (1305971115 * h / 958003200) * K
        - (384709327 * h / 958003200) * L
        + (68928781 * h / 958003200) * M := by
  subst hA; subst hB; subst hC; subst hD; subst hE; subst hF; subst hG; subst hH; subst hI; subst hJ; subst hK; subst hL; subst hM
  ring

private lemma am11_residual_bound_alg_identity (M h : ℝ) :
    M / 6227020800 * (11 * h) ^ 13
      + M / 6227020800 * (10 * h) ^ 13
      + (262747265 * h / 958003200) * (M / 479001600 * (11 * h) ^ 12)
      + (1374799219 * h / 958003200) * (M / 479001600 * (10 * h) ^ 12)
      + (2092490673 * h / 958003200) * (M / 479001600 * (9 * h) ^ 12)
      + (3828828885 * h / 958003200) * (M / 479001600 * (8 * h) ^ 12)
      + (5519460582 * h / 958003200) * (M / 479001600 * (7 * h) ^ 12)
      + (6043521486 * h / 958003200) * (M / 479001600 * (6 * h) ^ 12)
      + (4963166514 * h / 958003200) * (M / 479001600 * (5 * h) ^ 12)
      + (3007739418 * h / 958003200) * (M / 479001600 * (4 * h) ^ 12)
      + (1305971115 * h / 958003200) * (M / 479001600 * (3 * h) ^ 12)
      + (384709327 * h / 958003200) * (M / 479001600 * (2 * h) ^ 12)
      + (68928781 * h / 958003200) * (M / 479001600 * h ^ 12)
      = (345161607571042875013 / 24650850631680000 : ℝ) * M * h ^ 13 := by
  ring

private lemma am11_residual_triangle_aux
    (A B sC sD sE sF sG sH sI sJ sK sL sM : ℝ) :
    |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL + sM|
      ≤ |A| + |B| + |sC| + |sD| + |sE| + |sF| + |sG| + |sH|
          + |sI| + |sJ| + |sK| + |sL| + |sM| := by
  have h1 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL + sM|
      ≤ |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL| + |sM| := abs_add_le _ _
  have h2 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL|
      ≤ |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK| + |sL| := abs_sub _ _
  have h3 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK|
      ≤ |A - B - sC - sD + sE - sF + sG - sH + sI - sJ| + |sK| := abs_add_le _ _
  have h4 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ|
      ≤ |A - B - sC - sD + sE - sF + sG - sH + sI| + |sJ| := abs_sub _ _
  have h5 : |A - B - sC - sD + sE - sF + sG - sH + sI|
      ≤ |A - B - sC - sD + sE - sF + sG - sH| + |sI| := abs_add_le _ _
  have h6 : |A - B - sC - sD + sE - sF + sG - sH|
      ≤ |A - B - sC - sD + sE - sF + sG| + |sH| := abs_sub _ _
  have h7 : |A - B - sC - sD + sE - sF + sG|
      ≤ |A - B - sC - sD + sE - sF| + |sG| := abs_add_le _ _
  have h8 : |A - B - sC - sD + sE - sF|
      ≤ |A - B - sC - sD + sE| + |sF| := abs_sub _ _
  have h9 : |A - B - sC - sD + sE|
      ≤ |A - B - sC - sD| + |sE| := abs_add_le _ _
  have h10 : |A - B - sC - sD| ≤ |A - B - sC| + |sD| := abs_sub _ _
  have h11 : |A - B - sC| ≤ |A - B| + |sC| := abs_sub _ _
  have h12 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith

private lemma am11_residual_thirteen_term_triangle
    (A B C D E F G H I J K L M h : ℝ) (hh : 0 ≤ h) :
    |A - B - (262747265 * h / 958003200) * C - (1374799219 * h / 958003200) * D + (2092490673 * h / 958003200) * E - (3828828885 * h / 958003200) * F + (5519460582 * h / 958003200) * G - (6043521486 * h / 958003200) * H + (4963166514 * h / 958003200) * I - (3007739418 * h / 958003200) * J + (1305971115 * h / 958003200) * K - (384709327 * h / 958003200) * L + (68928781 * h / 958003200) * M| ≤ |A| + |B| + (262747265 * h / 958003200) * |C| + (1374799219 * h / 958003200) * |D| + (2092490673 * h / 958003200) * |E| + (3828828885 * h / 958003200) * |F| + (5519460582 * h / 958003200) * |G| + (6043521486 * h / 958003200) * |H| + (4963166514 * h / 958003200) * |I| + (3007739418 * h / 958003200) * |J| + (1305971115 * h / 958003200) * |K| + (384709327 * h / 958003200) * |L| + (68928781 * h / 958003200) * |M| := by
  have hcC_nn : 0 ≤ 262747265 * h / 958003200 := by positivity
  have hcD_nn : 0 ≤ 1374799219 * h / 958003200 := by positivity
  have hcE_nn : 0 ≤ 2092490673 * h / 958003200 := by positivity
  have hcF_nn : 0 ≤ 3828828885 * h / 958003200 := by positivity
  have hcG_nn : 0 ≤ 5519460582 * h / 958003200 := by positivity
  have hcH_nn : 0 ≤ 6043521486 * h / 958003200 := by positivity
  have hcI_nn : 0 ≤ 4963166514 * h / 958003200 := by positivity
  have hcJ_nn : 0 ≤ 3007739418 * h / 958003200 := by positivity
  have hcK_nn : 0 ≤ 1305971115 * h / 958003200 := by positivity
  have hcL_nn : 0 ≤ 384709327 * h / 958003200 := by positivity
  have hcM_nn : 0 ≤ 68928781 * h / 958003200 := by positivity
  have habsC : |(262747265 * h / 958003200) * C| = (262747265 * h / 958003200) * |C| := by
    rw [abs_mul, abs_of_nonneg hcC_nn]
  have habsD : |(1374799219 * h / 958003200) * D| = (1374799219 * h / 958003200) * |D| := by
    rw [abs_mul, abs_of_nonneg hcD_nn]
  have habsE : |(2092490673 * h / 958003200) * E| = (2092490673 * h / 958003200) * |E| := by
    rw [abs_mul, abs_of_nonneg hcE_nn]
  have habsF : |(3828828885 * h / 958003200) * F| = (3828828885 * h / 958003200) * |F| := by
    rw [abs_mul, abs_of_nonneg hcF_nn]
  have habsG : |(5519460582 * h / 958003200) * G| = (5519460582 * h / 958003200) * |G| := by
    rw [abs_mul, abs_of_nonneg hcG_nn]
  have habsH : |(6043521486 * h / 958003200) * H| = (6043521486 * h / 958003200) * |H| := by
    rw [abs_mul, abs_of_nonneg hcH_nn]
  have habsI : |(4963166514 * h / 958003200) * I| = (4963166514 * h / 958003200) * |I| := by
    rw [abs_mul, abs_of_nonneg hcI_nn]
  have habsJ : |(3007739418 * h / 958003200) * J| = (3007739418 * h / 958003200) * |J| := by
    rw [abs_mul, abs_of_nonneg hcJ_nn]
  have habsK : |(1305971115 * h / 958003200) * K| = (1305971115 * h / 958003200) * |K| := by
    rw [abs_mul, abs_of_nonneg hcK_nn]
  have habsL : |(384709327 * h / 958003200) * L| = (384709327 * h / 958003200) * |L| := by
    rw [abs_mul, abs_of_nonneg hcL_nn]
  have habsM : |(68928781 * h / 958003200) * M| = (68928781 * h / 958003200) * |M| := by
    rw [abs_mul, abs_of_nonneg hcM_nn]
  have htri := am11_residual_triangle_aux A B ((262747265 * h / 958003200) * C) ((1374799219 * h / 958003200) * D) ((2092490673 * h / 958003200) * E) ((3828828885 * h / 958003200) * F) ((5519460582 * h / 958003200) * G) ((6043521486 * h / 958003200) * H) ((4963166514 * h / 958003200) * I) ((3007739418 * h / 958003200) * J) ((1305971115 * h / 958003200) * K) ((384709327 * h / 958003200) * L) ((68928781 * h / 958003200) * M)
  rw [habsC, habsD, habsE, habsF, habsG, habsH, habsI, habsJ, habsK, habsL, habsM] at htri
  exact htri

private lemma am11_residual_combine_aux
    (A B C D E F G H I J K L M : ℝ) {Mb h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ Mb)
    (hA_bd : |A| ≤ Mb / 6227020800 * (11 * h) ^ 13)
    (hB_bd : |B| ≤ Mb / 6227020800 * (10 * h) ^ 13)
    (hC_bd : |C| ≤ Mb / 479001600 * (11 * h) ^ 12)
    (hD_bd : |D| ≤ Mb / 479001600 * (10 * h) ^ 12)
    (hE_bd : |E| ≤ Mb / 479001600 * (9 * h) ^ 12)
    (hF_bd : |F| ≤ Mb / 479001600 * (8 * h) ^ 12)
    (hG_bd : |G| ≤ Mb / 479001600 * (7 * h) ^ 12)
    (hH_bd : |H| ≤ Mb / 479001600 * (6 * h) ^ 12)
    (hI_bd : |I| ≤ Mb / 479001600 * (5 * h) ^ 12)
    (hJ_bd : |J| ≤ Mb / 479001600 * (4 * h) ^ 12)
    (hK_bd : |K| ≤ Mb / 479001600 * (3 * h) ^ 12)
    (hL_bd : |L| ≤ Mb / 479001600 * (2 * h) ^ 12)
    (hM_bd : |M| ≤ Mb / 479001600 * h ^ 12)
    : |A - B - (262747265 * h / 958003200) * C - (1374799219 * h / 958003200) * D + (2092490673 * h / 958003200) * E - (3828828885 * h / 958003200) * F + (5519460582 * h / 958003200) * G - (6043521486 * h / 958003200) * H + (4963166514 * h / 958003200) * I - (3007739418 * h / 958003200) * J + (1305971115 * h / 958003200) * K - (384709327 * h / 958003200) * L + (68928781 * h / 958003200) * M| ≤ (14003 : ℝ) * Mb * h ^ 13 := by
  have htri := am11_residual_thirteen_term_triangle A B C D E F G H I J K L M h hh
  have hcC_nn : 0 ≤ 262747265 * h / 958003200 := by positivity
  have hcD_nn : 0 ≤ 1374799219 * h / 958003200 := by positivity
  have hcE_nn : 0 ≤ 2092490673 * h / 958003200 := by positivity
  have hcF_nn : 0 ≤ 3828828885 * h / 958003200 := by positivity
  have hcG_nn : 0 ≤ 5519460582 * h / 958003200 := by positivity
  have hcH_nn : 0 ≤ 6043521486 * h / 958003200 := by positivity
  have hcI_nn : 0 ≤ 4963166514 * h / 958003200 := by positivity
  have hcJ_nn : 0 ≤ 3007739418 * h / 958003200 := by positivity
  have hcK_nn : 0 ≤ 1305971115 * h / 958003200 := by positivity
  have hcL_nn : 0 ≤ 384709327 * h / 958003200 := by positivity
  have hcM_nn : 0 ≤ 68928781 * h / 958003200 := by positivity
  have hCbd_s : (262747265 * h / 958003200) * |C|
      ≤ (262747265 * h / 958003200) * (Mb / 479001600 * (11 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hC_bd hcC_nn
  have hDbd_s : (1374799219 * h / 958003200) * |D|
      ≤ (1374799219 * h / 958003200) * (Mb / 479001600 * (10 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hD_bd hcD_nn
  have hEbd_s : (2092490673 * h / 958003200) * |E|
      ≤ (2092490673 * h / 958003200) * (Mb / 479001600 * (9 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hE_bd hcE_nn
  have hFbd_s : (3828828885 * h / 958003200) * |F|
      ≤ (3828828885 * h / 958003200) * (Mb / 479001600 * (8 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hF_bd hcF_nn
  have hGbd_s : (5519460582 * h / 958003200) * |G|
      ≤ (5519460582 * h / 958003200) * (Mb / 479001600 * (7 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hG_bd hcG_nn
  have hHbd_s : (6043521486 * h / 958003200) * |H|
      ≤ (6043521486 * h / 958003200) * (Mb / 479001600 * (6 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hH_bd hcH_nn
  have hIbd_s : (4963166514 * h / 958003200) * |I|
      ≤ (4963166514 * h / 958003200) * (Mb / 479001600 * (5 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hI_bd hcI_nn
  have hJbd_s : (3007739418 * h / 958003200) * |J|
      ≤ (3007739418 * h / 958003200) * (Mb / 479001600 * (4 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hJ_bd hcJ_nn
  have hKbd_s : (1305971115 * h / 958003200) * |K|
      ≤ (1305971115 * h / 958003200) * (Mb / 479001600 * (3 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hK_bd hcK_nn
  have hLbd_s : (384709327 * h / 958003200) * |L|
      ≤ (384709327 * h / 958003200) * (Mb / 479001600 * (2 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hL_bd hcL_nn
  have hMbd_s : (68928781 * h / 958003200) * |M|
      ≤ (68928781 * h / 958003200) * (Mb / 479001600 * h ^ 12) :=
    mul_le_mul_of_nonneg_left hM_bd hcM_nn
  have hbound_alg := am11_residual_bound_alg_identity Mb h
  have hh13_nn : 0 ≤ h ^ 13 := by positivity
  have hMh13_nn : 0 ≤ Mb * h ^ 13 := mul_nonneg hMnn hh13_nn
  have hslack : (345161607571042875013 / 24650850631680000 : ℝ) * Mb * h ^ 13
      ≤ 14003 * Mb * h ^ 13 := by
    rw [mul_assoc, mul_assoc (14003 : ℝ)]
    have hle : (345161607571042875013 / 24650850631680000 : ℝ) ≤ 14003 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh13_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hEbd_s, hFbd_s, hGbd_s, hHbd_s, hIbd_s, hJbd_s, hKbd_s, hLbd_s, hMbd_s]

/-- Pointwise AM11 truncation residual bound. -/
theorem am11_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 13 y) {a b Mb : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 13 y t| ≤ Mb)
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
    (ht11h : t + 11 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |am11Residual h t y| ≤ (14003 : ℝ) * Mb * h ^ 13 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have h9h : 0 ≤ 9 * h := by linarith
  have h10h : 0 ≤ 10 * h := by linarith
  have h11h : 0 ≤ 11 * h := by linarith
  have hRy10 :=
    y_thirteenth_order_taylor_remainder hy hbnd ht ht10h h10h
  have hRy11 :=
    y_thirteenth_order_taylor_remainder hy hbnd ht ht11h h11h
  have hRyp1 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht9h h9h
  have hRyp10 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht10h h10h
  have hRyp11 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht11h h11h
  unfold am11Residual
  set y0 := y t with hy0_def
  set y10 := y (t + 10 * h) with hy10_def
  set y11 := y (t + 11 * h) with hy11_def
  set d0 := deriv y (t) with hd0_def
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
  set d11 := deriv y (t + 11 * h) with hd11_def
  set d2t := iteratedDeriv 2 y t with hd2t_def
  set d3t := iteratedDeriv 3 y t with hd3t_def
  set d4t := iteratedDeriv 4 y t with hd4t_def
  set d5t := iteratedDeriv 5 y t with hd5t_def
  set d6t := iteratedDeriv 6 y t with hd6t_def
  set d7t := iteratedDeriv 7 y t with hd7t_def
  set d8t := iteratedDeriv 8 y t with hd8t_def
  set d9t := iteratedDeriv 9 y t with hd9t_def
  set d10t := iteratedDeriv 10 y t with hd10t_def
  set d11t := iteratedDeriv 11 y t with hd11t_def
  set d12t := iteratedDeriv 12 y t with hd12t_def
  clear_value y0 y10 y11 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
    d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t
  set A := y11 - y0 - (11 * h) * d0
            - (11 * h) ^ 2 / 2 * d2t
            - (11 * h) ^ 3 / 6 * d3t
            - (11 * h) ^ 4 / 24 * d4t
            - (11 * h) ^ 5 / 120 * d5t
            - (11 * h) ^ 6 / 720 * d6t
            - (11 * h) ^ 7 / 5040 * d7t
            - (11 * h) ^ 8 / 40320 * d8t
            - (11 * h) ^ 9 / 362880 * d9t
            - (11 * h) ^ 10 / 3628800 * d10t
            - (11 * h) ^ 11 / 39916800 * d11t
            - (11 * h) ^ 12 / 479001600 * d12t with hA_def
  set B := y10 - y0 - (10 * h) * d0
            - (10 * h) ^ 2 / 2 * d2t
            - (10 * h) ^ 3 / 6 * d3t
            - (10 * h) ^ 4 / 24 * d4t
            - (10 * h) ^ 5 / 120 * d5t
            - (10 * h) ^ 6 / 720 * d6t
            - (10 * h) ^ 7 / 5040 * d7t
            - (10 * h) ^ 8 / 40320 * d8t
            - (10 * h) ^ 9 / 362880 * d9t
            - (10 * h) ^ 10 / 3628800 * d10t
            - (10 * h) ^ 11 / 39916800 * d11t
            - (10 * h) ^ 12 / 479001600 * d12t with hB_def
  set C := d11 - d0 - (11 * h) * d2t
                - (11 * h) ^ 2 / 2 * d3t
                - (11 * h) ^ 3 / 6 * d4t
                - (11 * h) ^ 4 / 24 * d5t
                - (11 * h) ^ 5 / 120 * d6t
                - (11 * h) ^ 6 / 720 * d7t
                - (11 * h) ^ 7 / 5040 * d8t
                - (11 * h) ^ 8 / 40320 * d9t
                - (11 * h) ^ 9 / 362880 * d10t
                - (11 * h) ^ 10 / 3628800 * d11t
                - (11 * h) ^ 11 / 39916800 * d12t with hC_def
  set D := d10 - d0 - (10 * h) * d2t
                - (10 * h) ^ 2 / 2 * d3t
                - (10 * h) ^ 3 / 6 * d4t
                - (10 * h) ^ 4 / 24 * d5t
                - (10 * h) ^ 5 / 120 * d6t
                - (10 * h) ^ 6 / 720 * d7t
                - (10 * h) ^ 7 / 5040 * d8t
                - (10 * h) ^ 8 / 40320 * d9t
                - (10 * h) ^ 9 / 362880 * d10t
                - (10 * h) ^ 10 / 3628800 * d11t
                - (10 * h) ^ 11 / 39916800 * d12t with hD_def
  set E := d9 - d0 - (9 * h) * d2t
                - (9 * h) ^ 2 / 2 * d3t
                - (9 * h) ^ 3 / 6 * d4t
                - (9 * h) ^ 4 / 24 * d5t
                - (9 * h) ^ 5 / 120 * d6t
                - (9 * h) ^ 6 / 720 * d7t
                - (9 * h) ^ 7 / 5040 * d8t
                - (9 * h) ^ 8 / 40320 * d9t
                - (9 * h) ^ 9 / 362880 * d10t
                - (9 * h) ^ 10 / 3628800 * d11t
                - (9 * h) ^ 11 / 39916800 * d12t with hE_def
  set F := d8 - d0 - (8 * h) * d2t
                - (8 * h) ^ 2 / 2 * d3t
                - (8 * h) ^ 3 / 6 * d4t
                - (8 * h) ^ 4 / 24 * d5t
                - (8 * h) ^ 5 / 120 * d6t
                - (8 * h) ^ 6 / 720 * d7t
                - (8 * h) ^ 7 / 5040 * d8t
                - (8 * h) ^ 8 / 40320 * d9t
                - (8 * h) ^ 9 / 362880 * d10t
                - (8 * h) ^ 10 / 3628800 * d11t
                - (8 * h) ^ 11 / 39916800 * d12t with hF_def
  set G := d7 - d0 - (7 * h) * d2t
                - (7 * h) ^ 2 / 2 * d3t
                - (7 * h) ^ 3 / 6 * d4t
                - (7 * h) ^ 4 / 24 * d5t
                - (7 * h) ^ 5 / 120 * d6t
                - (7 * h) ^ 6 / 720 * d7t
                - (7 * h) ^ 7 / 5040 * d8t
                - (7 * h) ^ 8 / 40320 * d9t
                - (7 * h) ^ 9 / 362880 * d10t
                - (7 * h) ^ 10 / 3628800 * d11t
                - (7 * h) ^ 11 / 39916800 * d12t with hG_def
  set H := d6 - d0 - (6 * h) * d2t
                - (6 * h) ^ 2 / 2 * d3t
                - (6 * h) ^ 3 / 6 * d4t
                - (6 * h) ^ 4 / 24 * d5t
                - (6 * h) ^ 5 / 120 * d6t
                - (6 * h) ^ 6 / 720 * d7t
                - (6 * h) ^ 7 / 5040 * d8t
                - (6 * h) ^ 8 / 40320 * d9t
                - (6 * h) ^ 9 / 362880 * d10t
                - (6 * h) ^ 10 / 3628800 * d11t
                - (6 * h) ^ 11 / 39916800 * d12t with hH_def
  set I := d5 - d0 - (5 * h) * d2t
                - (5 * h) ^ 2 / 2 * d3t
                - (5 * h) ^ 3 / 6 * d4t
                - (5 * h) ^ 4 / 24 * d5t
                - (5 * h) ^ 5 / 120 * d6t
                - (5 * h) ^ 6 / 720 * d7t
                - (5 * h) ^ 7 / 5040 * d8t
                - (5 * h) ^ 8 / 40320 * d9t
                - (5 * h) ^ 9 / 362880 * d10t
                - (5 * h) ^ 10 / 3628800 * d11t
                - (5 * h) ^ 11 / 39916800 * d12t with hI_def
  set J := d4 - d0 - (4 * h) * d2t
                - (4 * h) ^ 2 / 2 * d3t
                - (4 * h) ^ 3 / 6 * d4t
                - (4 * h) ^ 4 / 24 * d5t
                - (4 * h) ^ 5 / 120 * d6t
                - (4 * h) ^ 6 / 720 * d7t
                - (4 * h) ^ 7 / 5040 * d8t
                - (4 * h) ^ 8 / 40320 * d9t
                - (4 * h) ^ 9 / 362880 * d10t
                - (4 * h) ^ 10 / 3628800 * d11t
                - (4 * h) ^ 11 / 39916800 * d12t with hJ_def
  set K := d3 - d0 - (3 * h) * d2t
                - (3 * h) ^ 2 / 2 * d3t
                - (3 * h) ^ 3 / 6 * d4t
                - (3 * h) ^ 4 / 24 * d5t
                - (3 * h) ^ 5 / 120 * d6t
                - (3 * h) ^ 6 / 720 * d7t
                - (3 * h) ^ 7 / 5040 * d8t
                - (3 * h) ^ 8 / 40320 * d9t
                - (3 * h) ^ 9 / 362880 * d10t
                - (3 * h) ^ 10 / 3628800 * d11t
                - (3 * h) ^ 11 / 39916800 * d12t with hK_def
  set L := d2 - d0 - (2 * h) * d2t
                - (2 * h) ^ 2 / 2 * d3t
                - (2 * h) ^ 3 / 6 * d4t
                - (2 * h) ^ 4 / 24 * d5t
                - (2 * h) ^ 5 / 120 * d6t
                - (2 * h) ^ 6 / 720 * d7t
                - (2 * h) ^ 7 / 5040 * d8t
                - (2 * h) ^ 8 / 40320 * d9t
                - (2 * h) ^ 9 / 362880 * d10t
                - (2 * h) ^ 10 / 3628800 * d11t
                - (2 * h) ^ 11 / 39916800 * d12t with hL_def
  set M := d1 - d0 - h * d2t
                - h ^ 2 / 2 * d3t
                - h ^ 3 / 6 * d4t
                - h ^ 4 / 24 * d5t
                - h ^ 5 / 120 * d6t
                - h ^ 6 / 720 * d7t
                - h ^ 7 / 5040 * d8t
                - h ^ 8 / 40320 * d9t
                - h ^ 9 / 362880 * d10t
                - h ^ 10 / 3628800 * d11t
                - h ^ 11 / 39916800 * d12t with hM_def
  clear_value A B C D E F G H I J K L M
  have hLTE_eq :=
    am11_residual_alg_identity y0 y10 y11 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t h A B C D E F G H I J K L M hA_def hB_def hC_def hD_def hE_def hF_def hG_def hH_def hI_def hJ_def hK_def hL_def hM_def
  have hres_eq :
      y11 - y10 - h * (∑ j : Fin 12,
          am11Coeff j * deriv y (t + (j : ℕ) * h))
        =
          y11 - y10
            - h * ((262747265 / 958003200 : ℝ) * d11
                  + (1374799219 / 958003200 : ℝ) * d10
                  - (2092490673 / 958003200 : ℝ) * d9
                  + (3828828885 / 958003200 : ℝ) * d8
                  - (5519460582 / 958003200 : ℝ) * d7
                  + (6043521486 / 958003200 : ℝ) * d6
                  - (4963166514 / 958003200 : ℝ) * d5
                  + (3007739418 / 958003200 : ℝ) * d4
                  - (1305971115 / 958003200 : ℝ) * d3
                  + (384709327 / 958003200 : ℝ) * d2
                  - (68928781 / 958003200 : ℝ) * d1
                  + (5675265 / 958003200 : ℝ) * d0) := by
    simp [am11Coeff, Fin.sum_univ_succ, hd0_def, hd1_def, hd2_def, hd3_def,
      hd4_def, hd5_def, hd6_def, hd7_def, hd8_def, hd9_def, hd10_def, hd11_def]
    ring_nf
    norm_num
  rw [hres_eq, hLTE_eq]
  have hA_bd : |A| ≤ Mb / 6227020800 * (11 * h) ^ 13 := hRy11
  have hB_bd : |B| ≤ Mb / 6227020800 * (10 * h) ^ 13 := hRy10
  have hC_bd : |C| ≤ Mb / 479001600 * (11 * h) ^ 12 := hRyp11
  have hD_bd : |D| ≤ Mb / 479001600 * (10 * h) ^ 12 := hRyp10
  have hE_bd : |E| ≤ Mb / 479001600 * (9 * h) ^ 12 := hRyp9
  have hF_bd : |F| ≤ Mb / 479001600 * (8 * h) ^ 12 := hRyp8
  have hG_bd : |G| ≤ Mb / 479001600 * (7 * h) ^ 12 := hRyp7
  have hH_bd : |H| ≤ Mb / 479001600 * (6 * h) ^ 12 := hRyp6
  have hI_bd : |I| ≤ Mb / 479001600 * (5 * h) ^ 12 := hRyp5
  have hJ_bd : |J| ≤ Mb / 479001600 * (4 * h) ^ 12 := hRyp4
  have hK_bd : |K| ≤ Mb / 479001600 * (3 * h) ^ 12 := hRyp3
  have hL_bd : |L| ≤ Mb / 479001600 * (2 * h) ^ 12 := hRyp2
  have hM_bd : |M| ≤ Mb / 479001600 * h ^ 12 := hRyp1
  have hMnn : 0 ≤ Mb := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact am11_residual_combine_aux A B C D E F G H I J K L M hh hMnn
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hH_bd hI_bd hJ_bd hK_bd hL_bd hM_bd

/-- Uniform bound on the AM11 one-step truncation residual on a finite
horizon, given a `C^13` exact solution. -/
theorem am11_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 13 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 11) * h ≤ T →
        |adamsMoulton11.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 13 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_thirteen_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(14003 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 11) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 9 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht10h_mem : t + 10 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 10 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht11h_mem : t + 11 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 11 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have hpoint :=
    am11_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem
      ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem ht10h_mem
      ht11h_mem hh.le
  rw [am11_localTruncationError_eq]
  exact hpoint

/-- Headline AM11 global error bound. -/
theorem am11_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 13 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (262747265 / 958003200 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsAM11Trajectory h f t₀ yseq →
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
      |yseq 10 - y (t₀ + 10 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 10) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((61 * L) * T) * ε₀ + K * h ^ 11 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am11_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((61 * L) * T) * (2 * C), min δ 1, ?_,
    lt_min hδ_pos (by norm_num), ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδg_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd he10_bd N hNh
  have hδ_le : h ≤ δ := le_trans hδg_le (min_le_left δ 1)
  have h_le_one : h ≤ 1 := le_trans hδg_le (min_le_right δ 1)
  set EN : ℕ → ℝ := fun k => am11ErrWindow h t₀ yseq y k with hEN_def
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k => by
    simpa [hEN_def] using am11ErrWindow_nonneg h t₀ yseq y k
  have hEN0_le : EN 0 ≤ ε₀ := by
    unfold EN
    unfold am11ErrWindow
    apply Finset.sup'_le
    intro j _
    fin_cases j
    · simpa [am11Err] using he0_bd
    · simpa [am11Err] using he1_bd
    · simpa [am11Err] using he2_bd
    · simpa [am11Err] using he3_bd
    · simpa [am11Err] using he4_bd
    · simpa [am11Err] using he5_bd
    · simpa [am11Err] using he6_bd
    · simpa [am11Err] using he7_bd
    · simpa [am11Err] using he8_bd
    · simpa [am11Err] using he9_bd
    · simpa [am11Err] using he10_bd
  have h61L_nn : (0 : ℝ) ≤ 61 * L := by linarith
  have hh13_le_hh12 : h ^ 13 ≤ h ^ 12 := by
    calc
      h ^ 13 = h ^ 12 * h := by ring
      _ ≤ h ^ 12 * 1 :=
        mul_le_mul_of_nonneg_left h_le_one (by positivity)
      _ = h ^ 12 := by ring
  have hstep_general : ∀ n : ℕ, n < N →
      EN (n + 1) ≤ (1 + h * (61 * L)) * EN n + (2 * C) * h ^ 12 := by
    intro n hn_lt
    have hres_arg : ((n : ℝ) + 11) * h ≤ T := by
      have hnat : n + 11 ≤ N + 10 := by omega
      have hreal : (n : ℝ) + 11 ≤ (N : ℝ) + 10 := by
        exact_mod_cast hnat
      have hle : ((n : ℝ) + 11) * h ≤ ((N : ℝ) + 10) * h :=
        mul_le_mul_of_nonneg_right hreal hh.le
      exact le_trans hle hNh
    have honestep :=
      am11_one_step_error_pair_bound (h := h) (L := L) hh.le hL hsmall
        hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hres_arg
    have h2τ : 2 * |adamsMoulton11.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (2 * C) * h ^ 12 := by
      have h2res : 2 * |adamsMoulton11.localTruncationError h
          (t₀ + (n : ℝ) * h) y| ≤ 2 * (C * h ^ 13) :=
        mul_le_mul_of_nonneg_left hres (by norm_num)
      have hweak : 2 * (C * h ^ 13) ≤ (2 * C) * h ^ 12 := by
        have hC2_nn : 0 ≤ 2 * C := by positivity
        have := mul_le_mul_of_nonneg_left hh13_le_hh12 hC2_nn
        linarith
      exact le_trans h2res hweak
    show EN (n + 1) ≤ (1 + h * (61 * L)) * EN n + (2 * C) * h ^ 12
    simpa [hEN_def] using le_trans honestep (by linarith)
  have hNh_base : (N : ℝ) * h ≤ T := by
    have hle : (N : ℝ) * h ≤ ((N : ℝ) + 10) * h :=
      mul_le_mul_of_nonneg_right (by linarith) hh.le
    exact le_trans hle hNh
  have hgronwall :=
    lmm_error_bound_from_local_truncation
      (h := h) (L := 61 * L) (C := 2 * C) (T := T) (p := 11) (e := EN)
      (N := N) hh.le h61L_nn (by positivity) (hEN_nn 0) hstep_general
      N le_rfl hNh_base
  have hexp_nn : 0 ≤ Real.exp ((61 * L) * T) := Real.exp_nonneg _
  have hstart_chain :
      Real.exp ((61 * L) * T) * EN 0
        ≤ Real.exp ((61 * L) * T) * ε₀ :=
    mul_le_mul_of_nonneg_left hEN0_le hexp_nn
  have hEN_bound :
      EN N ≤ Real.exp ((61 * L) * T) * ε₀
        + T * Real.exp ((61 * L) * T) * (2 * C) * h ^ 11 := by
    linarith
  have hpoint_le_window : am11Err h t₀ yseq y N ≤ EN N := by
    show am11Err h t₀ yseq y N ≤ am11ErrWindow h t₀ yseq y N
    unfold am11ErrWindow
    have hsup := Finset.le_sup' (b := (0 : Fin 11))
      (f := fun j : Fin 11 => am11Err h t₀ yseq y (N + (j : ℕ)))
      (Finset.mem_univ _)
    simpa using hsup
  calc
    |yseq N - y (t₀ + (N : ℝ) * h)|
        = am11Err h t₀ yseq y N := rfl
    _ ≤ EN N := hpoint_le_window
    _ ≤ Real.exp ((61 * L) * T) * ε₀
        + T * Real.exp ((61 * L) * T) * (2 * C) * h ^ 11 := hEN_bound

end LMM
