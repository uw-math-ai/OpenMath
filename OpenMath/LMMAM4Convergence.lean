import OpenMath.LMMTruncationOp
import OpenMath.LMMAB4Convergence
import OpenMath.LMMAB5Convergence
import OpenMath.AdamsMethods

/-! ## Adams--Moulton 4-step Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit Adams--Moulton
4-step method.  The chain follows the AM3 template (cycle 435) one stencil
step up: the implicit update is parameterised by a supplied trajectory
satisfying the AM4 recurrence, the local residual is bounded by sixth-order
Taylor remainders exposed from `LMMAB5Convergence`, and the global error is
assembled with `lmm_error_bound_from_local_truncation`.

The one-step Lipschitz inequality keeps the new implicit sample on the left
with factor `1 - (251/720)·h·L`.  The explicit-history weights add up to
`1035/720 = 23/16`, and we slack the divided growth constant to `4L`
(`3L` does not close `nlinarith` across the full small-step regime). -/

namespace LMM

/-- AM4 trajectory predicate:
`y_{n+4} = y_{n+3} + h(251/720 f_{n+4} + 646/720 f_{n+3}
  - 264/720 f_{n+2} + 106/720 f_{n+1} - 19/720 f_n)`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM4Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 4)
      = y (n + 3)
        + h * ((251 / 720 : ℝ) * f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             + (646 / 720 : ℝ) * f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             - (264 / 720 : ℝ) * f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             + (106 / 720 : ℝ) * f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             - (19 / 720 : ℝ) * f (t₀ + (n : ℝ) * h) (y n))

/-- AM4 local truncation operator reduces to the textbook residual
`y(t+4h) - y(t+3h) - h(251/720 y'(t+4h) + 646/720 y'(t+3h)
  - 264/720 y'(t+2h) + 106/720 y'(t+h) - 19/720 y'(t))`. -/
theorem am4_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsMoulton4.localTruncationError h t y
      = y (t + 4 * h) - y (t + 3 * h)
          - h * ((251 / 720 : ℝ) * deriv y (t + 4 * h)
                + (646 / 720 : ℝ) * deriv y (t + 3 * h)
                - (264 / 720 : ℝ) * deriv y (t + 2 * h)
                + (106 / 720 : ℝ) * deriv y (t + h)
                - (19 / 720 : ℝ) * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsMoulton4, Fin.sum_univ_five, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AM4 Lipschitz inequality before dividing by the implicit
new-point factor.  The side condition records the small-step regime used by
the divided form. -/
theorem am4_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (251 / 720 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM4Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (251 / 720 : ℝ) * h * L)
        * |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
      ≤ |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
        + (646 / 720 : ℝ) * h * L
            * |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
        + (264 / 720 : ℝ) * h * L
            * |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
        + (106 / 720 : ℝ) * h * L
            * |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
        + (19 / 720 : ℝ) * h * L
            * |yseq n - y (t₀ + (n : ℝ) * h)|
        + |adamsMoulton4.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  -- Abbreviations.
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set yn3 : ℝ := yseq (n + 3) with hyn3_def
  set yn4 : ℝ := yseq (n + 4) with hyn4_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set τ : ℝ := adamsMoulton4.localTruncationError h tn y with hτ_def
  have _hsmall_record : (251 / 720 : ℝ) * h * L ≤ 1 / 2 := hsmall
  -- AM4 step formula for the supplied implicit trajectory.
  have hstep : yn4
      = yn3
        + h * ((251 / 720 : ℝ) * f tn4 yn4
             + (646 / 720 : ℝ) * f tn3 yn3
             - (264 / 720 : ℝ) * f tn2 yn2
             + (106 / 720 : ℝ) * f tn1 yn1
             - (19 / 720 : ℝ) * f tn yn) := by
    simpa [hyn4_def, hyn3_def, hyn2_def, hyn1_def, hyn_def, htn4_def,
      htn3_def, htn2_def, htn1_def, htn_def] using hy.recurrence n
  -- Local truncation residual at `tn`, expressed via `f` along the trajectory.
  have htn1_h : tn + h = tn1 := by
    simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by
    simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by
    simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by
    simp [htn_def, htn4_def]; ring
  have hτ_eq : τ = zn4 - zn3
      - h * ((251 / 720 : ℝ) * f tn4 zn4
             + (646 / 720 : ℝ) * f tn3 zn3
             - (264 / 720 : ℝ) * f tn2 zn2
             + (106 / 720 : ℝ) * f tn1 zn1
             - (19 / 720 : ℝ) * f tn zn) := by
    show adamsMoulton4.localTruncationError h tn y = _
    rw [am4_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h,
      hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the implicit global-error increment.
  have halg : yn4 - zn4
      = (yn3 - zn3)
        + (251 / 720 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        + (646 / 720 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        - (264 / 720 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        + (106 / 720 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        - (19 / 720 : ℝ) * h * (f tn yn - f tn zn)
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
  -- Lipschitz bounds on the five `f` increments.
  have hLip4 : |f tn4 yn4 - f tn4 zn4| ≤ L * |yn4 - zn4| :=
    hf tn4 yn4 zn4
  have hLip3 : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| :=
    hf tn3 yn3 zn3
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| :=
    hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| :=
    hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| :=
    hf tn yn zn
  have h251_nn : 0 ≤ (251 / 720 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h646_nn : 0 ≤ (646 / 720 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h264_nn : 0 ≤ (264 / 720 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h106_nn : 0 ≤ (106 / 720 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h19_nn : 0 ≤ (19 / 720 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h251_abs :
      |(251 / 720 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (251 / 720 : ℝ) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h251_nn]
    calc (251 / 720 : ℝ) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (251 / 720 : ℝ) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 h251_nn
      _ = (251 / 720 : ℝ) * h * L * |yn4 - zn4| := by ring
  have h646_abs :
      |(646 / 720 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (646 / 720 : ℝ) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h646_nn]
    calc (646 / 720 : ℝ) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (646 / 720 : ℝ) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h646_nn
      _ = (646 / 720 : ℝ) * h * L * |yn3 - zn3| := by ring
  have h264_abs :
      |(264 / 720 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (264 / 720 : ℝ) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h264_nn]
    calc (264 / 720 : ℝ) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (264 / 720 : ℝ) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h264_nn
      _ = (264 / 720 : ℝ) * h * L * |yn2 - zn2| := by ring
  have h106_abs :
      |(106 / 720 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (106 / 720 : ℝ) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h106_nn]
    calc (106 / 720 : ℝ) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (106 / 720 : ℝ) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h106_nn
      _ = (106 / 720 : ℝ) * h * L * |yn1 - zn1| := by ring
  have h19_abs :
      |(19 / 720 : ℝ) * h * (f tn yn - f tn zn)|
      ≤ (19 / 720 : ℝ) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h19_nn]
    calc (19 / 720 : ℝ) * h * |f tn yn - f tn zn|
        ≤ (19 / 720 : ℝ) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h19_nn
      _ = (19 / 720 : ℝ) * h * L * |yn - zn| := by ring
  -- Triangle inequality, then move the implicit contribution to the left.
  have htri_terms (A B C D E F G : ℝ) :
      |A + B + C - D + E - F - G|
        ≤ |A| + |B| + |C| + |D| + |E| + |F| + |G| := by
    have h1 : |A + B + C - D + E - F - G|
        ≤ |A + B + C - D + E - F| + |G| := abs_sub _ _
    have h2 : |A + B + C - D + E - F|
        ≤ |A + B + C - D + E| + |F| := abs_sub _ _
    have h3 : |A + B + C - D + E|
        ≤ |A + B + C - D| + |E| := abs_add_le _ _
    have h4 : |A + B + C - D| ≤ |A + B + C| + |D| := abs_sub _ _
    have h5 : |A + B + C| ≤ |A + B| + |C| := abs_add_le _ _
    have h6 : |A + B| ≤ |A| + |B| := abs_add_le _ _
    linarith
  have htri :
      |(yn3 - zn3)
        + (251 / 720 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        + (646 / 720 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        - (264 / 720 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        + (106 / 720 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        - (19 / 720 : ℝ) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn3 - zn3|
          + |(251 / 720 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(646 / 720 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(264 / 720 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(106 / 720 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(19 / 720 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| :=
    htri_terms (yn3 - zn3)
      ((251 / 720 : ℝ) * h * (f tn4 yn4 - f tn4 zn4))
      ((646 / 720 : ℝ) * h * (f tn3 yn3 - f tn3 zn3))
      ((264 / 720 : ℝ) * h * (f tn2 yn2 - f tn2 zn2))
      ((106 / 720 : ℝ) * h * (f tn1 yn1 - f tn1 zn1))
      ((19 / 720 : ℝ) * h * (f tn yn - f tn zn)) τ
  have hmain :
      |yn4 - zn4|
        ≤ |yn3 - zn3|
          + (251 / 720 : ℝ) * h * L * |yn4 - zn4|
          + (646 / 720 : ℝ) * h * L * |yn3 - zn3|
          + (264 / 720 : ℝ) * h * L * |yn2 - zn2|
          + (106 / 720 : ℝ) * h * L * |yn1 - zn1|
          + (19 / 720 : ℝ) * h * L * |yn - zn|
          + |τ| := by
    calc |yn4 - zn4|
        = |(yn3 - zn3)
            + (251 / 720 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
            + (646 / 720 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
            - (264 / 720 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
            + (106 / 720 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
            - (19 / 720 : ℝ) * h * (f tn yn - f tn zn)
            - τ| := by rw [halg]
      _ ≤ |yn3 - zn3|
          + |(251 / 720 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(646 / 720 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(264 / 720 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(106 / 720 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(19 / 720 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| := htri
      _ ≤ |yn3 - zn3|
          + (251 / 720 : ℝ) * h * L * |yn4 - zn4|
          + (646 / 720 : ℝ) * h * L * |yn3 - zn3|
          + (264 / 720 : ℝ) * h * L * |yn2 - zn2|
          + (106 / 720 : ℝ) * h * L * |yn1 - zn1|
          + (19 / 720 : ℝ) * h * L * |yn - zn|
          + |τ| := by
        linarith [h251_abs, h646_abs, h264_abs, h106_abs, h19_abs]
  linarith [hmain]

/-- Divided one-step AM4 error bound.  The explicit AM4 weights contribute
`23/16 = 1035/720`; after dividing by the implicit `(1 - (251/720)hL)`
factor, we slacken the max-window growth to `4L` and the residual
coefficient to `2`. -/
theorem am4_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (251 / 720 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM4Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
      ≤ (1 + h * (4 * L))
            * max (max (max |yseq n - y (t₀ + (n : ℝ) * h)|
                            |yseq (n + 1)
                                - y (t₀ + ((n : ℝ) + 1) * h)|)
                       |yseq (n + 2)
                            - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |yseq (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)|
        + 2 * |adamsMoulton4.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |yseq n - y (t₀ + (n : ℝ) * h)| with hen_def
  set en1 : ℝ :=
    |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| with hen1_def
  set en2 : ℝ :=
    |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| with hen2_def
  set en3 : ℝ :=
    |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)| with hen3_def
  set en4 : ℝ :=
    |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)| with hen4_def
  set τabs : ℝ :=
    |adamsMoulton4.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ := max (max (max en en1) en2) en3 with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen_le_E : en ≤ E :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen3_le_E : en3 ≤ E := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 360 / 251 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (251 / 720 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (251 / 720 : ℝ) * h * L) * en4
        ≤ en3
          + (646 / 720 : ℝ) * h * L * en3
          + (264 / 720 : ℝ) * h * L * en2
          + (106 / 720 : ℝ) * h * L * en1
          + (19 / 720 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hτabs_def] using
      (am4_one_step_lipschitz (h := h) (L := L) hh hsmall hf t₀ hy y hyf n)
  have h646_nn : 0 ≤ (646 / 720 : ℝ) * h * L := by positivity
  have h264_nn : 0 ≤ (264 / 720 : ℝ) * h * L := by positivity
  have h106_nn : 0 ≤ (106 / 720 : ℝ) * h * L := by positivity
  have h19_nn : 0 ≤ (19 / 720 : ℝ) * h * L := by positivity
  have h646_le :
      (646 / 720 : ℝ) * h * L * en3
        ≤ (646 / 720 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen3_le_E h646_nn
  have h264_le :
      (264 / 720 : ℝ) * h * L * en2
        ≤ (264 / 720 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen2_le_E h264_nn
  have h106_le :
      (106 / 720 : ℝ) * h * L * en1
        ≤ (106 / 720 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen1_le_E h106_nn
  have h19_le :
      (19 / 720 : ℝ) * h * L * en
        ≤ (19 / 720 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen_le_E h19_nn
  have hR_le :
      en3
          + (646 / 720 : ℝ) * h * L * en3
          + (264 / 720 : ℝ) * h * L * en2
          + (106 / 720 : ℝ) * h * L * en1
          + (19 / 720 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (23 / 16 : ℝ) * (h * L)) * E + τabs := by
    have h_alg :
        E + (646 / 720 : ℝ) * h * L * E
            + (264 / 720 : ℝ) * h * L * E
            + (106 / 720 : ℝ) * h * L * E
            + (19 / 720 : ℝ) * h * L * E + τabs
          = (1 + (23 / 16 : ℝ) * (h * L)) * E + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (23 / 16 : ℝ) * (h * L)
        ≤ (1 - (251 / 720 : ℝ) * h * L) * (1 + h * (4 * L)) := by
    nlinarith [hx_nn, hx_small, hsmall]
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (251 / 720 : ℝ) * h * L) * 2 := by
    nlinarith [hsmall]
  have hE_part :
      (1 + (23 / 16 : ℝ) * (h * L)) * E
        ≤ ((1 - (251 / 720 : ℝ) * h * L) * (1 + h * (4 * L))) * E :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (251 / 720 : ℝ) * h * L) * 2) * τabs :=
    by simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (23 / 16 : ℝ) * (h * L)) * E + τabs
        ≤ (1 - (251 / 720 : ℝ) * h * L)
            * ((1 + h * (4 * L)) * E + 2 * τabs) := by
    have hsplit :
        (1 - (251 / 720 : ℝ) * h * L)
            * ((1 + h * (4 * L)) * E + 2 * τabs)
          = ((1 - (251 / 720 : ℝ) * h * L) * (1 + h * (4 * L))) * E
              + ((1 - (251 / 720 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (251 / 720 : ℝ) * h * L) * en4
        ≤ (1 - (251 / 720 : ℝ) * h * L)
            * ((1 + h * (4 * L)) * E + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  have hcancel :
      en4 ≤ (1 + h * (4 * L)) * E + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  exact hcancel

/-- Max-norm AM4 one-step recurrence on the rolling 4-window
`(en, en1, en2, en3)`. -/
theorem am4_one_step_error_pair_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (251 / 720 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM4Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max
          |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
        |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
      ≤ (1 + h * (4 * L))
            * max (max (max |yseq n - y (t₀ + (n : ℝ) * h)|
                            |yseq (n + 1)
                                - y (t₀ + ((n : ℝ) + 1) * h)|)
                       |yseq (n + 2)
                            - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |yseq (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)|
        + 2 * |adamsMoulton4.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |yseq n - y (t₀ + (n : ℝ) * h)| with hen_def
  set en1 : ℝ :=
    |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| with hen1_def
  set en2 : ℝ :=
    |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| with hen2_def
  set en3 : ℝ :=
    |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)| with hen3_def
  set en4 : ℝ :=
    |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)| with hen4_def
  set τabs : ℝ :=
    |adamsMoulton4.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ := max (max (max en en1) en2) en3 with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen3_le_E : en3 ≤ E := le_max_right _ _
  have h4hL_nn : 0 ≤ h * (4 * L) := by positivity
  -- en4 bound from `am4_one_step_error_bound`.
  have hen4_bd :
      en4 ≤ (1 + h * (4 * L)) * E + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hτabs_def, hE_def]
      using
      (am4_one_step_error_bound (h := h) (L := L) hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : E ≤ (1 + h * (4 * L)) * E := by
    have hone : (1 : ℝ) * E ≤ (1 + h * (4 * L)) * E :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (4 * L)) * E + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (4 * L)) * E + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (4 * L)) * E + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  exact max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd) hen4_bd

/-- Pointwise AM4 truncation residual bound.  The residual expands as
`R_y(4) - R_y(3) - (251h/720)·R_y'(4) - (646h/720)·R_y'(3)
  + (264h/720)·R_y'(2) - (106h/720)·R_y'(1)`.  The exact triangle-bound
coefficient is `1001556/86400 = 250389/21600 ≤ 12`. -/
theorem am4_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 6 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 4 * h) - y (t + 3 * h)
        - h * ((251 / 720) * deriv y (t + 4 * h)
              + (646 / 720) * deriv y (t + 3 * h)
              - (264 / 720) * deriv y (t + 2 * h)
              + (106 / 720) * deriv y (t + h)
              - (19 / 720) * deriv y t)|
      ≤ (12 : ℝ) * M * h ^ 6 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  -- R_y(3) and R_y(4), both expanded to fifth order around `t`.
  have hRy3 :=
    y_sixth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRy4 :=
    y_sixth_order_taylor_remainder hy hbnd ht ht4h h4h
  -- Remainders for `y'` at h, 2h, 3h, 4h.
  have hRyp1 :=
    derivY_fifth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_fifth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_fifth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_fifth_order_taylor_remainder hy hbnd ht ht4h h4h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y3 := y (t + 3 * h) with hy3_def
  set y4 := y (t + 4 * h) with hy4_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  -- Algebraic identity for the AM4 residual.
  have hLTE_eq :
      y4 - y3 - h * ((251 / 720) * d4 + (646 / 720) * d3
                    - (264 / 720) * d2 + (106 / 720) * d1
                    - (19 / 720) * d0)
        = (y4 - y0 - (4 * h) * d0
              - (4 * h) ^ 2 / 2 * dd
              - (4 * h) ^ 3 / 6 * ddd
              - (4 * h) ^ 4 / 24 * dddd
              - (4 * h) ^ 5 / 120 * ddddd)
          - (y3 - y0 - (3 * h) * d0
              - (3 * h) ^ 2 / 2 * dd
              - (3 * h) ^ 3 / 6 * ddd
              - (3 * h) ^ 4 / 24 * dddd
              - (3 * h) ^ 5 / 120 * ddddd)
          - (251 * h / 720)
              * (d4 - d0 - (4 * h) * dd
                  - (4 * h) ^ 2 / 2 * ddd
                  - (4 * h) ^ 3 / 6 * dddd
                  - (4 * h) ^ 4 / 24 * ddddd)
          - (646 * h / 720)
              * (d3 - d0 - (3 * h) * dd
                  - (3 * h) ^ 2 / 2 * ddd
                  - (3 * h) ^ 3 / 6 * dddd
                  - (3 * h) ^ 4 / 24 * ddddd)
          + (264 * h / 720)
              * (d2 - d0 - (2 * h) * dd
                  - (2 * h) ^ 2 / 2 * ddd
                  - (2 * h) ^ 3 / 6 * dddd
                  - (2 * h) ^ 4 / 24 * ddddd)
          - (106 * h / 720)
              * (d1 - d0 - h * dd
                  - h ^ 2 / 2 * ddd
                  - h ^ 3 / 6 * dddd
                  - h ^ 4 / 24 * ddddd) := by ring
  rw [hLTE_eq]
  -- Triangle inequality.
  set A := y4 - y0 - (4 * h) * d0
            - (4 * h) ^ 2 / 2 * dd
            - (4 * h) ^ 3 / 6 * ddd
            - (4 * h) ^ 4 / 24 * dddd
            - (4 * h) ^ 5 / 120 * ddddd with hA_def
  set B := y3 - y0 - (3 * h) * d0
            - (3 * h) ^ 2 / 2 * dd
            - (3 * h) ^ 3 / 6 * ddd
            - (3 * h) ^ 4 / 24 * dddd
            - (3 * h) ^ 5 / 120 * ddddd with hB_def
  set C := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd with hC_def
  set D := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd with hD_def
  set E := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd with hE_def
  set F := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd with hF_def
  have h251h_nn : 0 ≤ 251 * h / 720 := by linarith
  have h646h_nn : 0 ≤ 646 * h / 720 := by linarith
  have h264h_nn : 0 ≤ 264 * h / 720 := by linarith
  have h106h_nn : 0 ≤ 106 * h / 720 := by linarith
  have habs251 : |(251 * h / 720) * C| = (251 * h / 720) * |C| := by
    rw [abs_mul, abs_of_nonneg h251h_nn]
  have habs646 : |(646 * h / 720) * D| = (646 * h / 720) * |D| := by
    rw [abs_mul, abs_of_nonneg h646h_nn]
  have habs264 : |(264 * h / 720) * E| = (264 * h / 720) * |E| := by
    rw [abs_mul, abs_of_nonneg h264h_nn]
  have habs106 : |(106 * h / 720) * F| = (106 * h / 720) * |F| := by
    rw [abs_mul, abs_of_nonneg h106h_nn]
  have htri : |A - B - (251 * h / 720) * C - (646 * h / 720) * D
                  + (264 * h / 720) * E - (106 * h / 720) * F|
      ≤ |A| + |B| + (251 * h / 720) * |C| + (646 * h / 720) * |D|
          + (264 * h / 720) * |E| + (106 * h / 720) * |F| := by
    have h1 : |A - B - (251 * h / 720) * C - (646 * h / 720) * D
                  + (264 * h / 720) * E - (106 * h / 720) * F|
        ≤ |A - B - (251 * h / 720) * C - (646 * h / 720) * D
              + (264 * h / 720) * E| + |(106 * h / 720) * F| :=
      abs_sub _ _
    have h2 : |A - B - (251 * h / 720) * C - (646 * h / 720) * D
                  + (264 * h / 720) * E|
        ≤ |A - B - (251 * h / 720) * C - (646 * h / 720) * D|
            + |(264 * h / 720) * E| := abs_add_le _ _
    have h3 : |A - B - (251 * h / 720) * C - (646 * h / 720) * D|
        ≤ |A - B - (251 * h / 720) * C| + |(646 * h / 720) * D| :=
      abs_sub _ _
    have h4 : |A - B - (251 * h / 720) * C|
        ≤ |A - B| + |(251 * h / 720) * C| := abs_sub _ _
    have h5 : |A - B| ≤ |A| + |B| := abs_sub _ _
    linarith [habs251.le, habs251.ge, habs646.le, habs646.ge,
      habs264.le, habs264.ge, habs106.le, habs106.ge]
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 720 * (4 * h) ^ 6 := hRy4
  have hB_bd : |B| ≤ M / 720 * (3 * h) ^ 6 := hRy3
  have hC_bd : |C| ≤ M / 120 * (4 * h) ^ 5 := hRyp4
  have hD_bd : |D| ≤ M / 120 * (3 * h) ^ 5 := hRyp3
  have hE_bd : |E| ≤ M / 120 * (2 * h) ^ 5 := hRyp2
  have hF_bd : |F| ≤ M / 120 * h ^ 5 := hRyp1
  -- Multiply scaled bounds.
  have hC_scaled :
      (251 * h / 720) * |C| ≤ (251 * h / 720) * (M / 120 * (4 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hC_bd h251h_nn
  have hD_scaled :
      (646 * h / 720) * |D| ≤ (646 * h / 720) * (M / 120 * (3 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hD_bd h646h_nn
  have hE_scaled :
      (264 * h / 720) * |E| ≤ (264 * h / 720) * (M / 120 * (2 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hE_bd h264h_nn
  have hF_scaled :
      (106 * h / 720) * |F| ≤ (106 * h / 720) * (M / 120 * h ^ 5) :=
    mul_le_mul_of_nonneg_left hF_bd h106h_nn
  -- Sum of upper bounds = (4096 + 729)/720 + (251*1024 + 646*243 + 264*32 + 106)/86400
  --   = 1001556/86400 = 250389/21600 ≈ 11.59. Slacken to 12.
  have hbound_alg :
      M / 720 * (4 * h) ^ 6 + M / 720 * (3 * h) ^ 6
        + (251 * h / 720) * (M / 120 * (4 * h) ^ 5)
        + (646 * h / 720) * (M / 120 * (3 * h) ^ 5)
        + (264 * h / 720) * (M / 120 * (2 * h) ^ 5)
        + (106 * h / 720) * (M / 120 * h ^ 5)
        = (250389 / 21600 : ℝ) * M * h ^ 6 := by ring
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh6_nn : 0 ≤ h ^ 6 := by positivity
  have hMh6_nn : 0 ≤ M * h ^ 6 := mul_nonneg hMnn hh6_nn
  have hslack : (250389 / 21600 : ℝ) * M * h ^ 6 ≤ 12 * M * h ^ 6 := by
    have hle : (250389 / 21600 : ℝ) ≤ 12 := by norm_num
    have := mul_le_mul_of_nonneg_right hle hMh6_nn
    linarith [this]
  linarith [htri, hA_bd, hB_bd, hC_scaled, hD_scaled, hE_scaled, hF_scaled,
    hbound_alg.le, hbound_alg.ge, hslack]

/-- Uniform bound on the AM4 one-step truncation residual on a finite
horizon, given a `C^6` exact solution. -/
theorem am4_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 4) * h ≤ T →
        |adamsMoulton4.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 6 := by
  -- Choose a compact sample interval `[t₀, t₀ + T + 1]` covering all `t + kh`
  -- with `k ≤ 4` (using `(n+4)*h ≤ T` and `h ≤ 1`).
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_six_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(12 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 4) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h = ((n : ℝ) + 4) * h := by ring
    linarith
  -- Rewrite the LTE in textbook form.
  rw [am4_localTruncationError_eq]
  show |y (t + 4 * h) - y (t + 3 * h)
      - h * ((251 / 720) * deriv y (t + 4 * h)
            + (646 / 720) * deriv y (t + 3 * h)
            - (264 / 720) * deriv y (t + 2 * h)
            + (106 / 720) * deriv y (t + h)
            - (19 / 720) * deriv y t)|
    ≤ 12 * M * h ^ 6
  exact am4_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem hh.le

/-- Headline AM4 global error bound.  Given a supplied AM4 trajectory and
starting errors bounded by `ε₀`, the scalar global error is `O(ε₀ + h^5)` on
a finite horizon. -/
theorem am4_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 6 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (251 / 720 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsAM4Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      |yseq 2 - y (t₀ + 2 * h)| ≤ ε₀ →
      |yseq 3 - y (t₀ + 3 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 3) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((4 * L) * T) * ε₀ + K * h ^ 5 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am4_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((4 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    N hNh
  set eN : ℕ → ℝ :=
    fun k => |yseq k - y (t₀ + (k : ℝ) * h)| with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (eN k) (eN (k + 1))) (eN (k + 2))) (eN (k + 3))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (heN_nn k)))
  -- Initial bound: EN 0 ≤ ε₀.
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (eN 0) (eN 1)) (eN 2)) (eN 3) ≤ ε₀
    refine max_le (max_le (max_le ?_ ?_) ?_) ?_
    · show |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀
      simpa using he0_bd
    · show |yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    · show |yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    · show |yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
  have h4L_nn : (0 : ℝ) ≤ 4 * L := by linarith
  -- The general recurrence: when (n + 4) * h ≤ T,
  -- EN (n+1) ≤ (1 + h*(4L)) * EN n + 2*C*h^6.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 4) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (4 * L)) * EN n + (2 * C) * h ^ 6 := by
    intro n hnh_le
    have honestep := am4_one_step_error_pair_bound
      (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hcast4 : ((n + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 4 := by
      push_cast; ring
    have heq_eN_n : eN n
        = |yseq n - y (t₀ + (n : ℝ) * h)| := rfl
    have heq_eN_n1 : eN (n + 1)
        = |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| := by
      show |_ - _| = _
      rw [hcast1]
    have heq_eN_n2 : eN (n + 1 + 1)
        = |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| := by
      show |_ - _| = _
      rw [hcast2]
    have heq_eN_n3 : eN (n + 1 + 1 + 1)
        = |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)| := by
      show |_ - _| = _
      rw [hcast3]
    have heq_eN_n4 : eN (n + 1 + 1 + 1 + 1)
        = |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)| := by
      show |_ - _| = _
      rw [hcast4]
    show max (max (max (eN (n + 1)) (eN (n + 1 + 1))) (eN (n + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1))
        ≤ (1 + h * (4 * L))
            * max (max (max (eN n) (eN (n + 1))) (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))
          + (2 * C) * h ^ 6
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4]
    have h2τ : 2 * |adamsMoulton4.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (2 * C) * h ^ 6 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith [this]
    linarith [honestep, h2τ]
  -- Base cases N = 0, 1, 2, 3 are direct from the starting bounds.
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((4 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((4 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh5_nn : 0 ≤ h ^ 5 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((4 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((4 * L) * T) * ε₀
            + T * Real.exp ((4 * L) * T) * (2 * C) * h ^ 5 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((4 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((4 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh5_nn : 0 ≤ T * Real.exp ((4 * L) * T) * (2 * C) * h ^ 5 :=
      mul_nonneg hKnn hh5_nn
    linarith
  match N, hNh with
  | 0, _ =>
    have hbase : |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      simpa using he0_bd
    exact hbase_to_headline _ hbase
  | 1, _ =>
    have hbase : |yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    exact hbase_to_headline _ hbase
  | 2, _ =>
    have hbase : |yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    exact hbase_to_headline _ hbase
  | 3, _ =>
    have hbase : |yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
    exact hbase_to_headline _ hbase
  | N' + 4, hNh =>
    -- Apply Gronwall to EN at index N'+1, then use EN_{N'+1} ≥ e_{N'+4}.
    have hcast : (((N' + 4 : ℕ) : ℝ) + 3) = (N' : ℝ) + 7 := by
      push_cast; ring
    have hN_hyp : ((N' : ℝ) + 7) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (4 * L)) * EN n + (2 * C) * h ^ (5 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (5 + 1) = (2 * C) * h ^ 6 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 4 ≤ (N' : ℝ) + 7 := by linarith
      have h_mul : ((n : ℝ) + 4) * h ≤ ((N' : ℝ) + 7) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have hle : (N' : ℝ) + 1 ≤ (N' : ℝ) + 7 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 4 * L) (C := 2 * C) (T := T) (p := 5)
        (e := EN) (N := N' + 1)
        hh.le h4L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 4) ≤ EN (N' + 1) := by
      show eN (N' + 4)
        ≤ max (max (max (eN (N' + 1)) (eN (N' + 1 + 1))) (eN (N' + 1 + 2)))
              (eN (N' + 1 + 3))
      have heq : N' + 4 = N' + 1 + 3 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((4 * L) * T) * EN 0 ≤ Real.exp ((4 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show |yseq (N' + 4) - y (t₀ + ((N' + 4 : ℕ) : ℝ) * h)|
        ≤ Real.exp ((4 * L) * T) * ε₀
          + T * Real.exp ((4 * L) * T) * (2 * C) * h ^ 5
    have heN_eq :
        eN (N' + 4)
          = |yseq (N' + 4) - y (t₀ + ((N' + 4 : ℕ) : ℝ) * h)| := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
