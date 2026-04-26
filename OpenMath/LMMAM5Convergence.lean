import OpenMath.LMMTruncationOp
import OpenMath.LMMAB6ScalarConvergence
import OpenMath.AdamsMethods

/-! ## Adams--Moulton 5-step Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit Adams--Moulton
5-step method.  The chain follows the AM4 template (cycle 436) one stencil
step up: the implicit update is parameterised by a supplied trajectory
satisfying the AM5 recurrence, the local residual is bounded by seventh-order
Taylor remainders exposed from `LMMAB6ScalarConvergence`, and the global error is
assembled with `lmm_error_bound_from_local_truncation`.

The one-step Lipschitz inequality keeps the new implicit sample on the left
with factor `1 - (475/1440)·h·L`.  The explicit-history weights add up to
`2907/1440`, and we slack the divided growth constant to `5L`. -/

namespace LMM

/-- AM5 trajectory predicate:
`y_{n+5} = y_{n+4} + h(475/1440 f_{n+5} + 1427/1440 f_{n+4}
  - 798/1440 f_{n+3} + 482/1440 f_{n+2} - 173/1440 f_{n+1}
  + 27/1440 f_n)`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM5Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 5)
      = y (n + 4)
        + h * ((475 / 1440 : ℝ) * f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             + (1427 / 1440 : ℝ) * f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             - (798 / 1440 : ℝ) * f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             + (482 / 1440 : ℝ) * f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             - (173 / 1440 : ℝ) * f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             + (27 / 1440 : ℝ) * f (t₀ + (n : ℝ) * h) (y n))

/-- AM5 local truncation operator reduces to the textbook residual
`y(t+5h) - y(t+4h) - h(475/1440 y'(t+5h) + 1427/1440 y'(t+4h)
  - 798/1440 y'(t+3h) + 482/1440 y'(t+2h) - 173/1440 y'(t+h)
  + 27/1440 y'(t))`. -/
theorem am5_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsMoulton5.localTruncationError h t y
      = y (t + 5 * h) - y (t + 4 * h)
          - h * ((475 / 1440 : ℝ) * deriv y (t + 5 * h)
                + (1427 / 1440 : ℝ) * deriv y (t + 4 * h)
                - (798 / 1440 : ℝ) * deriv y (t + 3 * h)
                + (482 / 1440 : ℝ) * deriv y (t + 2 * h)
                - (173 / 1440 : ℝ) * deriv y (t + h)
                + (27 / 1440 : ℝ) * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsMoulton5, Fin.sum_univ_six, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AM5 Lipschitz inequality before dividing by the implicit
new-point factor.  The side condition records the small-step regime used by
the divided form. -/
theorem am5_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (475 / 1440 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM5Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (475 / 1440 : ℝ) * h * L)
        * |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
      ≤ |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
        + (1427 / 1440 : ℝ) * h * L
            * |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
        + (798 / 1440 : ℝ) * h * L
            * |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
        + (482 / 1440 : ℝ) * h * L
            * |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
        + (173 / 1440 : ℝ) * h * L
            * |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
        + (27 / 1440 : ℝ) * h * L
            * |yseq n - y (t₀ + (n : ℝ) * h)|
        + |adamsMoulton5.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  -- Abbreviations.
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set yn3 : ℝ := yseq (n + 3) with hyn3_def
  set yn4 : ℝ := yseq (n + 4) with hyn4_def
  set yn5 : ℝ := yseq (n + 5) with hyn5_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set τ : ℝ := adamsMoulton5.localTruncationError h tn y with hτ_def
  have _hsmall_record : (475 / 1440 : ℝ) * h * L ≤ 1 / 2 := hsmall
  -- AM5 step formula for the supplied implicit trajectory.
  have hstep : yn5
      = yn4
        + h * ((475 / 1440 : ℝ) * f tn5 yn5
             + (1427 / 1440 : ℝ) * f tn4 yn4
             - (798 / 1440 : ℝ) * f tn3 yn3
             + (482 / 1440 : ℝ) * f tn2 yn2
             - (173 / 1440 : ℝ) * f tn1 yn1
             + (27 / 1440 : ℝ) * f tn yn) := by
    simpa [hyn5_def, hyn4_def, hyn3_def, hyn2_def, hyn1_def, hyn_def,
      htn5_def, htn4_def, htn3_def, htn2_def, htn1_def, htn_def] using
      hy.recurrence n
  -- Local truncation residual at `tn`, expressed via `f` along the trajectory.
  have htn1_h : tn + h = tn1 := by
    simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by
    simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by
    simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by
    simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by
    simp [htn_def, htn5_def]; ring
  have hτ_eq : τ = zn5 - zn4
      - h * ((475 / 1440 : ℝ) * f tn5 zn5
             + (1427 / 1440 : ℝ) * f tn4 zn4
             - (798 / 1440 : ℝ) * f tn3 zn3
             + (482 / 1440 : ℝ) * f tn2 zn2
             - (173 / 1440 : ℝ) * f tn1 zn1
             + (27 / 1440 : ℝ) * f tn zn) := by
    show adamsMoulton5.localTruncationError h tn y = _
    rw [am5_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h,
      htn_5h, hyf tn5, hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the implicit global-error increment.
  have halg : yn5 - zn5
      = (yn4 - zn4)
        + (475 / 1440 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
        + (1427 / 1440 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        - (798 / 1440 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        + (482 / 1440 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        - (173 / 1440 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        + (27 / 1440 : ℝ) * h * (f tn yn - f tn zn)
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
  -- Lipschitz bounds on the six `f` increments.
  have hLip5 : |f tn5 yn5 - f tn5 zn5| ≤ L * |yn5 - zn5| :=
    hf tn5 yn5 zn5
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
  have h475_nn : 0 ≤ (475 / 1440 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h1427_nn : 0 ≤ (1427 / 1440 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h798_nn : 0 ≤ (798 / 1440 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h482_nn : 0 ≤ (482 / 1440 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h173_nn : 0 ≤ (173 / 1440 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h27_nn : 0 ≤ (27 / 1440 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h475_abs :
      |(475 / 1440 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
      ≤ (475 / 1440 : ℝ) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg h475_nn]
    calc (475 / 1440 : ℝ) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (475 / 1440 : ℝ) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip5 h475_nn
      _ = (475 / 1440 : ℝ) * h * L * |yn5 - zn5| := by ring
  have h1427_abs :
      |(1427 / 1440 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (1427 / 1440 : ℝ) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h1427_nn]
    calc (1427 / 1440 : ℝ) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (1427 / 1440 : ℝ) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 h1427_nn
      _ = (1427 / 1440 : ℝ) * h * L * |yn4 - zn4| := by ring
  have h798_abs :
      |(798 / 1440 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (798 / 1440 : ℝ) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h798_nn]
    calc (798 / 1440 : ℝ) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (798 / 1440 : ℝ) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h798_nn
      _ = (798 / 1440 : ℝ) * h * L * |yn3 - zn3| := by ring
  have h482_abs :
      |(482 / 1440 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (482 / 1440 : ℝ) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h482_nn]
    calc (482 / 1440 : ℝ) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (482 / 1440 : ℝ) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h482_nn
      _ = (482 / 1440 : ℝ) * h * L * |yn2 - zn2| := by ring
  have h173_abs :
      |(173 / 1440 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (173 / 1440 : ℝ) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h173_nn]
    calc (173 / 1440 : ℝ) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (173 / 1440 : ℝ) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h173_nn
      _ = (173 / 1440 : ℝ) * h * L * |yn1 - zn1| := by ring
  have h27_abs :
      |(27 / 1440 : ℝ) * h * (f tn yn - f tn zn)|
      ≤ (27 / 1440 : ℝ) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h27_nn]
    calc (27 / 1440 : ℝ) * h * |f tn yn - f tn zn|
        ≤ (27 / 1440 : ℝ) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h27_nn
      _ = (27 / 1440 : ℝ) * h * L * |yn - zn| := by ring
  -- Triangle inequality, then move the implicit contribution to the left.
  have htri_terms (A B C D E F G H : ℝ) :
      |A + B + C - D + E - F + G - H|
        ≤ |A| + |B| + |C| + |D| + |E| + |F| + |G| + |H| := by
    have h1 : |A + B + C - D + E - F + G - H|
        ≤ |A + B + C - D + E - F + G| + |H| := abs_sub _ _
    have h2 : |A + B + C - D + E - F + G|
        ≤ |A + B + C - D + E - F| + |G| := abs_add_le _ _
    have h3 : |A + B + C - D + E - F|
        ≤ |A + B + C - D + E| + |F| := abs_sub _ _
    have h4 : |A + B + C - D + E|
        ≤ |A + B + C - D| + |E| := abs_add_le _ _
    have h5 : |A + B + C - D| ≤ |A + B + C| + |D| := abs_sub _ _
    have h6 : |A + B + C| ≤ |A + B| + |C| := abs_add_le _ _
    have h7 : |A + B| ≤ |A| + |B| := abs_add_le _ _
    linarith
  have htri :
      |(yn4 - zn4)
        + (475 / 1440 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
        + (1427 / 1440 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        - (798 / 1440 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        + (482 / 1440 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        - (173 / 1440 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        + (27 / 1440 : ℝ) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn4 - zn4|
          + |(475 / 1440 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(1427 / 1440 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(798 / 1440 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(482 / 1440 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(173 / 1440 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(27 / 1440 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| :=
    htri_terms (yn4 - zn4)
      ((475 / 1440 : ℝ) * h * (f tn5 yn5 - f tn5 zn5))
      ((1427 / 1440 : ℝ) * h * (f tn4 yn4 - f tn4 zn4))
      ((798 / 1440 : ℝ) * h * (f tn3 yn3 - f tn3 zn3))
      ((482 / 1440 : ℝ) * h * (f tn2 yn2 - f tn2 zn2))
      ((173 / 1440 : ℝ) * h * (f tn1 yn1 - f tn1 zn1))
      ((27 / 1440 : ℝ) * h * (f tn yn - f tn zn)) τ
  have hmain :
      |yn5 - zn5|
        ≤ |yn4 - zn4|
          + (475 / 1440 : ℝ) * h * L * |yn5 - zn5|
          + (1427 / 1440 : ℝ) * h * L * |yn4 - zn4|
          + (798 / 1440 : ℝ) * h * L * |yn3 - zn3|
          + (482 / 1440 : ℝ) * h * L * |yn2 - zn2|
          + (173 / 1440 : ℝ) * h * L * |yn1 - zn1|
          + (27 / 1440 : ℝ) * h * L * |yn - zn|
          + |τ| := by
    calc |yn5 - zn5|
        = |(yn4 - zn4)
            + (475 / 1440 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
            + (1427 / 1440 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
            - (798 / 1440 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
            + (482 / 1440 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
            - (173 / 1440 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
            + (27 / 1440 : ℝ) * h * (f tn yn - f tn zn)
            - τ| := by rw [halg]
      _ ≤ |yn4 - zn4|
          + |(475 / 1440 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(1427 / 1440 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(798 / 1440 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(482 / 1440 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(173 / 1440 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(27 / 1440 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| := htri
      _ ≤ |yn4 - zn4|
          + (475 / 1440 : ℝ) * h * L * |yn5 - zn5|
          + (1427 / 1440 : ℝ) * h * L * |yn4 - zn4|
          + (798 / 1440 : ℝ) * h * L * |yn3 - zn3|
          + (482 / 1440 : ℝ) * h * L * |yn2 - zn2|
          + (173 / 1440 : ℝ) * h * L * |yn1 - zn1|
          + (27 / 1440 : ℝ) * h * L * |yn - zn|
          + |τ| := by
        linarith [h475_abs, h1427_abs, h798_abs, h482_abs, h173_abs, h27_abs]
  linarith [hmain]

/-- Divided one-step AM5 error bound.  The explicit AM5 weights contribute
`2907/1440`; after dividing by the implicit `(1 - (475/1440)hL)`
factor, we slacken the max-window growth to `5L` and the residual
coefficient to `2`. -/
theorem am5_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (475 / 1440 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM5Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
      ≤ (1 + h * (5 * L))
            * max (max (max (max |yseq n - y (t₀ + (n : ℝ) * h)|
                                  |yseq (n + 1)
                                      - y (t₀ + ((n : ℝ) + 1) * h)|)
                             |yseq (n + 2)
                                  - y (t₀ + ((n : ℝ) + 2) * h)|)
                        |yseq (n + 3)
                            - y (t₀ + ((n : ℝ) + 3) * h)|)
                  |yseq (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)|
        + 2 * |adamsMoulton5.localTruncationError h
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
  set en5 : ℝ :=
    |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)| with hen5_def
  set τabs : ℝ :=
    |adamsMoulton5.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ := max (max (max (max en en1) en2) en3) en4 with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen_le_E : en ≤ E :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen3_le_E : en3 ≤ E := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen4_le_E : en4 ≤ E := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 144 / 95 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (475 / 1440 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (475 / 1440 : ℝ) * h * L) * en5
        ≤ en4
          + (1427 / 1440 : ℝ) * h * L * en4
          + (798 / 1440 : ℝ) * h * L * en3
          + (482 / 1440 : ℝ) * h * L * en2
          + (173 / 1440 : ℝ) * h * L * en1
          + (27 / 1440 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hτabs_def]
      using
      (am5_one_step_lipschitz (h := h) (L := L) hh hsmall hf t₀ hy y hyf n)
  have h1427_nn : 0 ≤ (1427 / 1440 : ℝ) * h * L := by positivity
  have h798_nn : 0 ≤ (798 / 1440 : ℝ) * h * L := by positivity
  have h482_nn : 0 ≤ (482 / 1440 : ℝ) * h * L := by positivity
  have h173_nn : 0 ≤ (173 / 1440 : ℝ) * h * L := by positivity
  have h27_nn : 0 ≤ (27 / 1440 : ℝ) * h * L := by positivity
  have h1427_le :
      (1427 / 1440 : ℝ) * h * L * en4
        ≤ (1427 / 1440 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen4_le_E h1427_nn
  have h798_le :
      (798 / 1440 : ℝ) * h * L * en3
        ≤ (798 / 1440 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen3_le_E h798_nn
  have h482_le :
      (482 / 1440 : ℝ) * h * L * en2
        ≤ (482 / 1440 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen2_le_E h482_nn
  have h173_le :
      (173 / 1440 : ℝ) * h * L * en1
        ≤ (173 / 1440 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen1_le_E h173_nn
  have h27_le :
      (27 / 1440 : ℝ) * h * L * en
        ≤ (27 / 1440 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen_le_E h27_nn
  have hR_le :
      en4
          + (1427 / 1440 : ℝ) * h * L * en4
          + (798 / 1440 : ℝ) * h * L * en3
          + (482 / 1440 : ℝ) * h * L * en2
          + (173 / 1440 : ℝ) * h * L * en1
          + (27 / 1440 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (2907 / 1440 : ℝ) * (h * L)) * E + τabs := by
    have h_alg :
        E + (1427 / 1440 : ℝ) * h * L * E
            + (798 / 1440 : ℝ) * h * L * E
            + (482 / 1440 : ℝ) * h * L * E
            + (173 / 1440 : ℝ) * h * L * E
            + (27 / 1440 : ℝ) * h * L * E + τabs
          = (1 + (2907 / 1440 : ℝ) * (h * L)) * E + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (2907 / 1440 : ℝ) * (h * L)
        ≤ (1 - (475 / 1440 : ℝ) * h * L) * (1 + h * (5 * L)) := by
    nlinarith [hx_nn, hx_small, hsmall]
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (475 / 1440 : ℝ) * h * L) * 2 := by
    nlinarith [hsmall]
  have hE_part :
      (1 + (2907 / 1440 : ℝ) * (h * L)) * E
        ≤ ((1 - (475 / 1440 : ℝ) * h * L) * (1 + h * (5 * L))) * E :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (475 / 1440 : ℝ) * h * L) * 2) * τabs :=
    by simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (2907 / 1440 : ℝ) * (h * L)) * E + τabs
        ≤ (1 - (475 / 1440 : ℝ) * h * L)
            * ((1 + h * (5 * L)) * E + 2 * τabs) := by
    have hsplit :
        (1 - (475 / 1440 : ℝ) * h * L)
            * ((1 + h * (5 * L)) * E + 2 * τabs)
          = ((1 - (475 / 1440 : ℝ) * h * L) * (1 + h * (5 * L))) * E
              + ((1 - (475 / 1440 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (475 / 1440 : ℝ) * h * L) * en5
        ≤ (1 - (475 / 1440 : ℝ) * h * L)
            * ((1 + h * (5 * L)) * E + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  have hcancel :
      en5 ≤ (1 + h * (5 * L)) * E + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  exact hcancel

/-- Max-norm AM5 one-step recurrence on the rolling 5-window
`(en, en1, en2, en3, en4)`. -/
theorem am5_one_step_error_pair_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (475 / 1440 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM5Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max
          |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
        |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
        |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
      ≤ (1 + h * (5 * L))
            * max (max (max (max |yseq n - y (t₀ + (n : ℝ) * h)|
                                  |yseq (n + 1)
                                      - y (t₀ + ((n : ℝ) + 1) * h)|)
                             |yseq (n + 2)
                                  - y (t₀ + ((n : ℝ) + 2) * h)|)
                        |yseq (n + 3)
                            - y (t₀ + ((n : ℝ) + 3) * h)|)
                  |yseq (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)|
        + 2 * |adamsMoulton5.localTruncationError h
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
  set en5 : ℝ :=
    |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)| with hen5_def
  set τabs : ℝ :=
    |adamsMoulton5.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ := max (max (max (max en en1) en2) en3) en4 with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen3_le_E : en3 ≤ E := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen4_le_E : en4 ≤ E := le_max_right _ _
  have h5hL_nn : 0 ≤ h * (5 * L) := by positivity
  -- en5 bound from `am5_one_step_error_bound`.
  have hen5_bd :
      en5 ≤ (1 + h * (5 * L)) * E + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hτabs_def,
      hE_def]
      using
      (am5_one_step_error_bound (h := h) (L := L) hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : E ≤ (1 + h * (5 * L)) * E := by
    have hone : (1 : ℝ) * E ≤ (1 + h * (5 * L)) * E :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (5 * L)) * E + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (5 * L)) * E + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (5 * L)) * E + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  have hen4_bd : en4 ≤ (1 + h * (5 * L)) * E + 2 * τabs := by
    linarith [hen4_le_E, hE_le_grow]
  exact max_le (max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd) hen4_bd)
    hen5_bd

/-- Pointwise AM5 truncation residual bound.  The residual expands as
`R_y(5) - R_y(4) - (475h/1440)·R_y'(5) - (1427h/1440)·R_y'(4)
  + (798h/1440)·R_y'(3) - (482h/1440)·R_y'(2)
  + (173h/1440)·R_y'(1)`.  The exact triangle-bound coefficient is
`23325037/725760 ≈ 32.14`, slackened to `33`. -/
theorem am5_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 7 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 7 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 5 * h) - y (t + 4 * h)
        - h * ((475 / 1440) * deriv y (t + 5 * h)
              + (1427 / 1440) * deriv y (t + 4 * h)
              - (798 / 1440) * deriv y (t + 3 * h)
              + (482 / 1440) * deriv y (t + 2 * h)
              - (173 / 1440) * deriv y (t + h)
              + (27 / 1440) * deriv y t)|
      ≤ (33 : ℝ) * M * h ^ 7 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  -- R_y(4) and R_y(5), both expanded to sixth order around `t`.
  have hRy4 :=
    y_seventh_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRy5 :=
    y_seventh_order_taylor_remainder hy hbnd ht ht5h h5h
  -- Remainders for `y'` at h, 2h, 3h, 4h, 5h.
  have hRyp1 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht ht5h h5h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y4 := y (t + 4 * h) with hy4_def
  set y5 := y (t + 5 * h) with hy5_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  -- Algebraic identity for the AM5 residual.
  have hLTE_eq :
      y5 - y4 - h * ((475 / 1440) * d5 + (1427 / 1440) * d4
                    - (798 / 1440) * d3 + (482 / 1440) * d2
                    - (173 / 1440) * d1 + (27 / 1440) * d0)
        = (y5 - y0 - (5 * h) * d0
              - (5 * h) ^ 2 / 2 * dd
              - (5 * h) ^ 3 / 6 * ddd
              - (5 * h) ^ 4 / 24 * dddd
              - (5 * h) ^ 5 / 120 * ddddd
              - (5 * h) ^ 6 / 720 * dddddd)
          - (y4 - y0 - (4 * h) * d0
              - (4 * h) ^ 2 / 2 * dd
              - (4 * h) ^ 3 / 6 * ddd
              - (4 * h) ^ 4 / 24 * dddd
              - (4 * h) ^ 5 / 120 * ddddd
              - (4 * h) ^ 6 / 720 * dddddd)
          - (475 * h / 1440)
              * (d5 - d0 - (5 * h) * dd
                  - (5 * h) ^ 2 / 2 * ddd
                  - (5 * h) ^ 3 / 6 * dddd
                  - (5 * h) ^ 4 / 24 * ddddd
                  - (5 * h) ^ 5 / 120 * dddddd)
          - (1427 * h / 1440)
              * (d4 - d0 - (4 * h) * dd
                  - (4 * h) ^ 2 / 2 * ddd
                  - (4 * h) ^ 3 / 6 * dddd
                  - (4 * h) ^ 4 / 24 * ddddd
                  - (4 * h) ^ 5 / 120 * dddddd)
          + (798 * h / 1440)
              * (d3 - d0 - (3 * h) * dd
                  - (3 * h) ^ 2 / 2 * ddd
                  - (3 * h) ^ 3 / 6 * dddd
                  - (3 * h) ^ 4 / 24 * ddddd
                  - (3 * h) ^ 5 / 120 * dddddd)
          - (482 * h / 1440)
              * (d2 - d0 - (2 * h) * dd
                  - (2 * h) ^ 2 / 2 * ddd
                  - (2 * h) ^ 3 / 6 * dddd
                  - (2 * h) ^ 4 / 24 * ddddd
                  - (2 * h) ^ 5 / 120 * dddddd)
          + (173 * h / 1440)
              * (d1 - d0 - h * dd
                  - h ^ 2 / 2 * ddd
                  - h ^ 3 / 6 * dddd
                  - h ^ 4 / 24 * ddddd
                  - h ^ 5 / 120 * dddddd) := by ring
  rw [hLTE_eq]
  -- Triangle inequality.
  set A := y5 - y0 - (5 * h) * d0
            - (5 * h) ^ 2 / 2 * dd
            - (5 * h) ^ 3 / 6 * ddd
            - (5 * h) ^ 4 / 24 * dddd
            - (5 * h) ^ 5 / 120 * ddddd
            - (5 * h) ^ 6 / 720 * dddddd with hA_def
  set B := y4 - y0 - (4 * h) * d0
            - (4 * h) ^ 2 / 2 * dd
            - (4 * h) ^ 3 / 6 * ddd
            - (4 * h) ^ 4 / 24 * dddd
            - (4 * h) ^ 5 / 120 * ddddd
            - (4 * h) ^ 6 / 720 * dddddd with hB_def
  set C := d5 - d0 - (5 * h) * dd
            - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd
            - (5 * h) ^ 5 / 120 * dddddd with hC_def
  set D := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd
            - (4 * h) ^ 5 / 120 * dddddd with hD_def
  set E := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd
            - (3 * h) ^ 5 / 120 * dddddd with hE_def
  set F := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd
            - (2 * h) ^ 5 / 120 * dddddd with hF_def
  set G := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd
            - h ^ 5 / 120 * dddddd with hG_def
  have h475h_nn : 0 ≤ 475 * h / 1440 := by positivity
  have h1427h_nn : 0 ≤ 1427 * h / 1440 := by positivity
  have h798h_nn : 0 ≤ 798 * h / 1440 := by positivity
  have h482h_nn : 0 ≤ 482 * h / 1440 := by positivity
  have h173h_nn : 0 ≤ 173 * h / 1440 := by positivity
  have habs475 : |(475 * h / 1440) * C| = (475 * h / 1440) * |C| := by
    rw [abs_mul, abs_of_nonneg h475h_nn]
  have habs1427 : |(1427 * h / 1440) * D| = (1427 * h / 1440) * |D| := by
    rw [abs_mul, abs_of_nonneg h1427h_nn]
  have habs798 : |(798 * h / 1440) * E| = (798 * h / 1440) * |E| := by
    rw [abs_mul, abs_of_nonneg h798h_nn]
  have habs482 : |(482 * h / 1440) * F| = (482 * h / 1440) * |F| := by
    rw [abs_mul, abs_of_nonneg h482h_nn]
  have habs173 : |(173 * h / 1440) * G| = (173 * h / 1440) * |G| := by
    rw [abs_mul, abs_of_nonneg h173h_nn]
  have htri : |A - B - (475 * h / 1440) * C - (1427 * h / 1440) * D
                  + (798 * h / 1440) * E - (482 * h / 1440) * F
                  + (173 * h / 1440) * G|
      ≤ |A| + |B| + (475 * h / 1440) * |C| + (1427 * h / 1440) * |D|
          + (798 * h / 1440) * |E| + (482 * h / 1440) * |F|
          + (173 * h / 1440) * |G| := by
    have h1 : |A - B - (475 * h / 1440) * C - (1427 * h / 1440) * D
                  + (798 * h / 1440) * E - (482 * h / 1440) * F
                  + (173 * h / 1440) * G|
        ≤ |A - B - (475 * h / 1440) * C - (1427 * h / 1440) * D
              + (798 * h / 1440) * E - (482 * h / 1440) * F|
            + |(173 * h / 1440) * G| := abs_add_le _ _
    have h2 : |A - B - (475 * h / 1440) * C - (1427 * h / 1440) * D
                  + (798 * h / 1440) * E - (482 * h / 1440) * F|
        ≤ |A - B - (475 * h / 1440) * C - (1427 * h / 1440) * D
              + (798 * h / 1440) * E| + |(482 * h / 1440) * F| :=
      abs_sub _ _
    have h3 : |A - B - (475 * h / 1440) * C - (1427 * h / 1440) * D
                  + (798 * h / 1440) * E|
        ≤ |A - B - (475 * h / 1440) * C - (1427 * h / 1440) * D|
            + |(798 * h / 1440) * E| := abs_add_le _ _
    have h4 : |A - B - (475 * h / 1440) * C - (1427 * h / 1440) * D|
        ≤ |A - B - (475 * h / 1440) * C| + |(1427 * h / 1440) * D| :=
      abs_sub _ _
    have h5 : |A - B - (475 * h / 1440) * C|
        ≤ |A - B| + |(475 * h / 1440) * C| := abs_sub _ _
    have h6 : |A - B| ≤ |A| + |B| := abs_sub _ _
    linarith [habs475.le, habs475.ge, habs1427.le, habs1427.ge,
      habs798.le, habs798.ge, habs482.le, habs482.ge, habs173.le, habs173.ge]
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 5040 * (5 * h) ^ 7 := hRy5
  have hB_bd : |B| ≤ M / 5040 * (4 * h) ^ 7 := hRy4
  have hC_bd : |C| ≤ M / 720 * (5 * h) ^ 6 := hRyp5
  have hD_bd : |D| ≤ M / 720 * (4 * h) ^ 6 := hRyp4
  have hE_bd : |E| ≤ M / 720 * (3 * h) ^ 6 := hRyp3
  have hF_bd : |F| ≤ M / 720 * (2 * h) ^ 6 := hRyp2
  have hG_bd : |G| ≤ M / 720 * h ^ 6 := hRyp1
  -- Multiply scaled bounds.
  have hC_scaled :
      (475 * h / 1440) * |C| ≤ (475 * h / 1440) * (M / 720 * (5 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hC_bd h475h_nn
  have hD_scaled :
      (1427 * h / 1440) * |D| ≤
        (1427 * h / 1440) * (M / 720 * (4 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hD_bd h1427h_nn
  have hE_scaled :
      (798 * h / 1440) * |E| ≤ (798 * h / 1440) * (M / 720 * (3 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hE_bd h798h_nn
  have hF_scaled :
      (482 * h / 1440) * |F| ≤ (482 * h / 1440) * (M / 720 * (2 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hF_bd h482h_nn
  have hG_scaled :
      (173 * h / 1440) * |G| ≤ (173 * h / 1440) * (M / 720 * h ^ 6) :=
    mul_le_mul_of_nonneg_left hG_bd h173h_nn
  -- Sum of upper bounds = 23325037/725760 ≈ 32.14. Slacken to 33.
  have hbound_alg :
      M / 5040 * (5 * h) ^ 7 + M / 5040 * (4 * h) ^ 7
        + (475 * h / 1440) * (M / 720 * (5 * h) ^ 6)
        + (1427 * h / 1440) * (M / 720 * (4 * h) ^ 6)
        + (798 * h / 1440) * (M / 720 * (3 * h) ^ 6)
        + (482 * h / 1440) * (M / 720 * (2 * h) ^ 6)
        + (173 * h / 1440) * (M / 720 * h ^ 6)
        = (23325037 / 725760 : ℝ) * M * h ^ 7 := by ring
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh7_nn : 0 ≤ h ^ 7 := by positivity
  have hMh7_nn : 0 ≤ M * h ^ 7 := mul_nonneg hMnn hh7_nn
  have hslack : (23325037 / 725760 : ℝ) * M * h ^ 7 ≤ 33 * M * h ^ 7 := by
    have hle : (23325037 / 725760 : ℝ) ≤ 33 := by norm_num
    have := mul_le_mul_of_nonneg_right hle hMh7_nn
    linarith [this]
  linarith [htri, hA_bd, hB_bd, hC_scaled, hD_scaled, hE_scaled, hF_scaled,
    hG_scaled, hbound_alg.le, hbound_alg.ge, hslack]

/-- Uniform bound on the AM5 one-step truncation residual on a finite
horizon, given a `C^7` exact solution. -/
theorem am5_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 7 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 5) * h ≤ T →
        |adamsMoulton5.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 7 := by
  -- Choose a compact sample interval `[t₀, t₀ + T + 1]` covering all `t + kh`
  -- with `k ≤ 5` (using `(n+5)*h ≤ T` and `h ≤ 1`).
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_seven_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(33 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 5) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 5) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 5) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 5) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 5) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h = ((n : ℝ) + 5) * h := by ring
    linarith
  -- Rewrite the LTE in textbook form.
  rw [am5_localTruncationError_eq]
  show |y (t + 5 * h) - y (t + 4 * h)
      - h * ((475 / 1440) * deriv y (t + 5 * h)
            + (1427 / 1440) * deriv y (t + 4 * h)
            - (798 / 1440) * deriv y (t + 3 * h)
            + (482 / 1440) * deriv y (t + 2 * h)
            - (173 / 1440) * deriv y (t + h)
            + (27 / 1440) * deriv y t)|
    ≤ 33 * M * h ^ 7
  exact am5_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem hh.le

/-- Headline AM5 global error bound.  Given a supplied AM5 trajectory and
starting errors bounded by `ε₀`, the scalar global error is `O(ε₀ + h^6)` on
a finite horizon. -/
theorem am5_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 7 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (475 / 1440 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsAM5Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      |yseq 2 - y (t₀ + 2 * h)| ≤ ε₀ →
      |yseq 3 - y (t₀ + 3 * h)| ≤ ε₀ →
      |yseq 4 - y (t₀ + 4 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 4) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((5 * L) * T) * ε₀ + K * h ^ 6 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am5_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((5 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => |yseq k - y (t₀ + (k : ℝ) * h)| with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (eN k) (eN (k + 1))) (eN (k + 2))) (eN (k + 3)))
      (eN (k + 4))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (heN_nn k))))
  -- Initial bound: EN 0 ≤ ε₀.
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4) ≤ ε₀
    refine max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_
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
    · show |yseq 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]; simpa using he4_bd
  have h5L_nn : (0 : ℝ) ≤ 5 * L := by linarith
  -- The general recurrence: when (n + 5) * h ≤ T,
  -- EN (n+1) ≤ (1 + h*(5L)) * EN n + 2*C*h^7.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 5) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (5 * L)) * EN n + (2 * C) * h ^ 7 := by
    intro n hnh_le
    have honestep := am5_one_step_error_pair_bound
      (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hcast4 : ((n + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 4 := by
      push_cast; ring
    have hcast5 : ((n + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 5 := by
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
    have heq_eN_n5 : eN (n + 1 + 1 + 1 + 1 + 1)
        = |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)| := by
      show |_ - _| = _
      rw [hcast5]
    show max (max (max (max (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * (5 * L))
            * max (max (max (max (eN n) (eN (n + 1))) (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1))
          + (2 * C) * h ^ 7
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5]
    have h2τ : 2 * |adamsMoulton5.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (2 * C) * h ^ 7 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith [this]
    linarith [honestep, h2τ]
  -- Base cases N = 0, 1, 2, 3, 4 are direct from the starting bounds.
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((5 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((5 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh6_nn : 0 ≤ h ^ 6 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((5 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((5 * L) * T) * ε₀
            + T * Real.exp ((5 * L) * T) * (2 * C) * h ^ 6 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((5 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((5 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh6_nn : 0 ≤ T * Real.exp ((5 * L) * T) * (2 * C) * h ^ 6 :=
      mul_nonneg hKnn hh6_nn
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
  | 4, _ =>
    have hbase : |yseq 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]; simpa using he4_bd
    exact hbase_to_headline _ hbase
  | N' + 5, hNh =>
    -- Apply Gronwall to EN at index N'+1, then use EN_{N'+1} ≥ e_{N'+5}.
    have hcast : (((N' + 5 : ℕ) : ℝ) + 4) = (N' : ℝ) + 9 := by
      push_cast; ring
    have hN_hyp : ((N' : ℝ) + 9) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (5 * L)) * EN n + (2 * C) * h ^ (6 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (6 + 1) = (2 * C) * h ^ 7 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 5 ≤ (N' : ℝ) + 9 := by linarith
      have h_mul : ((n : ℝ) + 5) * h ≤ ((N' : ℝ) + 9) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have hle : (N' : ℝ) + 1 ≤ (N' : ℝ) + 9 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 5 * L) (C := 2 * C) (T := T) (p := 6)
        (e := EN) (N := N' + 1)
        hh.le h5L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 5) ≤ EN (N' + 1) := by
      show eN (N' + 5)
        ≤ max (max (max (max (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4))
      have heq : N' + 5 = N' + 1 + 4 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((5 * L) * T) * EN 0 ≤ Real.exp ((5 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show |yseq (N' + 5) - y (t₀ + ((N' + 5 : ℕ) : ℝ) * h)|
        ≤ Real.exp ((5 * L) * T) * ε₀
          + T * Real.exp ((5 * L) * T) * (2 * C) * h ^ 6
    have heN_eq :
        eN (N' + 5)
          = |yseq (N' + 5) - y (t₀ + ((N' + 5 : ℕ) : ℝ) * h)| := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
