import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB3Convergence

/-! ## Adams--Moulton 2-step Quantitative Convergence Chain (Iserles §1.2)

This file starts the quantitative scalar convergence chain for the implicit
Adams--Moulton 2-step method.  Unlike the explicit Adams--Bashforth chains, the
implicit update is parameterised by a supplied trajectory satisfying the AM2
recurrence; fixed-point existence for that trajectory is kept as a separate
frontier theorem.
-/

namespace LMM

/-- AM2 trajectory predicate:
`y_{n+2} = y_{n+1} + h(5/12 f_{n+2} + 8/12 f_{n+1} - 1/12 f_n)`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM2Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 2)
      = y (n + 1)
        + h * ((5 / 12 : ℝ) * f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             + (8 / 12 : ℝ) * f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             - (1 / 12 : ℝ) * f (t₀ + (n : ℝ) * h) (y n))

/-- Existence of an AM2 trajectory from two starting values under the usual
implicit-step contraction hypothesis.  This Banach fixed-point construction is
not part of the cycle-433 error-analysis chain. -/
theorem am2Trajectory_exists
    {h L : ℝ} {f : ℝ → ℝ → ℝ} (t₀ y₀ y₁ : ℝ)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hcontract : (5 / 12 : ℝ) * h * L < 1) :
    ∃ y : ℕ → ℝ, y 0 = y₀ ∧ y 1 = y₁ ∧ IsAM2Trajectory h f t₀ y := by
  sorry

/-- AM2 local truncation operator reduces to the textbook residual
`y(t+2h) - y(t+h) - h(5/12 y'(t+2h) + 8/12 y'(t+h) - 1/12 y'(t))`. -/
theorem am2_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsMoulton2.localTruncationError h t y
      = y (t + 2 * h) - y (t + h)
          - h * ((5 / 12 : ℝ) * deriv y (t + 2 * h)
                + (8 / 12 : ℝ) * deriv y (t + h)
                - (1 / 12 : ℝ) * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsMoulton2, Fin.sum_univ_three, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AM2 Lipschitz inequality before dividing by the implicit
new-point factor.  The side condition records the small-step regime used by the
divided form. -/
theorem am2_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (5 / 12 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM2Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (5 / 12 : ℝ) * h * L)
        * |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
      ≤ |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
        + (8 / 12 : ℝ) * h * L
            * |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
        + (1 / 12 : ℝ) * h * L
            * |yseq n - y (t₀ + (n : ℝ) * h)|
        + |adamsMoulton2.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  -- Abbreviations.
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set τ : ℝ := adamsMoulton2.localTruncationError h tn y with hτ_def
  have _hsmall_record : (5 / 12 : ℝ) * h * L ≤ 1 / 2 := hsmall
  -- AM2 step formula for the supplied implicit trajectory.
  have hstep : yn2
      = yn1
        + h * ((5 / 12 : ℝ) * f tn2 yn2
             + (8 / 12 : ℝ) * f tn1 yn1
             - (1 / 12 : ℝ) * f tn yn) := by
    simpa [hyn2_def, hyn1_def, hyn_def, htn2_def, htn1_def, htn_def]
      using hy.recurrence n
  -- Local truncation residual at `tn`, expressed via `f` along the trajectory.
  have htn1_h : tn + h = tn1 := by
    simp [htn_def, htn1_def]
    ring
  have htn_2h : tn + 2 * h = tn2 := by
    simp [htn_def, htn2_def]
    ring
  have hτ_eq : τ = zn2 - zn1
      - h * ((5 / 12 : ℝ) * f tn2 zn2
             + (8 / 12 : ℝ) * f tn1 zn1
             - (1 / 12 : ℝ) * f tn zn) := by
    show adamsMoulton2.localTruncationError h tn y = _
    rw [am2_localTruncationError_eq, htn1_h, htn_2h,
      hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the implicit global-error increment.
  have halg : yn2 - zn2
      = (yn1 - zn1)
        + (5 / 12 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        + (8 / 12 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        - (1 / 12 : ℝ) * h * (f tn yn - f tn zn)
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    ring
  -- Lipschitz bounds on the three `f` increments.
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| :=
    hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| :=
    hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| :=
    hf tn yn zn
  have h5_nn : 0 ≤ (5 / 12 : ℝ) * h :=
    mul_nonneg (by norm_num) hh
  have h8_nn : 0 ≤ (8 / 12 : ℝ) * h :=
    mul_nonneg (by norm_num) hh
  have h1_nn : 0 ≤ (1 / 12 : ℝ) * h :=
    mul_nonneg (by norm_num) hh
  have h5_abs :
      |(5 / 12 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (5 / 12 : ℝ) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h5_nn]
    calc (5 / 12 : ℝ) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (5 / 12 : ℝ) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h5_nn
      _ = (5 / 12 : ℝ) * h * L * |yn2 - zn2| := by ring
  have h8_abs :
      |(8 / 12 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (8 / 12 : ℝ) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h8_nn]
    calc (8 / 12 : ℝ) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (8 / 12 : ℝ) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h8_nn
      _ = (8 / 12 : ℝ) * h * L * |yn1 - zn1| := by ring
  have h1_abs :
      |(1 / 12 : ℝ) * h * (f tn yn - f tn zn)|
      ≤ (1 / 12 : ℝ) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h1_nn]
    calc (1 / 12 : ℝ) * h * |f tn yn - f tn zn|
        ≤ (1 / 12 : ℝ) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h1_nn
      _ = (1 / 12 : ℝ) * h * L * |yn - zn| := by ring
  -- Triangle inequality, then move the implicit contribution to the left.
  have htri_terms (A B C D E : ℝ) :
      |A + B + C - D - E| ≤ |A| + |B| + |C| + |D| + |E| := by
    have h1 : |A + B + C - D - E| ≤ |A + B + C - D| + |E| :=
      abs_sub _ _
    have h2 : |A + B + C - D| ≤ |A + B + C| + |D| :=
      abs_sub _ _
    have h3 : |A + B + C| ≤ |A + B| + |C| :=
      abs_add_le _ _
    have h4 : |A + B| ≤ |A| + |B| :=
      abs_add_le _ _
    linarith
  have htri :
      |(yn1 - zn1)
        + (5 / 12 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        + (8 / 12 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        - (1 / 12 : ℝ) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn1 - zn1|
          + |(5 / 12 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(8 / 12 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(1 / 12 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| :=
    htri_terms (yn1 - zn1)
      ((5 / 12 : ℝ) * h * (f tn2 yn2 - f tn2 zn2))
      ((8 / 12 : ℝ) * h * (f tn1 yn1 - f tn1 zn1))
      ((1 / 12 : ℝ) * h * (f tn yn - f tn zn)) τ
  have hmain :
      |yn2 - zn2|
        ≤ |yn1 - zn1|
          + (5 / 12 : ℝ) * h * L * |yn2 - zn2|
          + (8 / 12 : ℝ) * h * L * |yn1 - zn1|
          + (1 / 12 : ℝ) * h * L * |yn - zn|
          + |τ| := by
    calc |yn2 - zn2|
        = |(yn1 - zn1)
            + (5 / 12 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
            + (8 / 12 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
            - (1 / 12 : ℝ) * h * (f tn yn - f tn zn)
            - τ| := by rw [halg]
      _ ≤ |yn1 - zn1|
          + |(5 / 12 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(8 / 12 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(1 / 12 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| := htri
      _ ≤ |yn1 - zn1|
          + (5 / 12 : ℝ) * h * L * |yn2 - zn2|
          + (8 / 12 : ℝ) * h * L * |yn1 - zn1|
          + (1 / 12 : ℝ) * h * L * |yn - zn|
          + |τ| := by
        linarith [h5_abs, h8_abs, h1_abs]
  linarith [hmain]

/-- Divided one-step AM2 error bound.  The effective Lipschitz constant is
slackened to `3L`; under `(5/12)hL ≤ 1/2`, the local residual coefficient is
bounded by `2`. -/
theorem am2_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (5 / 12 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM2Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
      ≤ (1 + h * (3 * L))
            * max |yseq n - y (t₀ + (n : ℝ) * h)|
                  |yseq (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)|
        + 2 * |adamsMoulton2.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |yseq n - y (t₀ + (n : ℝ) * h)| with hen_def
  set en1 : ℝ :=
    |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| with hen1_def
  set en2 : ℝ :=
    |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| with hen2_def
  set τabs : ℝ :=
    |adamsMoulton2.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ := max en en1 with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E := le_trans hen_nn (le_max_left _ _)
  have hen_le_E : en ≤ E := le_max_left _ _
  have hen1_le_E : en1 ≤ E := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 6 / 5 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (5 / 12 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (5 / 12 : ℝ) * h * L) * en2
        ≤ en1
          + (8 / 12 : ℝ) * h * L * en1
          + (1 / 12 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hτabs_def] using
      (am2_one_step_lipschitz (h := h) (L := L) hh hsmall hf t₀ hy y hyf n)
  have h8_nn : 0 ≤ (8 / 12 : ℝ) * h * L := by positivity
  have h1_nn : 0 ≤ (1 / 12 : ℝ) * h * L := by positivity
  have h8_le :
      (8 / 12 : ℝ) * h * L * en1
        ≤ (8 / 12 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen1_le_E h8_nn
  have h1_le :
      (1 / 12 : ℝ) * h * L * en
        ≤ (1 / 12 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen_le_E h1_nn
  have hR_le :
      en1
          + (8 / 12 : ℝ) * h * L * en1
          + (1 / 12 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (3 / 4 : ℝ) * (h * L)) * E + τabs := by
    have h_alg :
        E + (8 / 12 : ℝ) * h * L * E
            + (1 / 12 : ℝ) * h * L * E + τabs
          = (1 + (3 / 4 : ℝ) * (h * L)) * E + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (3 / 4 : ℝ) * (h * L)
        ≤ (1 - (5 / 12 : ℝ) * h * L) * (1 + h * (3 * L)) := by
    nlinarith [hx_nn, hx_small]
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (5 / 12 : ℝ) * h * L) * 2 := by
    nlinarith [hsmall]
  have hE_part :
      (1 + (3 / 4 : ℝ) * (h * L)) * E
        ≤ ((1 - (5 / 12 : ℝ) * h * L) * (1 + h * (3 * L))) * E :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (5 / 12 : ℝ) * h * L) * 2) * τabs :=
    by simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (3 / 4 : ℝ) * (h * L)) * E + τabs
        ≤ (1 - (5 / 12 : ℝ) * h * L)
            * ((1 + h * (3 * L)) * E + 2 * τabs) := by
    have hsplit :
        (1 - (5 / 12 : ℝ) * h * L)
            * ((1 + h * (3 * L)) * E + 2 * τabs)
          = ((1 - (5 / 12 : ℝ) * h * L) * (1 + h * (3 * L))) * E
              + ((1 - (5 / 12 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (5 / 12 : ℝ) * h * L) * en2
        ≤ (1 - (5 / 12 : ℝ) * h * L)
            * ((1 + h * (3 * L)) * E + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  have hcancel :
      en2 ≤ (1 + h * (3 * L)) * E + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  exact hcancel

/-- Uniform AM2 local residual bound on a finite horizon.  The planned
pointwise coefficient from the Taylor-remainder decomposition is `11/8`; this
declaration keeps the public surface existential, matching the AB chains. -/
theorem am2_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 2) * h ≤ T →
        |adamsMoulton2.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 4 := by
  sorry

/-- Headline AM2 global error bound.  Given a supplied AM2 trajectory and
starting errors bounded by `ε₀`, the scalar global error is `O(ε₀ + h^3)` on a
finite horizon. -/
theorem am2_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 4 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (5 / 12 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsAM2Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 1) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((3 * L) * T) * ε₀ + K * h ^ 3 := by
  sorry

end LMM
