import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAM7VectorConvergence

/-! ## Adams--Moulton 8-step Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the AM8 scalar quantitative convergence chain in
`OpenMath/LMMAM8Convergence.lean`.  The implicit AM8 update is parameterised
by a supplied trajectory; existence of such a trajectory is a separate
fixed-point problem and is not part of this chain.

This cycle (454) lands the trajectory predicate, the textbook local truncation
residual unfolding, and the supporting tenth-order vector Taylor ladder
(promoted public in `LMMAM7VectorConvergence`).  The remaining pieces of the
chain — the one-step Lipschitz/error recurrence, the ten-term residual algebra
split, the pointwise/local residual bound, and the global headline — are
scoped to a follow-up cycle: they require porting the AM8 scalar
(`LMMAM8Convergence`) chain at full size, plus the kernel-discipline
`clear_value` + four-helper extraction pattern from cycle 444's AM7 vector
chain.
-/

namespace LMM

/-- AM8 vector trajectory predicate.  The new value appears inside `f`, so
existence of such a trajectory is a separate fixed-point problem. -/
structure IsAM8TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 8)
      = y (n + 7)
        + h • ((1070017 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h) (y (n + 8))
             + (4467094 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h) (y (n + 7))
             - (4604594 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             + (5595358 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             - (5033120 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             + (3146338 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             - (1291214 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             + (312874 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             - (33953 / 3628800 : ℝ) • f (t₀ + (n : ℝ) * h) (y n))

/-- Textbook AM8 vector residual: the value of the local truncation error of
the AM8 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def am8VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 8 * h) - y (t + 7 * h)
    - h • ((1070017 / 3628800 : ℝ) • deriv y (t + 8 * h)
          + (4467094 / 3628800 : ℝ) • deriv y (t + 7 * h)
          - (4604594 / 3628800 : ℝ) • deriv y (t + 6 * h)
          + (5595358 / 3628800 : ℝ) • deriv y (t + 5 * h)
          - (5033120 / 3628800 : ℝ) • deriv y (t + 4 * h)
          + (3146338 / 3628800 : ℝ) • deriv y (t + 3 * h)
          - (1291214 / 3628800 : ℝ) • deriv y (t + 2 * h)
          + (312874 / 3628800 : ℝ) • deriv y (t + h)
          - (33953 / 3628800 : ℝ) • deriv y t)

theorem am8Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am8VecResidual h t y
      = y (t + 8 * h) - y (t + 7 * h)
          - h • ((1070017 / 3628800 : ℝ) • deriv y (t + 8 * h)
                + (4467094 / 3628800 : ℝ) • deriv y (t + 7 * h)
                - (4604594 / 3628800 : ℝ) • deriv y (t + 6 * h)
                + (5595358 / 3628800 : ℝ) • deriv y (t + 5 * h)
                - (5033120 / 3628800 : ℝ) • deriv y (t + 4 * h)
                + (3146338 / 3628800 : ℝ) • deriv y (t + 3 * h)
                - (1291214 / 3628800 : ℝ) • deriv y (t + 2 * h)
                + (312874 / 3628800 : ℝ) • deriv y (t + h)
                - (33953 / 3628800 : ℝ) • deriv y t) := by
  rfl

theorem am8Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM8TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (1070017 / 3628800 : ℝ) * h * L)
        * ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
      ≤ ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
        + (4467094 / 3628800 : ℝ) * h * L
            * ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
        + (4604594 / 3628800 : ℝ) * h * L
            * ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (5595358 / 3628800 : ℝ) * h * L
            * ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (5033120 / 3628800 : ℝ) * h * L
            * ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (3146338 / 3628800 : ℝ) * h * L
            * ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (1291214 / 3628800 : ℝ) * h * L
            * ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (312874 / 3628800 : ℝ) * h * L
            * ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (33953 / 3628800 : ℝ) * h * L
            * ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + ‖am8VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set yn2 : E := yseq (n + 2) with hyn2_def
  set yn3 : E := yseq (n + 3) with hyn3_def
  set yn4 : E := yseq (n + 4) with hyn4_def
  set yn5 : E := yseq (n + 5) with hyn5_def
  set yn6 : E := yseq (n + 6) with hyn6_def
  set yn7 : E := yseq (n + 7) with hyn7_def
  set yn8 : E := yseq (n + 8) with hyn8_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set tn8 : ℝ := t₀ + ((n : ℝ) + 8) * h with htn8_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set zn3 : E := y tn3 with hzn3_def
  set zn4 : E := y tn4 with hzn4_def
  set zn5 : E := y tn5 with hzn5_def
  set zn6 : E := y tn6 with hzn6_def
  set zn7 : E := y tn7 with hzn7_def
  set zn8 : E := y tn8 with hzn8_def
  set τ : E := am8VecResidual h tn y with hτ_def
  have _hsmall_record : (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2 := hsmall
  have hstep : yn8
      = yn7
        + h • ((1070017 / 3628800 : ℝ) • f tn8 yn8
             + (4467094 / 3628800 : ℝ) • f tn7 yn7
             - (4604594 / 3628800 : ℝ) • f tn6 yn6
             + (5595358 / 3628800 : ℝ) • f tn5 yn5
             - (5033120 / 3628800 : ℝ) • f tn4 yn4
             + (3146338 / 3628800 : ℝ) • f tn3 yn3
             - (1291214 / 3628800 : ℝ) • f tn2 yn2
             + (312874 / 3628800 : ℝ) • f tn1 yn1
             - (33953 / 3628800 : ℝ) • f tn yn) := by
    simpa [hyn8_def, hyn7_def, hyn6_def, hyn5_def, hyn4_def, hyn3_def, hyn2_def,
      hyn1_def, hyn_def, htn8_def, htn7_def, htn6_def, htn5_def, htn4_def,
      htn3_def, htn2_def, htn1_def, htn_def] using hy.recurrence n
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
  have htn_6h : tn + 6 * h = tn6 := by
    simp [htn_def, htn6_def]; ring
  have htn_7h : tn + 7 * h = tn7 := by
    simp [htn_def, htn7_def]; ring
  have htn_8h : tn + 8 * h = tn8 := by
    simp [htn_def, htn8_def]; ring
  have hτ_eq : τ = zn8 - zn7
      - h • ((1070017 / 3628800 : ℝ) • f tn8 zn8
             + (4467094 / 3628800 : ℝ) • f tn7 zn7
             - (4604594 / 3628800 : ℝ) • f tn6 zn6
             + (5595358 / 3628800 : ℝ) • f tn5 zn5
             - (5033120 / 3628800 : ℝ) • f tn4 zn4
             + (3146338 / 3628800 : ℝ) • f tn3 zn3
             - (1291214 / 3628800 : ℝ) • f tn2 zn2
             + (312874 / 3628800 : ℝ) • f tn1 zn1
             - (33953 / 3628800 : ℝ) • f tn zn) := by
    show am8VecResidual h tn y = _
    unfold am8VecResidual
    rw [htn1_h, htn_2h, htn_3h, htn_4h, htn_5h, htn_6h, htn_7h, htn_8h,
      hyf tn8, hyf tn7, hyf tn6, hyf tn5, hyf tn4, hyf tn3, hyf tn2,
      hyf tn1, hyf tn]
  have halg : yn8 - zn8
      = (yn7 - zn7)
        + h • ((1070017 / 3628800 : ℝ) • (f tn8 yn8 - f tn8 zn8))
        + h • ((4467094 / 3628800 : ℝ) • (f tn7 yn7 - f tn7 zn7))
        - h • ((4604594 / 3628800 : ℝ) • (f tn6 yn6 - f tn6 zn6))
        + h • ((5595358 / 3628800 : ℝ) • (f tn5 yn5 - f tn5 zn5))
        - h • ((5033120 / 3628800 : ℝ) • (f tn4 yn4 - f tn4 zn4))
        + h • ((3146338 / 3628800 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        - h • ((1291214 / 3628800 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        + h • ((312874 / 3628800 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        - h • ((33953 / 3628800 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_add]
    abel
  have hLip8 : ‖f tn8 yn8 - f tn8 zn8‖ ≤ L * ‖yn8 - zn8‖ := hf tn8 yn8 zn8
  have hLip7 : ‖f tn7 yn7 - f tn7 zn7‖ ≤ L * ‖yn7 - zn7‖ := hf tn7 yn7 zn7
  have hLip6 : ‖f tn6 yn6 - f tn6 zn6‖ ≤ L * ‖yn6 - zn6‖ := hf tn6 yn6 zn6
  have hLip5 : ‖f tn5 yn5 - f tn5 zn5‖ ≤ L * ‖yn5 - zn5‖ := hf tn5 yn5 zn5
  have hLip4 : ‖f tn4 yn4 - f tn4 zn4‖ ≤ L * ‖yn4 - zn4‖ := hf tn4 yn4 zn4
  have hLip3 : ‖f tn3 yn3 - f tn3 zn3‖ ≤ L * ‖yn3 - zn3‖ := hf tn3 yn3 zn3
  have hLip2 : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ := hf tn2 yn2 zn2
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ := hf tn1 yn1 zn1
  have hLip0 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ := hf tn yn zn
  have h1070017_nn : (0 : ℝ) ≤ 1070017 / 3628800 := by norm_num
  have h4467094_nn : (0 : ℝ) ≤ 4467094 / 3628800 := by norm_num
  have h4604594_nn : (0 : ℝ) ≤ 4604594 / 3628800 := by norm_num
  have h5595358_nn : (0 : ℝ) ≤ 5595358 / 3628800 := by norm_num
  have h5033120_nn : (0 : ℝ) ≤ 5033120 / 3628800 := by norm_num
  have h3146338_nn : (0 : ℝ) ≤ 3146338 / 3628800 := by norm_num
  have h1291214_nn : (0 : ℝ) ≤ 1291214 / 3628800 := by norm_num
  have h312874_nn : (0 : ℝ) ≤ 312874 / 3628800 := by norm_num
  have h33953_nn : (0 : ℝ) ≤ 33953 / 3628800 := by norm_num
  set A : E := yn7 - zn7 with hA_def
  set B1070017 : E := h • ((1070017 / 3628800 : ℝ) • (f tn8 yn8 - f tn8 zn8))
    with hB1070017_def
  set B4467094 : E := h • ((4467094 / 3628800 : ℝ) • (f tn7 yn7 - f tn7 zn7))
    with hB4467094_def
  set B4604594 : E := h • ((4604594 / 3628800 : ℝ) • (f tn6 yn6 - f tn6 zn6))
    with hB4604594_def
  set B5595358 : E := h • ((5595358 / 3628800 : ℝ) • (f tn5 yn5 - f tn5 zn5))
    with hB5595358_def
  set B5033120 : E := h • ((5033120 / 3628800 : ℝ) • (f tn4 yn4 - f tn4 zn4))
    with hB5033120_def
  set B3146338 : E := h • ((3146338 / 3628800 : ℝ) • (f tn3 yn3 - f tn3 zn3))
    with hB3146338_def
  set B1291214 : E := h • ((1291214 / 3628800 : ℝ) • (f tn2 yn2 - f tn2 zn2))
    with hB1291214_def
  set B312874 : E := h • ((312874 / 3628800 : ℝ) • (f tn1 yn1 - f tn1 zn1))
    with hB312874_def
  set B33953 : E := h • ((33953 / 3628800 : ℝ) • (f tn yn - f tn zn))
    with hB33953_def
  have halg' :
      yn8 - zn8 = A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338 - B1291214 + B312874 - B33953 - τ := by
    simpa [hA_def, hB1070017_def, hB4467094_def, hB4604594_def,
      hB5595358_def, hB5033120_def, hB3146338_def, hB1291214_def,
      hB312874_def, hB33953_def] using halg
  have h1070017_norm :
      ‖B1070017‖ ≤ (1070017 / 3628800 : ℝ) * h * L * ‖yn8 - zn8‖ := by
    rw [hB1070017_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h1070017_nn]
    have : h * ((1070017 / 3628800 : ℝ) * ‖f tn8 yn8 - f tn8 zn8‖)
        ≤ h * ((1070017 / 3628800 : ℝ) * (L * ‖yn8 - zn8‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip8 h1070017_nn
    calc h * ((1070017 / 3628800 : ℝ) * ‖f tn8 yn8 - f tn8 zn8‖)
        ≤ h * ((1070017 / 3628800 : ℝ) * (L * ‖yn8 - zn8‖)) := this
      _ = (1070017 / 3628800 : ℝ) * h * L * ‖yn8 - zn8‖ := by ring
  have h4467094_norm :
      ‖B4467094‖ ≤ (4467094 / 3628800 : ℝ) * h * L * ‖yn7 - zn7‖ := by
    rw [hB4467094_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h4467094_nn]
    have : h * ((4467094 / 3628800 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((4467094 / 3628800 : ℝ) * (L * ‖yn7 - zn7‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip7 h4467094_nn
    calc h * ((4467094 / 3628800 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((4467094 / 3628800 : ℝ) * (L * ‖yn7 - zn7‖)) := this
      _ = (4467094 / 3628800 : ℝ) * h * L * ‖yn7 - zn7‖ := by ring
  have h4604594_norm :
      ‖B4604594‖ ≤ (4604594 / 3628800 : ℝ) * h * L * ‖yn6 - zn6‖ := by
    rw [hB4604594_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h4604594_nn]
    have : h * ((4604594 / 3628800 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((4604594 / 3628800 : ℝ) * (L * ‖yn6 - zn6‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip6 h4604594_nn
    calc h * ((4604594 / 3628800 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((4604594 / 3628800 : ℝ) * (L * ‖yn6 - zn6‖)) := this
      _ = (4604594 / 3628800 : ℝ) * h * L * ‖yn6 - zn6‖ := by ring
  have h5595358_norm :
      ‖B5595358‖ ≤ (5595358 / 3628800 : ℝ) * h * L * ‖yn5 - zn5‖ := by
    rw [hB5595358_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h5595358_nn]
    have : h * ((5595358 / 3628800 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((5595358 / 3628800 : ℝ) * (L * ‖yn5 - zn5‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip5 h5595358_nn
    calc h * ((5595358 / 3628800 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((5595358 / 3628800 : ℝ) * (L * ‖yn5 - zn5‖)) := this
      _ = (5595358 / 3628800 : ℝ) * h * L * ‖yn5 - zn5‖ := by ring
  have h5033120_norm :
      ‖B5033120‖ ≤ (5033120 / 3628800 : ℝ) * h * L * ‖yn4 - zn4‖ := by
    rw [hB5033120_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h5033120_nn]
    have : h * ((5033120 / 3628800 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((5033120 / 3628800 : ℝ) * (L * ‖yn4 - zn4‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip4 h5033120_nn
    calc h * ((5033120 / 3628800 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((5033120 / 3628800 : ℝ) * (L * ‖yn4 - zn4‖)) := this
      _ = (5033120 / 3628800 : ℝ) * h * L * ‖yn4 - zn4‖ := by ring
  have h3146338_norm :
      ‖B3146338‖ ≤ (3146338 / 3628800 : ℝ) * h * L * ‖yn3 - zn3‖ := by
    rw [hB3146338_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h3146338_nn]
    have : h * ((3146338 / 3628800 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((3146338 / 3628800 : ℝ) * (L * ‖yn3 - zn3‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip3 h3146338_nn
    calc h * ((3146338 / 3628800 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((3146338 / 3628800 : ℝ) * (L * ‖yn3 - zn3‖)) := this
      _ = (3146338 / 3628800 : ℝ) * h * L * ‖yn3 - zn3‖ := by ring
  have h1291214_norm :
      ‖B1291214‖ ≤ (1291214 / 3628800 : ℝ) * h * L * ‖yn2 - zn2‖ := by
    rw [hB1291214_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h1291214_nn]
    have : h * ((1291214 / 3628800 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((1291214 / 3628800 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 h1291214_nn
    calc h * ((1291214 / 3628800 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((1291214 / 3628800 : ℝ) * (L * ‖yn2 - zn2‖)) := this
      _ = (1291214 / 3628800 : ℝ) * h * L * ‖yn2 - zn2‖ := by ring
  have h312874_norm :
      ‖B312874‖ ≤ (312874 / 3628800 : ℝ) * h * L * ‖yn1 - zn1‖ := by
    rw [hB312874_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h312874_nn]
    have : h * ((312874 / 3628800 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((312874 / 3628800 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 h312874_nn
    calc h * ((312874 / 3628800 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((312874 / 3628800 : ℝ) * (L * ‖yn1 - zn1‖)) := this
      _ = (312874 / 3628800 : ℝ) * h * L * ‖yn1 - zn1‖ := by ring
  have h33953_norm :
      ‖B33953‖ ≤ (33953 / 3628800 : ℝ) * h * L * ‖yn - zn‖ := by
    rw [hB33953_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h33953_nn]
    have : h * ((33953 / 3628800 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((33953 / 3628800 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 h33953_nn
    calc h * ((33953 / 3628800 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((33953 / 3628800 : ℝ) * (L * ‖yn - zn‖)) := this
      _ = (33953 / 3628800 : ℝ) * h * L * ‖yn - zn‖ := by ring
  have htri :
      ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338 - B1291214 + B312874 - B33953 - τ‖
        ≤ ‖A‖ + ‖B1070017‖ + ‖B4467094‖ + ‖B4604594‖ + ‖B5595358‖
            + ‖B5033120‖ + ‖B3146338‖ + ‖B1291214‖ + ‖B312874‖
            + ‖B33953‖ + ‖τ‖ := by
    have h1 : ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338 - B1291214 + B312874 - B33953 - τ‖
        ≤ ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338 - B1291214 + B312874 - B33953‖ + ‖τ‖ := norm_sub_le _ _
    have h2 : ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338 - B1291214 + B312874 - B33953‖
        ≤ ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338 - B1291214 + B312874‖ + ‖B33953‖ := norm_sub_le _ _
    have h3 : ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338 - B1291214 + B312874‖
        ≤ ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338 - B1291214‖ + ‖B312874‖ := norm_add_le _ _
    have h4 : ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338 - B1291214‖
        ≤ ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338‖ + ‖B1291214‖ := norm_sub_le _ _
    have h5 : ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
          + B3146338‖
        ≤ ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120‖
          + ‖B3146338‖ := norm_add_le _ _
    have h6 : ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120‖
        ≤ ‖A + B1070017 + B4467094 - B4604594 + B5595358‖
          + ‖B5033120‖ := norm_sub_le _ _
    have h7 : ‖A + B1070017 + B4467094 - B4604594 + B5595358‖
        ≤ ‖A + B1070017 + B4467094 - B4604594‖ + ‖B5595358‖ :=
      norm_add_le _ _
    have h8 : ‖A + B1070017 + B4467094 - B4604594‖
        ≤ ‖A + B1070017 + B4467094‖ + ‖B4604594‖ := norm_sub_le _ _
    have h9 : ‖A + B1070017 + B4467094‖
        ≤ ‖A + B1070017‖ + ‖B4467094‖ := norm_add_le _ _
    have h10 : ‖A + B1070017‖ ≤ ‖A‖ + ‖B1070017‖ := norm_add_le _ _
    linarith
  have hmain :
      ‖yn8 - zn8‖
        ≤ ‖yn7 - zn7‖
          + (1070017 / 3628800 : ℝ) * h * L * ‖yn8 - zn8‖
          + (4467094 / 3628800 : ℝ) * h * L * ‖yn7 - zn7‖
          + (4604594 / 3628800 : ℝ) * h * L * ‖yn6 - zn6‖
          + (5595358 / 3628800 : ℝ) * h * L * ‖yn5 - zn5‖
          + (5033120 / 3628800 : ℝ) * h * L * ‖yn4 - zn4‖
          + (3146338 / 3628800 : ℝ) * h * L * ‖yn3 - zn3‖
          + (1291214 / 3628800 : ℝ) * h * L * ‖yn2 - zn2‖
          + (312874 / 3628800 : ℝ) * h * L * ‖yn1 - zn1‖
          + (33953 / 3628800 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    calc ‖yn8 - zn8‖
        = ‖A + B1070017 + B4467094 - B4604594 + B5595358 - B5033120
            + B3146338 - B1291214 + B312874 - B33953 - τ‖ := by
            rw [halg']
      _ ≤ ‖A‖ + ‖B1070017‖ + ‖B4467094‖ + ‖B4604594‖ + ‖B5595358‖
          + ‖B5033120‖ + ‖B3146338‖ + ‖B1291214‖ + ‖B312874‖
          + ‖B33953‖ + ‖τ‖ := htri
      _ ≤ ‖yn7 - zn7‖
          + (1070017 / 3628800 : ℝ) * h * L * ‖yn8 - zn8‖
          + (4467094 / 3628800 : ℝ) * h * L * ‖yn7 - zn7‖
          + (4604594 / 3628800 : ℝ) * h * L * ‖yn6 - zn6‖
          + (5595358 / 3628800 : ℝ) * h * L * ‖yn5 - zn5‖
          + (5033120 / 3628800 : ℝ) * h * L * ‖yn4 - zn4‖
          + (3146338 / 3628800 : ℝ) * h * L * ‖yn3 - zn3‖
          + (1291214 / 3628800 : ℝ) * h * L * ‖yn2 - zn2‖
          + (312874 / 3628800 : ℝ) * h * L * ‖yn1 - zn1‖
          + (33953 / 3628800 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
        rw [hA_def]
        linarith [h1070017_norm, h4467094_norm, h4604594_norm, h5595358_norm,
          h5033120_norm, h3146338_norm, h1291214_norm, h312874_norm,
          h33953_norm]
  linarith [hmain]

/-- Divided one-step AM8 vector error bound. The explicit AM8 weights
contribute `24484545/3628800`; after dividing by the implicit
`(1 - (1070017/3628800)hL)` factor, we slacken the max-window growth to
`15L` and the residual coefficient to `2`. -/
theorem am8Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM8TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
      ≤ (1 + h * (15 * L))
            * max (max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
                ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
        + 2 * ‖am8VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖yseq n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set en3 : ℝ :=
    ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖ with hen3_def
  set en4 : ℝ :=
    ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖ with hen4_def
  set en5 : ℝ :=
    ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖ with hen5_def
  set en6 : ℝ :=
    ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖ with hen6_def
  set en7 : ℝ :=
    ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖ with hen7_def
  set en8 : ℝ :=
    ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖ with hen8_def
  set τabs : ℝ :=
    ‖am8VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7
    with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hen4_nn : 0 ≤ en4 := norm_nonneg _
  have hen5_nn : 0 ≤ en5 := norm_nonneg _
  have hen6_nn : 0 ≤ en6 := norm_nonneg _
  have hen7_nn : 0 ≤ en7 := norm_nonneg _
  have hen8_nn : 0 ≤ en8 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _)))))))
  have hen_le_E : en ≤ Emax :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen1_le_E : en1 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen2_le_E : en2 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen3_le_E : en3 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen4_le_E : en4 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen5_le_E : en5 ≤ Emax :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen6_le_E : en6 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen7_le_E : en7 ≤ Emax := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 1814400 / 1070017 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (1070017 / 3628800 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (1070017 / 3628800 : ℝ) * h * L) * en8
        ≤ en7
          + (4467094 / 3628800 : ℝ) * h * L * en7
          + (4604594 / 3628800 : ℝ) * h * L * en6
          + (5595358 / 3628800 : ℝ) * h * L * en5
          + (5033120 / 3628800 : ℝ) * h * L * en4
          + (3146338 / 3628800 : ℝ) * h * L * en3
          + (1291214 / 3628800 : ℝ) * h * L * en2
          + (312874 / 3628800 : ℝ) * h * L * en1
          + (33953 / 3628800 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hτabs_def]
      using
      (am8Vec_one_step_lipschitz (E := E) (h := h) (L := L)
        hh hsmall hf t₀ hy y hyf n)
  have h4467094_nn : 0 ≤ (4467094 / 3628800 : ℝ) * h * L := by positivity
  have h4604594_nn : 0 ≤ (4604594 / 3628800 : ℝ) * h * L := by positivity
  have h5595358_nn : 0 ≤ (5595358 / 3628800 : ℝ) * h * L := by positivity
  have h5033120_nn : 0 ≤ (5033120 / 3628800 : ℝ) * h * L := by positivity
  have h3146338_nn : 0 ≤ (3146338 / 3628800 : ℝ) * h * L := by positivity
  have h1291214_nn : 0 ≤ (1291214 / 3628800 : ℝ) * h * L := by positivity
  have h312874_nn : 0 ≤ (312874 / 3628800 : ℝ) * h * L := by positivity
  have h33953_nn : 0 ≤ (33953 / 3628800 : ℝ) * h * L := by positivity
  have h4467094_le :
      (4467094 / 3628800 : ℝ) * h * L * en7
        ≤ (4467094 / 3628800 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen7_le_E h4467094_nn
  have h4604594_le :
      (4604594 / 3628800 : ℝ) * h * L * en6
        ≤ (4604594 / 3628800 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen6_le_E h4604594_nn
  have h5595358_le :
      (5595358 / 3628800 : ℝ) * h * L * en5
        ≤ (5595358 / 3628800 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen5_le_E h5595358_nn
  have h5033120_le :
      (5033120 / 3628800 : ℝ) * h * L * en4
        ≤ (5033120 / 3628800 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen4_le_E h5033120_nn
  have h3146338_le :
      (3146338 / 3628800 : ℝ) * h * L * en3
        ≤ (3146338 / 3628800 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen3_le_E h3146338_nn
  have h1291214_le :
      (1291214 / 3628800 : ℝ) * h * L * en2
        ≤ (1291214 / 3628800 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen2_le_E h1291214_nn
  have h312874_le :
      (312874 / 3628800 : ℝ) * h * L * en1
        ≤ (312874 / 3628800 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen1_le_E h312874_nn
  have h33953_le :
      (33953 / 3628800 : ℝ) * h * L * en
        ≤ (33953 / 3628800 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen_le_E h33953_nn
  have hR_le :
      en7
          + (4467094 / 3628800 : ℝ) * h * L * en7
          + (4604594 / 3628800 : ℝ) * h * L * en6
          + (5595358 / 3628800 : ℝ) * h * L * en5
          + (5033120 / 3628800 : ℝ) * h * L * en4
          + (3146338 / 3628800 : ℝ) * h * L * en3
          + (1291214 / 3628800 : ℝ) * h * L * en2
          + (312874 / 3628800 : ℝ) * h * L * en1
          + (33953 / 3628800 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (24484545 / 3628800 : ℝ) * (h * L)) * Emax + τabs := by
    have h_alg :
        Emax + (4467094 / 3628800 : ℝ) * h * L * Emax
            + (4604594 / 3628800 : ℝ) * h * L * Emax
            + (5595358 / 3628800 : ℝ) * h * L * Emax
            + (5033120 / 3628800 : ℝ) * h * L * Emax
            + (3146338 / 3628800 : ℝ) * h * L * Emax
            + (1291214 / 3628800 : ℝ) * h * L * Emax
            + (312874 / 3628800 : ℝ) * h * L * Emax
            + (33953 / 3628800 : ℝ) * h * L * Emax + τabs
          = (1 + (24484545 / 3628800 : ℝ) * (h * L)) * Emax + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (24484545 / 3628800 : ℝ) * (h * L)
        ≤ (1 - (1070017 / 3628800 : ℝ) * h * L) * (1 + h * (15 * L)) := by
    have hxL_eq :
        (1 - (1070017 / 3628800 : ℝ) * h * L) * (1 + h * (15 * L))
          - (1 + (24484545 / 3628800 : ℝ) * (h * L))
          = (h * L) / 3628800 * (28877438 - 16050255 * (h * L)) := by ring
    have hpos : 0 ≤ 28877438 - 16050255 * (h * L) := by
      have hbound : 16050255 * (h * L) ≤ 16050255 * (1814400 / 1070017) := by
        have h16050255_nn : (0 : ℝ) ≤ 16050255 := by norm_num
        exact mul_le_mul_of_nonneg_left hx_small h16050255_nn
      have hnum : (16050255 : ℝ) * (1814400 / 1070017) ≤ 28877438 := by
        norm_num
      linarith
    have hprod : 0 ≤ (h * L) / 3628800 * (28877438 - 16050255 * (h * L)) := by
      apply mul_nonneg
      · positivity
      · exact hpos
    linarith
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (1070017 / 3628800 : ℝ) * h * L) * 2 := by
    linarith [hsmall]
  have hE_part :
      (1 + (24484545 / 3628800 : ℝ) * (h * L)) * Emax
        ≤ ((1 - (1070017 / 3628800 : ℝ) * h * L) * (1 + h * (15 * L))) * Emax :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (1070017 / 3628800 : ℝ) * h * L) * 2) * τabs :=
    by simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (24484545 / 3628800 : ℝ) * (h * L)) * Emax + τabs
        ≤ (1 - (1070017 / 3628800 : ℝ) * h * L)
            * ((1 + h * (15 * L)) * Emax + 2 * τabs) := by
    have hsplit :
        (1 - (1070017 / 3628800 : ℝ) * h * L)
            * ((1 + h * (15 * L)) * Emax + 2 * τabs)
          = ((1 - (1070017 / 3628800 : ℝ) * h * L) * (1 + h * (15 * L))) * Emax
              + ((1 - (1070017 / 3628800 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (1070017 / 3628800 : ℝ) * h * L) * en8
        ≤ (1 - (1070017 / 3628800 : ℝ) * h * L)
            * ((1 + h * (15 * L)) * Emax + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  exact le_of_mul_le_mul_left hprod hA_pos

theorem am8Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM8TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max
          ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
          ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
          ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
          ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
      ≤ (1 + h * (15 * L))
            * max (max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
                ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
        + 2 * ‖am8VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖yseq n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set en3 : ℝ :=
    ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖ with hen3_def
  set en4 : ℝ :=
    ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖ with hen4_def
  set en5 : ℝ :=
    ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖ with hen5_def
  set en6 : ℝ :=
    ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖ with hen6_def
  set en7 : ℝ :=
    ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖ with hen7_def
  set en8 : ℝ :=
    ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖ with hen8_def
  set τabs : ℝ :=
    ‖am8VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7
    with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hen4_nn : 0 ≤ en4 := norm_nonneg _
  have hen5_nn : 0 ≤ en5 := norm_nonneg _
  have hen6_nn : 0 ≤ en6 := norm_nonneg _
  have hen7_nn : 0 ≤ en7 := norm_nonneg _
  have hen8_nn : 0 ≤ en8 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _)))))))
  have hen1_le_E : en1 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen2_le_E : en2 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen3_le_E : en3 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen4_le_E : en4 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen5_le_E : en5 ≤ Emax :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen6_le_E : en6 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen7_le_E : en7 ≤ Emax := le_max_right _ _
  have h15hL_nn : 0 ≤ h * (15 * L) := by positivity
  have hen8_bd :
      en8 ≤ (1 + h * (15 * L)) * Emax + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hτabs_def, hE_def]
      using
      (am8Vec_one_step_error_bound (E := E) (h := h) (L := L)
        hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : Emax ≤ (1 + h * (15 * L)) * Emax := by
    have hone : (1 : ℝ) * Emax ≤ (1 + h * (15 * L)) * Emax :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (15 * L)) * Emax + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (15 * L)) * Emax + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (15 * L)) * Emax + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  have hen4_bd : en4 ≤ (1 + h * (15 * L)) * Emax + 2 * τabs := by
    linarith [hen4_le_E, hE_le_grow]
  have hen5_bd : en5 ≤ (1 + h * (15 * L)) * Emax + 2 * τabs := by
    linarith [hen5_le_E, hE_le_grow]
  have hen6_bd : en6 ≤ (1 + h * (15 * L)) * Emax + 2 * τabs := by
    linarith [hen6_le_E, hE_le_grow]
  have hen7_bd : en7 ≤ (1 + h * (15 * L)) * Emax + 2 * τabs := by
    linarith [hen7_le_E, hE_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd)
    hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd

/-- Pure module-algebra identity: the AM8 vector residual structure
rewrites to a ten-term abstract split where each chunk is an order-9 (or
order-10) Taylor remainder. -/
private lemma am8Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7 d8
        dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd : E) (h : ℝ) :
    y8 - y7
        - h • ((1070017 / 3628800 : ℝ) • d8
              + (4467094 / 3628800 : ℝ) • d7
              - (4604594 / 3628800 : ℝ) • d6
              + (5595358 / 3628800 : ℝ) • d5
              - (5033120 / 3628800 : ℝ) • d4
              + (3146338 / 3628800 : ℝ) • d3
              - (1291214 / 3628800 : ℝ) • d2
              + (312874 / 3628800 : ℝ) • d1
              - (33953 / 3628800 : ℝ) • d0)
      = (y8 - y0 - (8 * h) • d0
            - ((8 * h) ^ 2 / 2) • dd
            - ((8 * h) ^ 3 / 6) • ddd
            - ((8 * h) ^ 4 / 24) • dddd
            - ((8 * h) ^ 5 / 120) • ddddd
            - ((8 * h) ^ 6 / 720) • dddddd
            - ((8 * h) ^ 7 / 5040) • ddddddd
            - ((8 * h) ^ 8 / 40320) • dddddddd
            - ((8 * h) ^ 9 / 362880) • ddddddddd)
        - (y7 - y0 - (7 * h) • d0
            - ((7 * h) ^ 2 / 2) • dd
            - ((7 * h) ^ 3 / 6) • ddd
            - ((7 * h) ^ 4 / 24) • dddd
            - ((7 * h) ^ 5 / 120) • ddddd
            - ((7 * h) ^ 6 / 720) • dddddd
            - ((7 * h) ^ 7 / 5040) • ddddddd
            - ((7 * h) ^ 8 / 40320) • dddddddd
            - ((7 * h) ^ 9 / 362880) • ddddddddd)
        - (1070017 * h / 3628800 : ℝ)
            • (d8 - d0 - (8 * h) • dd
                - ((8 * h) ^ 2 / 2) • ddd
                - ((8 * h) ^ 3 / 6) • dddd
                - ((8 * h) ^ 4 / 24) • ddddd
                - ((8 * h) ^ 5 / 120) • dddddd
                - ((8 * h) ^ 6 / 720) • ddddddd
                - ((8 * h) ^ 7 / 5040) • dddddddd
                - ((8 * h) ^ 8 / 40320) • ddddddddd)
        - (4467094 * h / 3628800 : ℝ)
            • (d7 - d0 - (7 * h) • dd
                - ((7 * h) ^ 2 / 2) • ddd
                - ((7 * h) ^ 3 / 6) • dddd
                - ((7 * h) ^ 4 / 24) • ddddd
                - ((7 * h) ^ 5 / 120) • dddddd
                - ((7 * h) ^ 6 / 720) • ddddddd
                - ((7 * h) ^ 7 / 5040) • dddddddd
                - ((7 * h) ^ 8 / 40320) • ddddddddd)
        + (4604594 * h / 3628800 : ℝ)
            • (d6 - d0 - (6 * h) • dd
                - ((6 * h) ^ 2 / 2) • ddd
                - ((6 * h) ^ 3 / 6) • dddd
                - ((6 * h) ^ 4 / 24) • ddddd
                - ((6 * h) ^ 5 / 120) • dddddd
                - ((6 * h) ^ 6 / 720) • ddddddd
                - ((6 * h) ^ 7 / 5040) • dddddddd
                - ((6 * h) ^ 8 / 40320) • ddddddddd)
        - (5595358 * h / 3628800 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd
                - ((5 * h) ^ 6 / 720) • ddddddd
                - ((5 * h) ^ 7 / 5040) • dddddddd
                - ((5 * h) ^ 8 / 40320) • ddddddddd)
        + (5033120 * h / 3628800 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd
                - ((4 * h) ^ 6 / 720) • ddddddd
                - ((4 * h) ^ 7 / 5040) • dddddddd
                - ((4 * h) ^ 8 / 40320) • ddddddddd)
        - (3146338 * h / 3628800 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd
                - ((3 * h) ^ 6 / 720) • ddddddd
                - ((3 * h) ^ 7 / 5040) • dddddddd
                - ((3 * h) ^ 8 / 40320) • ddddddddd)
        + (1291214 * h / 3628800 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd
                - ((2 * h) ^ 6 / 720) • ddddddd
                - ((2 * h) ^ 7 / 5040) • dddddddd
                - ((2 * h) ^ 8 / 40320) • ddddddddd)
        - (312874 * h / 3628800 : ℝ)
            • (d1 - d0 - h • dd
                - (h ^ 2 / 2) • ddd
                - (h ^ 3 / 6) • dddd
                - (h ^ 4 / 24) • ddddd
                - (h ^ 5 / 120) • dddddd
                - (h ^ 6 / 720) • ddddddd
                - (h ^ 7 / 5040) • dddddddd
                - (h ^ 8 / 40320) • ddddddddd) := by
  simp only [smul_sub, smul_add, smul_smul]
  module

/-- Pure ring identity for the upper bound on the AM8 vector residual.
The exact coefficient `4555920744497/6858432000 ≈ 664.28` is slackened to
`665` in the next helper. -/
private lemma am8Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 3628800 * (8 * h) ^ 10 + M / 3628800 * (7 * h) ^ 10
      + (1070017 * h / 3628800) * (M / 362880 * (8 * h) ^ 9)
      + (4467094 * h / 3628800) * (M / 362880 * (7 * h) ^ 9)
      + (4604594 * h / 3628800) * (M / 362880 * (6 * h) ^ 9)
      + (5595358 * h / 3628800) * (M / 362880 * (5 * h) ^ 9)
      + (5033120 * h / 3628800) * (M / 362880 * (4 * h) ^ 9)
      + (3146338 * h / 3628800) * (M / 362880 * (3 * h) ^ 9)
      + (1291214 * h / 3628800) * (M / 362880 * (2 * h) ^ 9)
      + (312874 * h / 3628800) * (M / 362880 * h ^ 9)
      = (4555920744497 / 6858432000 : ℝ) * M * h ^ 10 := by
  ring

/-- Triangle inequality for the ten-term AM8 vector residual chunk. -/
private lemma am8Vec_residual_ten_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G I J K L : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (1070017 * h / 3628800 : ℝ) • C
        - (4467094 * h / 3628800 : ℝ) • D
        + (4604594 * h / 3628800 : ℝ) • F
        - (5595358 * h / 3628800 : ℝ) • G
        + (5033120 * h / 3628800 : ℝ) • I
        - (3146338 * h / 3628800 : ℝ) • J
        + (1291214 * h / 3628800 : ℝ) • K
        - (312874 * h / 3628800 : ℝ) • L‖
      ≤ ‖A‖ + ‖B‖ + (1070017 * h / 3628800) * ‖C‖
          + (4467094 * h / 3628800) * ‖D‖
          + (4604594 * h / 3628800) * ‖F‖
          + (5595358 * h / 3628800) * ‖G‖
          + (5033120 * h / 3628800) * ‖I‖
          + (3146338 * h / 3628800) * ‖J‖
          + (1291214 * h / 3628800) * ‖K‖
          + (312874 * h / 3628800) * ‖L‖ := by
  have h1070017h_nn : 0 ≤ (1070017 * h / 3628800 : ℝ) := by linarith
  have h4467094h_nn : 0 ≤ (4467094 * h / 3628800 : ℝ) := by linarith
  have h4604594h_nn : 0 ≤ (4604594 * h / 3628800 : ℝ) := by linarith
  have h5595358h_nn : 0 ≤ (5595358 * h / 3628800 : ℝ) := by linarith
  have h5033120h_nn : 0 ≤ (5033120 * h / 3628800 : ℝ) := by linarith
  have h3146338h_nn : 0 ≤ (3146338 * h / 3628800 : ℝ) := by linarith
  have h1291214h_nn : 0 ≤ (1291214 * h / 3628800 : ℝ) := by linarith
  have h312874h_nn : 0 ≤ (312874 * h / 3628800 : ℝ) := by linarith
  have hC_norm :
      ‖(1070017 * h / 3628800 : ℝ) • C‖
        = (1070017 * h / 3628800) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg h1070017h_nn]
  have hD_norm :
      ‖(4467094 * h / 3628800 : ℝ) • D‖
        = (4467094 * h / 3628800) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg h4467094h_nn]
  have hF_norm :
      ‖(4604594 * h / 3628800 : ℝ) • F‖
        = (4604594 * h / 3628800) * ‖F‖ := by
    rw [norm_smul, Real.norm_of_nonneg h4604594h_nn]
  have hG_norm :
      ‖(5595358 * h / 3628800 : ℝ) • G‖
        = (5595358 * h / 3628800) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg h5595358h_nn]
  have hI_norm :
      ‖(5033120 * h / 3628800 : ℝ) • I‖
        = (5033120 * h / 3628800) * ‖I‖ := by
    rw [norm_smul, Real.norm_of_nonneg h5033120h_nn]
  have hJ_norm :
      ‖(3146338 * h / 3628800 : ℝ) • J‖
        = (3146338 * h / 3628800) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg h3146338h_nn]
  have hK_norm :
      ‖(1291214 * h / 3628800 : ℝ) • K‖
        = (1291214 * h / 3628800) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg h1291214h_nn]
  have hL_norm :
      ‖(312874 * h / 3628800 : ℝ) • L‖
        = (312874 * h / 3628800) * ‖L‖ := by
    rw [norm_smul, Real.norm_of_nonneg h312874h_nn]
  have h1 :
      ‖A - B - (1070017 * h / 3628800 : ℝ) • C
          - (4467094 * h / 3628800 : ℝ) • D
          + (4604594 * h / 3628800 : ℝ) • F
          - (5595358 * h / 3628800 : ℝ) • G
          + (5033120 * h / 3628800 : ℝ) • I
          - (3146338 * h / 3628800 : ℝ) • J
          + (1291214 * h / 3628800 : ℝ) • K
          - (312874 * h / 3628800 : ℝ) • L‖
        ≤ ‖A - B - (1070017 * h / 3628800 : ℝ) • C
            - (4467094 * h / 3628800 : ℝ) • D
            + (4604594 * h / 3628800 : ℝ) • F
            - (5595358 * h / 3628800 : ℝ) • G
            + (5033120 * h / 3628800 : ℝ) • I
            - (3146338 * h / 3628800 : ℝ) • J
            + (1291214 * h / 3628800 : ℝ) • K‖
          + ‖(312874 * h / 3628800 : ℝ) • L‖ := norm_sub_le _ _
  have h2 :
      ‖A - B - (1070017 * h / 3628800 : ℝ) • C
          - (4467094 * h / 3628800 : ℝ) • D
          + (4604594 * h / 3628800 : ℝ) • F
          - (5595358 * h / 3628800 : ℝ) • G
          + (5033120 * h / 3628800 : ℝ) • I
          - (3146338 * h / 3628800 : ℝ) • J
          + (1291214 * h / 3628800 : ℝ) • K‖
        ≤ ‖A - B - (1070017 * h / 3628800 : ℝ) • C
            - (4467094 * h / 3628800 : ℝ) • D
            + (4604594 * h / 3628800 : ℝ) • F
            - (5595358 * h / 3628800 : ℝ) • G
            + (5033120 * h / 3628800 : ℝ) • I
            - (3146338 * h / 3628800 : ℝ) • J‖
          + ‖(1291214 * h / 3628800 : ℝ) • K‖ := norm_add_le _ _
  have h3 :
      ‖A - B - (1070017 * h / 3628800 : ℝ) • C
          - (4467094 * h / 3628800 : ℝ) • D
          + (4604594 * h / 3628800 : ℝ) • F
          - (5595358 * h / 3628800 : ℝ) • G
          + (5033120 * h / 3628800 : ℝ) • I
          - (3146338 * h / 3628800 : ℝ) • J‖
        ≤ ‖A - B - (1070017 * h / 3628800 : ℝ) • C
            - (4467094 * h / 3628800 : ℝ) • D
            + (4604594 * h / 3628800 : ℝ) • F
            - (5595358 * h / 3628800 : ℝ) • G
            + (5033120 * h / 3628800 : ℝ) • I‖
          + ‖(3146338 * h / 3628800 : ℝ) • J‖ := norm_sub_le _ _
  have h4 :
      ‖A - B - (1070017 * h / 3628800 : ℝ) • C
          - (4467094 * h / 3628800 : ℝ) • D
          + (4604594 * h / 3628800 : ℝ) • F
          - (5595358 * h / 3628800 : ℝ) • G
          + (5033120 * h / 3628800 : ℝ) • I‖
        ≤ ‖A - B - (1070017 * h / 3628800 : ℝ) • C
            - (4467094 * h / 3628800 : ℝ) • D
            + (4604594 * h / 3628800 : ℝ) • F
            - (5595358 * h / 3628800 : ℝ) • G‖
          + ‖(5033120 * h / 3628800 : ℝ) • I‖ := norm_add_le _ _
  have h5 :
      ‖A - B - (1070017 * h / 3628800 : ℝ) • C
          - (4467094 * h / 3628800 : ℝ) • D
          + (4604594 * h / 3628800 : ℝ) • F
          - (5595358 * h / 3628800 : ℝ) • G‖
        ≤ ‖A - B - (1070017 * h / 3628800 : ℝ) • C
            - (4467094 * h / 3628800 : ℝ) • D
            + (4604594 * h / 3628800 : ℝ) • F‖
          + ‖(5595358 * h / 3628800 : ℝ) • G‖ := norm_sub_le _ _
  have h6 :
      ‖A - B - (1070017 * h / 3628800 : ℝ) • C
          - (4467094 * h / 3628800 : ℝ) • D
          + (4604594 * h / 3628800 : ℝ) • F‖
        ≤ ‖A - B - (1070017 * h / 3628800 : ℝ) • C
            - (4467094 * h / 3628800 : ℝ) • D‖
          + ‖(4604594 * h / 3628800 : ℝ) • F‖ := norm_add_le _ _
  have h7 :
      ‖A - B - (1070017 * h / 3628800 : ℝ) • C
          - (4467094 * h / 3628800 : ℝ) • D‖
        ≤ ‖A - B - (1070017 * h / 3628800 : ℝ) • C‖
          + ‖(4467094 * h / 3628800 : ℝ) • D‖ := norm_sub_le _ _
  have h8 :
      ‖A - B - (1070017 * h / 3628800 : ℝ) • C‖
        ≤ ‖A - B‖ + ‖(1070017 * h / 3628800 : ℝ) • C‖ := norm_sub_le _ _
  have h9 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith [hC_norm.le, hC_norm.ge, hD_norm.le, hD_norm.ge,
    hF_norm.le, hF_norm.ge, hG_norm.le, hG_norm.ge, hI_norm.le,
    hI_norm.ge, hJ_norm.le, hJ_norm.ge, hK_norm.le, hK_norm.ge,
    hL_norm.le, hL_norm.ge]

/-- Combine the ten-term triangle inequality with the norm bounds on
each piece to obtain the `665 · M · h^10` final AM8 vector residual bound. -/
private lemma am8Vec_residual_combine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D F G I J K L : E)
    (htri : ‖A - B - (1070017 * h / 3628800 : ℝ) • C
              - (4467094 * h / 3628800 : ℝ) • D
              + (4604594 * h / 3628800 : ℝ) • F
              - (5595358 * h / 3628800 : ℝ) • G
              + (5033120 * h / 3628800 : ℝ) • I
              - (3146338 * h / 3628800 : ℝ) • J
              + (1291214 * h / 3628800 : ℝ) • K
              - (312874 * h / 3628800 : ℝ) • L‖
            ≤ ‖A‖ + ‖B‖ + (1070017 * h / 3628800) * ‖C‖
              + (4467094 * h / 3628800) * ‖D‖
              + (4604594 * h / 3628800) * ‖F‖
              + (5595358 * h / 3628800) * ‖G‖
              + (5033120 * h / 3628800) * ‖I‖
              + (3146338 * h / 3628800) * ‖J‖
              + (1291214 * h / 3628800) * ‖K‖
              + (312874 * h / 3628800) * ‖L‖)
    (hA_bd : ‖A‖ ≤ M / 3628800 * (8 * h) ^ 10)
    (hB_bd : ‖B‖ ≤ M / 3628800 * (7 * h) ^ 10)
    (hC_bd : ‖C‖ ≤ M / 362880 * (8 * h) ^ 9)
    (hD_bd : ‖D‖ ≤ M / 362880 * (7 * h) ^ 9)
    (hF_bd : ‖F‖ ≤ M / 362880 * (6 * h) ^ 9)
    (hG_bd : ‖G‖ ≤ M / 362880 * (5 * h) ^ 9)
    (hI_bd : ‖I‖ ≤ M / 362880 * (4 * h) ^ 9)
    (hJ_bd : ‖J‖ ≤ M / 362880 * (3 * h) ^ 9)
    (hK_bd : ‖K‖ ≤ M / 362880 * (2 * h) ^ 9)
    (hL_bd : ‖L‖ ≤ M / 362880 * h ^ 9) :
    ‖A - B - (1070017 * h / 3628800 : ℝ) • C
        - (4467094 * h / 3628800 : ℝ) • D
        + (4604594 * h / 3628800 : ℝ) • F
        - (5595358 * h / 3628800 : ℝ) • G
        + (5033120 * h / 3628800 : ℝ) • I
        - (3146338 * h / 3628800 : ℝ) • J
        + (1291214 * h / 3628800 : ℝ) • K
        - (312874 * h / 3628800 : ℝ) • L‖
      ≤ (665 : ℝ) * M * h ^ 10 := by
  have h1070017h_nn : 0 ≤ (1070017 * h / 3628800 : ℝ) := by linarith
  have h4467094h_nn : 0 ≤ (4467094 * h / 3628800 : ℝ) := by linarith
  have h4604594h_nn : 0 ≤ (4604594 * h / 3628800 : ℝ) := by linarith
  have h5595358h_nn : 0 ≤ (5595358 * h / 3628800 : ℝ) := by linarith
  have h5033120h_nn : 0 ≤ (5033120 * h / 3628800 : ℝ) := by linarith
  have h3146338h_nn : 0 ≤ (3146338 * h / 3628800 : ℝ) := by linarith
  have h1291214h_nn : 0 ≤ (1291214 * h / 3628800 : ℝ) := by linarith
  have h312874h_nn : 0 ≤ (312874 * h / 3628800 : ℝ) := by linarith
  have h1070017C_bd : (1070017 * h / 3628800) * ‖C‖
      ≤ (1070017 * h / 3628800) * (M / 362880 * (8 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hC_bd h1070017h_nn
  have h4467094D_bd : (4467094 * h / 3628800) * ‖D‖
      ≤ (4467094 * h / 3628800) * (M / 362880 * (7 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hD_bd h4467094h_nn
  have h4604594F_bd : (4604594 * h / 3628800) * ‖F‖
      ≤ (4604594 * h / 3628800) * (M / 362880 * (6 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hF_bd h4604594h_nn
  have h5595358G_bd : (5595358 * h / 3628800) * ‖G‖
      ≤ (5595358 * h / 3628800) * (M / 362880 * (5 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hG_bd h5595358h_nn
  have h5033120I_bd : (5033120 * h / 3628800) * ‖I‖
      ≤ (5033120 * h / 3628800) * (M / 362880 * (4 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hI_bd h5033120h_nn
  have h3146338J_bd : (3146338 * h / 3628800) * ‖J‖
      ≤ (3146338 * h / 3628800) * (M / 362880 * (3 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hJ_bd h3146338h_nn
  have h1291214K_bd : (1291214 * h / 3628800) * ‖K‖
      ≤ (1291214 * h / 3628800) * (M / 362880 * (2 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hK_bd h1291214h_nn
  have h312874L_bd : (312874 * h / 3628800) * ‖L‖
      ≤ (312874 * h / 3628800) * (M / 362880 * h ^ 9) :=
    mul_le_mul_of_nonneg_left hL_bd h312874h_nn
  have hbound_alg :
      M / 3628800 * (8 * h) ^ 10 + M / 3628800 * (7 * h) ^ 10
        + (1070017 * h / 3628800) * (M / 362880 * (8 * h) ^ 9)
        + (4467094 * h / 3628800) * (M / 362880 * (7 * h) ^ 9)
        + (4604594 * h / 3628800) * (M / 362880 * (6 * h) ^ 9)
        + (5595358 * h / 3628800) * (M / 362880 * (5 * h) ^ 9)
        + (5033120 * h / 3628800) * (M / 362880 * (4 * h) ^ 9)
        + (3146338 * h / 3628800) * (M / 362880 * (3 * h) ^ 9)
        + (1291214 * h / 3628800) * (M / 362880 * (2 * h) ^ 9)
        + (312874 * h / 3628800) * (M / 362880 * h ^ 9)
        = (4555920744497 / 6858432000 : ℝ) * M * h ^ 10 :=
    am8Vec_residual_bound_alg_identity M h
  have hh10_nn : 0 ≤ h ^ 10 := by positivity
  have hMh10_nn : 0 ≤ M * h ^ 10 := mul_nonneg hMnn hh10_nn
  have hslack :
      (4555920744497 / 6858432000 : ℝ) * M * h ^ 10 ≤ 665 * M * h ^ 10 := by
    have hle : (4555920744497 / 6858432000 : ℝ) ≤ 665 := by norm_num
    have hbase :
        (4555920744497 / 6858432000 : ℝ) * (M * h ^ 10) ≤ 665 * (M * h ^ 10) :=
      mul_le_mul_of_nonneg_right hle hMh10_nn
    have hL' : (4555920744497 / 6858432000 : ℝ) * M * h ^ 10
        = (4555920744497 / 6858432000 : ℝ) * (M * h ^ 10) := by ring
    have hR : (665 : ℝ) * M * h ^ 10 = 665 * (M * h ^ 10) := by ring
    rw [hL', hR]
    exact hbase
  linarith [htri, hA_bd, hB_bd, h1070017C_bd, h4467094D_bd, h4604594F_bd,
    h5595358G_bd, h5033120I_bd, h3146338J_bd, h1291214K_bd, h312874L_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

theorem am8Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 10 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 10 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (ht8h : t + 8 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 8 * h) - y (t + 7 * h)
        - h • ((1070017 / 3628800 : ℝ) • deriv y (t + 8 * h)
              + (4467094 / 3628800 : ℝ) • deriv y (t + 7 * h)
              - (4604594 / 3628800 : ℝ) • deriv y (t + 6 * h)
              + (5595358 / 3628800 : ℝ) • deriv y (t + 5 * h)
              - (5033120 / 3628800 : ℝ) • deriv y (t + 4 * h)
              + (3146338 / 3628800 : ℝ) • deriv y (t + 3 * h)
              - (1291214 / 3628800 : ℝ) • deriv y (t + 2 * h)
              + (312874 / 3628800 : ℝ) • deriv y (t + h)
              - (33953 / 3628800 : ℝ) • deriv y t)‖
      ≤ (665 : ℝ) * M * h ^ 10 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have hRy7 :=
    y_tenth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRy8 :=
    y_tenth_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRyp1 :=
    derivY_ninth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_ninth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_ninth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_ninth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_ninth_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_ninth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_ninth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_ninth_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  set y0 : E := y t with hy0_def
  set y7 : E := y (t + 7 * h) with hy7_def
  set y8 : E := y (t + 8 * h) with hy8_def
  set d0 : E := deriv y t with hd0_def
  set d1 : E := deriv y (t + h) with hd1_def
  set d2 : E := deriv y (t + 2 * h) with hd2_def
  set d3 : E := deriv y (t + 3 * h) with hd3_def
  set d4 : E := deriv y (t + 4 * h) with hd4_def
  set d5 : E := deriv y (t + 5 * h) with hd5_def
  set d6 : E := deriv y (t + 6 * h) with hd6_def
  set d7 : E := deriv y (t + 7 * h) with hd7_def
  set d8 : E := deriv y (t + 8 * h) with hd8_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  set ddddd : E := iteratedDeriv 5 y t with hddddd_def
  set dddddd : E := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd : E := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd : E := iteratedDeriv 8 y t with hdddddddd_def
  set ddddddddd : E := iteratedDeriv 9 y t with hddddddddd_def
  clear_value y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7 d8
    dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd
  have hLTE_eq :
      y8 - y7 - h • ((1070017 / 3628800 : ℝ) • d8
                    + (4467094 / 3628800 : ℝ) • d7
                    - (4604594 / 3628800 : ℝ) • d6
                    + (5595358 / 3628800 : ℝ) • d5
                    - (5033120 / 3628800 : ℝ) • d4
                    + (3146338 / 3628800 : ℝ) • d3
                    - (1291214 / 3628800 : ℝ) • d2
                    + (312874 / 3628800 : ℝ) • d1
                    - (33953 / 3628800 : ℝ) • d0)
        = (y8 - y0 - (8 * h) • d0
              - ((8 * h) ^ 2 / 2) • dd
              - ((8 * h) ^ 3 / 6) • ddd
              - ((8 * h) ^ 4 / 24) • dddd
              - ((8 * h) ^ 5 / 120) • ddddd
              - ((8 * h) ^ 6 / 720) • dddddd
              - ((8 * h) ^ 7 / 5040) • ddddddd
              - ((8 * h) ^ 8 / 40320) • dddddddd
              - ((8 * h) ^ 9 / 362880) • ddddddddd)
          - (y7 - y0 - (7 * h) • d0
              - ((7 * h) ^ 2 / 2) • dd
              - ((7 * h) ^ 3 / 6) • ddd
              - ((7 * h) ^ 4 / 24) • dddd
              - ((7 * h) ^ 5 / 120) • ddddd
              - ((7 * h) ^ 6 / 720) • dddddd
              - ((7 * h) ^ 7 / 5040) • ddddddd
              - ((7 * h) ^ 8 / 40320) • dddddddd
              - ((7 * h) ^ 9 / 362880) • ddddddddd)
          - (1070017 * h / 3628800 : ℝ)
              • (d8 - d0 - (8 * h) • dd
                  - ((8 * h) ^ 2 / 2) • ddd
                  - ((8 * h) ^ 3 / 6) • dddd
                  - ((8 * h) ^ 4 / 24) • ddddd
                  - ((8 * h) ^ 5 / 120) • dddddd
                  - ((8 * h) ^ 6 / 720) • ddddddd
                  - ((8 * h) ^ 7 / 5040) • dddddddd
                  - ((8 * h) ^ 8 / 40320) • ddddddddd)
          - (4467094 * h / 3628800 : ℝ)
              • (d7 - d0 - (7 * h) • dd
                  - ((7 * h) ^ 2 / 2) • ddd
                  - ((7 * h) ^ 3 / 6) • dddd
                  - ((7 * h) ^ 4 / 24) • ddddd
                  - ((7 * h) ^ 5 / 120) • dddddd
                  - ((7 * h) ^ 6 / 720) • ddddddd
                  - ((7 * h) ^ 7 / 5040) • dddddddd
                  - ((7 * h) ^ 8 / 40320) • ddddddddd)
          + (4604594 * h / 3628800 : ℝ)
              • (d6 - d0 - (6 * h) • dd
                  - ((6 * h) ^ 2 / 2) • ddd
                  - ((6 * h) ^ 3 / 6) • dddd
                  - ((6 * h) ^ 4 / 24) • ddddd
                  - ((6 * h) ^ 5 / 120) • dddddd
                  - ((6 * h) ^ 6 / 720) • ddddddd
                  - ((6 * h) ^ 7 / 5040) • dddddddd
                  - ((6 * h) ^ 8 / 40320) • ddddddddd)
          - (5595358 * h / 3628800 : ℝ)
              • (d5 - d0 - (5 * h) • dd
                  - ((5 * h) ^ 2 / 2) • ddd
                  - ((5 * h) ^ 3 / 6) • dddd
                  - ((5 * h) ^ 4 / 24) • ddddd
                  - ((5 * h) ^ 5 / 120) • dddddd
                  - ((5 * h) ^ 6 / 720) • ddddddd
                  - ((5 * h) ^ 7 / 5040) • dddddddd
                  - ((5 * h) ^ 8 / 40320) • ddddddddd)
          + (5033120 * h / 3628800 : ℝ)
              • (d4 - d0 - (4 * h) • dd
                  - ((4 * h) ^ 2 / 2) • ddd
                  - ((4 * h) ^ 3 / 6) • dddd
                  - ((4 * h) ^ 4 / 24) • ddddd
                  - ((4 * h) ^ 5 / 120) • dddddd
                  - ((4 * h) ^ 6 / 720) • ddddddd
                  - ((4 * h) ^ 7 / 5040) • dddddddd
                  - ((4 * h) ^ 8 / 40320) • ddddddddd)
          - (3146338 * h / 3628800 : ℝ)
              • (d3 - d0 - (3 * h) • dd
                  - ((3 * h) ^ 2 / 2) • ddd
                  - ((3 * h) ^ 3 / 6) • dddd
                  - ((3 * h) ^ 4 / 24) • ddddd
                  - ((3 * h) ^ 5 / 120) • dddddd
                  - ((3 * h) ^ 6 / 720) • ddddddd
                  - ((3 * h) ^ 7 / 5040) • dddddddd
                  - ((3 * h) ^ 8 / 40320) • ddddddddd)
          + (1291214 * h / 3628800 : ℝ)
              • (d2 - d0 - (2 * h) • dd
                  - ((2 * h) ^ 2 / 2) • ddd
                  - ((2 * h) ^ 3 / 6) • dddd
                  - ((2 * h) ^ 4 / 24) • ddddd
                  - ((2 * h) ^ 5 / 120) • dddddd
                  - ((2 * h) ^ 6 / 720) • ddddddd
                  - ((2 * h) ^ 7 / 5040) • dddddddd
                  - ((2 * h) ^ 8 / 40320) • ddddddddd)
          - (312874 * h / 3628800 : ℝ)
              • (d1 - d0 - h • dd
                  - (h ^ 2 / 2) • ddd
                  - (h ^ 3 / 6) • dddd
                  - (h ^ 4 / 24) • ddddd
                  - (h ^ 5 / 120) • dddddd
                  - (h ^ 6 / 720) • ddddddd
                  - (h ^ 7 / 5040) • dddddddd
                  - (h ^ 8 / 40320) • ddddddddd) :=
    am8Vec_residual_alg_identity y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7 d8
      dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd h
  rw [hLTE_eq]
  set A : E := y8 - y0 - (8 * h) • d0
            - ((8 * h) ^ 2 / 2) • dd
            - ((8 * h) ^ 3 / 6) • ddd
            - ((8 * h) ^ 4 / 24) • dddd
            - ((8 * h) ^ 5 / 120) • ddddd
            - ((8 * h) ^ 6 / 720) • dddddd
            - ((8 * h) ^ 7 / 5040) • ddddddd
            - ((8 * h) ^ 8 / 40320) • dddddddd
            - ((8 * h) ^ 9 / 362880) • ddddddddd with hA_def
  set B : E := y7 - y0 - (7 * h) • d0
            - ((7 * h) ^ 2 / 2) • dd
            - ((7 * h) ^ 3 / 6) • ddd
            - ((7 * h) ^ 4 / 24) • dddd
            - ((7 * h) ^ 5 / 120) • ddddd
            - ((7 * h) ^ 6 / 720) • dddddd
            - ((7 * h) ^ 7 / 5040) • ddddddd
            - ((7 * h) ^ 8 / 40320) • dddddddd
            - ((7 * h) ^ 9 / 362880) • ddddddddd with hB_def
  set C : E := d8 - d0 - (8 * h) • dd
            - ((8 * h) ^ 2 / 2) • ddd
            - ((8 * h) ^ 3 / 6) • dddd
            - ((8 * h) ^ 4 / 24) • ddddd
            - ((8 * h) ^ 5 / 120) • dddddd
            - ((8 * h) ^ 6 / 720) • ddddddd
            - ((8 * h) ^ 7 / 5040) • dddddddd
            - ((8 * h) ^ 8 / 40320) • ddddddddd with hC_def
  set D : E := d7 - d0 - (7 * h) • dd
            - ((7 * h) ^ 2 / 2) • ddd
            - ((7 * h) ^ 3 / 6) • dddd
            - ((7 * h) ^ 4 / 24) • ddddd
            - ((7 * h) ^ 5 / 120) • dddddd
            - ((7 * h) ^ 6 / 720) • ddddddd
            - ((7 * h) ^ 7 / 5040) • dddddddd
            - ((7 * h) ^ 8 / 40320) • ddddddddd with hD_def
  set F : E := d6 - d0 - (6 * h) • dd
            - ((6 * h) ^ 2 / 2) • ddd
            - ((6 * h) ^ 3 / 6) • dddd
            - ((6 * h) ^ 4 / 24) • ddddd
            - ((6 * h) ^ 5 / 120) • dddddd
            - ((6 * h) ^ 6 / 720) • ddddddd
            - ((6 * h) ^ 7 / 5040) • dddddddd
            - ((6 * h) ^ 8 / 40320) • ddddddddd with hF_def
  set G : E := d5 - d0 - (5 * h) • dd
            - ((5 * h) ^ 2 / 2) • ddd
            - ((5 * h) ^ 3 / 6) • dddd
            - ((5 * h) ^ 4 / 24) • ddddd
            - ((5 * h) ^ 5 / 120) • dddddd
            - ((5 * h) ^ 6 / 720) • ddddddd
            - ((5 * h) ^ 7 / 5040) • dddddddd
            - ((5 * h) ^ 8 / 40320) • ddddddddd with hG_def
  set I : E := d4 - d0 - (4 * h) • dd
            - ((4 * h) ^ 2 / 2) • ddd
            - ((4 * h) ^ 3 / 6) • dddd
            - ((4 * h) ^ 4 / 24) • ddddd
            - ((4 * h) ^ 5 / 120) • dddddd
            - ((4 * h) ^ 6 / 720) • ddddddd
            - ((4 * h) ^ 7 / 5040) • dddddddd
            - ((4 * h) ^ 8 / 40320) • ddddddddd with hI_def
  set J : E := d3 - d0 - (3 * h) • dd
            - ((3 * h) ^ 2 / 2) • ddd
            - ((3 * h) ^ 3 / 6) • dddd
            - ((3 * h) ^ 4 / 24) • ddddd
            - ((3 * h) ^ 5 / 120) • dddddd
            - ((3 * h) ^ 6 / 720) • ddddddd
            - ((3 * h) ^ 7 / 5040) • dddddddd
            - ((3 * h) ^ 8 / 40320) • ddddddddd with hJ_def
  set K : E := d2 - d0 - (2 * h) • dd
            - ((2 * h) ^ 2 / 2) • ddd
            - ((2 * h) ^ 3 / 6) • dddd
            - ((2 * h) ^ 4 / 24) • ddddd
            - ((2 * h) ^ 5 / 120) • dddddd
            - ((2 * h) ^ 6 / 720) • ddddddd
            - ((2 * h) ^ 7 / 5040) • dddddddd
            - ((2 * h) ^ 8 / 40320) • ddddddddd with hK_def
  set L : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd
            - (h ^ 4 / 24) • ddddd
            - (h ^ 5 / 120) • dddddd
            - (h ^ 6 / 720) • ddddddd
            - (h ^ 7 / 5040) • dddddddd
            - (h ^ 8 / 40320) • ddddddddd with hL_def
  clear_value A B C D F G I J K L
  have htri := am8Vec_residual_ten_term_triangle A B C D F G I J K L h hh
  have hA_bd : ‖A‖ ≤ M / 3628800 * (8 * h) ^ 10 := hRy8
  have hB_bd : ‖B‖ ≤ M / 3628800 * (7 * h) ^ 10 := hRy7
  have hC_bd : ‖C‖ ≤ M / 362880 * (8 * h) ^ 9 := hRyp8
  have hD_bd : ‖D‖ ≤ M / 362880 * (7 * h) ^ 9 := hRyp7
  have hF_bd : ‖F‖ ≤ M / 362880 * (6 * h) ^ 9 := hRyp6
  have hG_bd : ‖G‖ ≤ M / 362880 * (5 * h) ^ 9 := hRyp5
  have hI_bd : ‖I‖ ≤ M / 362880 * (4 * h) ^ 9 := hRyp4
  have hJ_bd : ‖J‖ ≤ M / 362880 * (3 * h) ^ 9 := hRyp3
  have hK_bd : ‖K‖ ≤ M / 362880 * (2 * h) ^ 9 := hRyp2
  have hL_bd : ‖L‖ ≤ M / 362880 * h ^ 9 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  exact am8Vec_residual_combine hh hMnn A B C D F G I J K L htri
    hA_bd hB_bd hC_bd hD_bd hF_bd hG_bd hI_bd hJ_bd hK_bd hL_bd

theorem am8Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 10 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 8) * h ≤ T →
        ‖am8VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 10 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_ten_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(665 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 8) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h = ((n : ℝ) + 8) * h := by ring
    linarith
  show ‖am8VecResidual h t y‖ ≤ 665 * M * h ^ 10
  unfold am8VecResidual
  exact am8Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem hh.le

theorem am8Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 10 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsAM8TrajectoryVec h f t₀ yseq →
      0 ≤ ε₀ →
      ‖yseq 0 - y t₀‖ ≤ ε₀ →
      ‖yseq 1 - y (t₀ + h)‖ ≤ ε₀ →
      ‖yseq 2 - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖yseq 3 - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖yseq 4 - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖yseq 5 - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖yseq 6 - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ‖yseq 7 - y (t₀ + 7 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 7) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((15 * L) * T) * ε₀ + K * h ^ 9 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am8Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((15 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd he7_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => ‖yseq k - y (t₀ + (k : ℝ) * h)‖ with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (max (max (max
        (eN k) (eN (k + 1))) (eN (k + 2)))
        (eN (k + 3))) (eN (k + 4))) (eN (k + 5))) (eN (k + 6))) (eN (k + 7))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => norm_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
        (le_max_of_le_left (heN_nn k)))))))
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (max (max (max
        (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4)) (eN 5)) (eN 6)) (eN 7)
        ≤ ε₀
    refine max_le (max_le (max_le (max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · show ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀
      simpa using he0_bd
    · show ‖yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    · show ‖yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    · show ‖yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
    · show ‖yseq 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]; simpa using he4_bd
    · show ‖yseq 5 - y (t₀ + ((5 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((5 : ℕ) : ℝ) * h = 5 * h := by push_cast; ring
      rw [hcast]; simpa using he5_bd
    · show ‖yseq 6 - y (t₀ + ((6 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((6 : ℕ) : ℝ) * h = 6 * h := by push_cast; ring
      rw [hcast]; simpa using he6_bd
    · show ‖yseq 7 - y (t₀ + ((7 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((7 : ℕ) : ℝ) * h = 7 * h := by push_cast; ring
      rw [hcast]; simpa using he7_bd
  have h15L_nn : (0 : ℝ) ≤ 15 * L := by linarith
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 8) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (15 * L)) * EN n + (2 * C) * h ^ 10 := by
    intro n hnh_le
    have honestep := am8Vec_one_step_error_pair_bound
      (E := E) (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by
      push_cast; ring
    have hcast4 : ((n + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 4 := by
      push_cast; ring
    have hcast5 : ((n + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 5 := by
      push_cast; ring
    have hcast6 : ((n + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 6 := by
      push_cast; ring
    have hcast7 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) =
        (n : ℝ) + 7 := by
      push_cast; ring
    have hcast8 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) =
        (n : ℝ) + 8 := by
      push_cast; ring
    have heq_eN_n : eN n
        = ‖yseq n - y (t₀ + (n : ℝ) * h)‖ := rfl
    have heq_eN_n1 : eN (n + 1)
        = ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast1]
    have heq_eN_n2 : eN (n + 1 + 1)
        = ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast2]
    have heq_eN_n3 : eN (n + 1 + 1 + 1)
        = ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast3]
    have heq_eN_n4 : eN (n + 1 + 1 + 1 + 1)
        = ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast4]
    have heq_eN_n5 : eN (n + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast5]
    have heq_eN_n6 : eN (n + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast6]
    have heq_eN_n7 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast7]
    have heq_eN_n8 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast8]
    show max (max (max (max (max (max (max
            (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * (15 * L))
            * max (max (max (max (max (max (max (eN n) (eN (n + 1)))
                  (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1))
          + (2 * C) * h ^ 10
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5,
      heq_eN_n6, heq_eN_n7, heq_eN_n8]
    have h2τ : 2 * ‖am8VecResidual h (t₀ + (n : ℝ) * h) y‖
        ≤ (2 * C) * h ^ 10 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith [this]
    linarith [honestep, h2τ]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((15 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((15 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh9_nn : 0 ≤ h ^ 9 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((15 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((15 * L) * T) * ε₀
            + T * Real.exp ((15 * L) * T) * (2 * C) * h ^ 9 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((15 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((15 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh9_nn : 0 ≤ T * Real.exp ((15 * L) * T) * (2 * C) * h ^ 9 :=
      mul_nonneg hKnn hh9_nn
    linarith
  match N, hNh with
  | 0, _ =>
    have hbase : ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      simpa using he0_bd
    exact hbase_to_headline _ hbase
  | 1, _ =>
    have hbase : ‖yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    exact hbase_to_headline _ hbase
  | 2, _ =>
    have hbase : ‖yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    exact hbase_to_headline _ hbase
  | 3, _ =>
    have hbase : ‖yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
    exact hbase_to_headline _ hbase
  | 4, _ =>
    have hbase : ‖yseq 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]; simpa using he4_bd
    exact hbase_to_headline _ hbase
  | 5, _ =>
    have hbase : ‖yseq 5 - y (t₀ + ((5 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((5 : ℕ) : ℝ) * h = 5 * h := by push_cast; ring
      rw [hcast]; simpa using he5_bd
    exact hbase_to_headline _ hbase
  | 6, _ =>
    have hbase : ‖yseq 6 - y (t₀ + ((6 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((6 : ℕ) : ℝ) * h = 6 * h := by push_cast; ring
      rw [hcast]; simpa using he6_bd
    exact hbase_to_headline _ hbase
  | 7, _ =>
    have hbase : ‖yseq 7 - y (t₀ + ((7 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((7 : ℕ) : ℝ) * h = 7 * h := by push_cast; ring
      rw [hcast]; simpa using he7_bd
    exact hbase_to_headline _ hbase
  | N' + 8, hNh =>
    have hcast : (((N' + 8 : ℕ) : ℝ) + 7) = (N' : ℝ) + 15 := by
      push_cast; ring
    have hN_hyp : ((N' : ℝ) + 15) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (15 * L)) * EN n + (2 * C) * h ^ (9 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (9 + 1) = (2 * C) * h ^ 10 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 8 ≤ (N' : ℝ) + 15 := by linarith
      have h_mul : ((n : ℝ) + 8) * h ≤ ((N' : ℝ) + 15) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have hle : (N' : ℝ) + 1 ≤ (N' : ℝ) + 15 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 15 * L) (C := 2 * C) (T := T) (p := 9)
        (e := EN) (N := N' + 1)
        hh.le h15L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 8) ≤ EN (N' + 1) := by
      show eN (N' + 8)
        ≤ max (max (max (max (max (max (max
              (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4)))
              (eN (N' + 1 + 5))) (eN (N' + 1 + 6))) (eN (N' + 1 + 7))
      have heq : N' + 8 = N' + 1 + 7 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((15 * L) * T) * EN 0 ≤ Real.exp ((15 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show ‖yseq (N' + 8) - y (t₀ + ((N' + 8 : ℕ) : ℝ) * h)‖
        ≤ Real.exp ((15 * L) * T) * ε₀
          + T * Real.exp ((15 * L) * T) * (2 * C) * h ^ 9
    have heN_eq :
        eN (N' + 8)
          = ‖yseq (N' + 8) - y (t₀ + ((N' + 8 : ℕ) : ℝ) * h)‖ := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
