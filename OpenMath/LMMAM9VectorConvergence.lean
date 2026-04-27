import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAM8VectorConvergence
import OpenMath.LMMAB10VectorConvergence

/-! ## Adams--Moulton 9-step Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the AM9 scalar quantitative convergence chain in
`OpenMath/LMMAM9Convergence.lean`.  The implicit AM9 update is parameterised
by a supplied trajectory; existence of such a trajectory is a separate
fixed-point problem and is not part of this chain.

The AM9 coefficients are obtained by integrating the Lagrange basis on
nodes 0,…,9 over `[8, 9]`; over the common denominator `7257600` they are
`[57281, -583435, 2687864, -7394032, 13510082, -17283646, 16002320,
 -11271304, 9449717, 2082753]`, summing to `7257600`.

The absolute-weight sum is `78239681/7257600`, so after division by the
implicit new-point factor the growth is slackened to `23L`.  The exact
eleventh-order residual coefficient is approximately `1826.97`, slackened
to `1827`.
-/

namespace LMM

/-- AM9 vector trajectory predicate.  The new value appears inside `f`, so
existence of such a trajectory is a separate fixed-point problem. -/
structure IsAM9TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 9)
      = y (n + 8)
        + h • ((2082753 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 9) * h) (y (n + 9))
             + (9449717 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h) (y (n + 8))
             - (11271304 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h) (y (n + 7))
             + (16002320 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             - (17283646 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             + (13510082 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             - (7394032 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             + (2687864 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             - (583435 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             + (57281 / 7257600 : ℝ) • f (t₀ + (n : ℝ) * h) (y n))

/-- Textbook AM9 vector residual: the value of the local truncation error of
the AM9 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def am9VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 9 * h) - y (t + 8 * h)
    - h • ((2082753 / 7257600 : ℝ) • deriv y (t + 9 * h)
          + (9449717 / 7257600 : ℝ) • deriv y (t + 8 * h)
          - (11271304 / 7257600 : ℝ) • deriv y (t + 7 * h)
          + (16002320 / 7257600 : ℝ) • deriv y (t + 6 * h)
          - (17283646 / 7257600 : ℝ) • deriv y (t + 5 * h)
          + (13510082 / 7257600 : ℝ) • deriv y (t + 4 * h)
          - (7394032 / 7257600 : ℝ) • deriv y (t + 3 * h)
          + (2687864 / 7257600 : ℝ) • deriv y (t + 2 * h)
          - (583435 / 7257600 : ℝ) • deriv y (t + h)
          + (57281 / 7257600 : ℝ) • deriv y t)

theorem am9Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am9VecResidual h t y
      = y (t + 9 * h) - y (t + 8 * h)
          - h • ((2082753 / 7257600 : ℝ) • deriv y (t + 9 * h)
                + (9449717 / 7257600 : ℝ) • deriv y (t + 8 * h)
                - (11271304 / 7257600 : ℝ) • deriv y (t + 7 * h)
                + (16002320 / 7257600 : ℝ) • deriv y (t + 6 * h)
                - (17283646 / 7257600 : ℝ) • deriv y (t + 5 * h)
                + (13510082 / 7257600 : ℝ) • deriv y (t + 4 * h)
                - (7394032 / 7257600 : ℝ) • deriv y (t + 3 * h)
                + (2687864 / 7257600 : ℝ) • deriv y (t + 2 * h)
                - (583435 / 7257600 : ℝ) • deriv y (t + h)
                + (57281 / 7257600 : ℝ) • deriv y t) := by
  rfl

theorem am9Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (2082753 / 7257600 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM9TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (2082753 / 7257600 : ℝ) * h * L)
        * ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
      ≤ ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
        + (9449717 / 7257600 : ℝ) * h * L
            * ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
        + (11271304 / 7257600 : ℝ) * h * L
            * ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
        + (16002320 / 7257600 : ℝ) * h * L
            * ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (17283646 / 7257600 : ℝ) * h * L
            * ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (13510082 / 7257600 : ℝ) * h * L
            * ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (7394032 / 7257600 : ℝ) * h * L
            * ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (2687864 / 7257600 : ℝ) * h * L
            * ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (583435 / 7257600 : ℝ) * h * L
            * ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (57281 / 7257600 : ℝ) * h * L
            * ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + ‖am9VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set yn2 : E := yseq (n + 2) with hyn2_def
  set yn3 : E := yseq (n + 3) with hyn3_def
  set yn4 : E := yseq (n + 4) with hyn4_def
  set yn5 : E := yseq (n + 5) with hyn5_def
  set yn6 : E := yseq (n + 6) with hyn6_def
  set yn7 : E := yseq (n + 7) with hyn7_def
  set yn8 : E := yseq (n + 8) with hyn8_def
  set yn9 : E := yseq (n + 9) with hyn9_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set tn8 : ℝ := t₀ + ((n : ℝ) + 8) * h with htn8_def
  set tn9 : ℝ := t₀ + ((n : ℝ) + 9) * h with htn9_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set zn3 : E := y tn3 with hzn3_def
  set zn4 : E := y tn4 with hzn4_def
  set zn5 : E := y tn5 with hzn5_def
  set zn6 : E := y tn6 with hzn6_def
  set zn7 : E := y tn7 with hzn7_def
  set zn8 : E := y tn8 with hzn8_def
  set zn9 : E := y tn9 with hzn9_def
  set τ : E := am9VecResidual h tn y with hτ_def
  have _hsmall_record : (2082753 / 7257600 : ℝ) * h * L ≤ 1 / 2 := hsmall
  have hstep : yn9
      = yn8
        + h • ((2082753 / 7257600 : ℝ) • f tn9 yn9
             + (9449717 / 7257600 : ℝ) • f tn8 yn8
             - (11271304 / 7257600 : ℝ) • f tn7 yn7
             + (16002320 / 7257600 : ℝ) • f tn6 yn6
             - (17283646 / 7257600 : ℝ) • f tn5 yn5
             + (13510082 / 7257600 : ℝ) • f tn4 yn4
             - (7394032 / 7257600 : ℝ) • f tn3 yn3
             + (2687864 / 7257600 : ℝ) • f tn2 yn2
             - (583435 / 7257600 : ℝ) • f tn1 yn1
             + (57281 / 7257600 : ℝ) • f tn yn) := by
    simpa [hyn9_def, hyn8_def, hyn7_def, hyn6_def, hyn5_def, hyn4_def, hyn3_def,
      hyn2_def, hyn1_def, hyn_def, htn9_def, htn8_def, htn7_def, htn6_def,
      htn5_def, htn4_def, htn3_def, htn2_def, htn1_def, htn_def]
      using hy.recurrence n
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
  have htn_9h : tn + 9 * h = tn9 := by
    simp [htn_def, htn9_def]; ring
  have hτ_eq : τ = zn9 - zn8
      - h • ((2082753 / 7257600 : ℝ) • f tn9 zn9
             + (9449717 / 7257600 : ℝ) • f tn8 zn8
             - (11271304 / 7257600 : ℝ) • f tn7 zn7
             + (16002320 / 7257600 : ℝ) • f tn6 zn6
             - (17283646 / 7257600 : ℝ) • f tn5 zn5
             + (13510082 / 7257600 : ℝ) • f tn4 zn4
             - (7394032 / 7257600 : ℝ) • f tn3 zn3
             + (2687864 / 7257600 : ℝ) • f tn2 zn2
             - (583435 / 7257600 : ℝ) • f tn1 zn1
             + (57281 / 7257600 : ℝ) • f tn zn) := by
    show am9VecResidual h tn y = _
    unfold am9VecResidual
    rw [htn1_h, htn_2h, htn_3h, htn_4h, htn_5h, htn_6h, htn_7h, htn_8h, htn_9h,
      hyf tn9, hyf tn8, hyf tn7, hyf tn6, hyf tn5, hyf tn4, hyf tn3, hyf tn2,
      hyf tn1, hyf tn]
  have halg : yn9 - zn9
      = (yn8 - zn8)
        + h • ((2082753 / 7257600 : ℝ) • (f tn9 yn9 - f tn9 zn9))
        + h • ((9449717 / 7257600 : ℝ) • (f tn8 yn8 - f tn8 zn8))
        - h • ((11271304 / 7257600 : ℝ) • (f tn7 yn7 - f tn7 zn7))
        + h • ((16002320 / 7257600 : ℝ) • (f tn6 yn6 - f tn6 zn6))
        - h • ((17283646 / 7257600 : ℝ) • (f tn5 yn5 - f tn5 zn5))
        + h • ((13510082 / 7257600 : ℝ) • (f tn4 yn4 - f tn4 zn4))
        - h • ((7394032 / 7257600 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        + h • ((2687864 / 7257600 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        - h • ((583435 / 7257600 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        + h • ((57281 / 7257600 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_add]
    abel
  have hLip9 : ‖f tn9 yn9 - f tn9 zn9‖ ≤ L * ‖yn9 - zn9‖ := hf tn9 yn9 zn9
  have hLip8 : ‖f tn8 yn8 - f tn8 zn8‖ ≤ L * ‖yn8 - zn8‖ := hf tn8 yn8 zn8
  have hLip7 : ‖f tn7 yn7 - f tn7 zn7‖ ≤ L * ‖yn7 - zn7‖ := hf tn7 yn7 zn7
  have hLip6 : ‖f tn6 yn6 - f tn6 zn6‖ ≤ L * ‖yn6 - zn6‖ := hf tn6 yn6 zn6
  have hLip5 : ‖f tn5 yn5 - f tn5 zn5‖ ≤ L * ‖yn5 - zn5‖ := hf tn5 yn5 zn5
  have hLip4 : ‖f tn4 yn4 - f tn4 zn4‖ ≤ L * ‖yn4 - zn4‖ := hf tn4 yn4 zn4
  have hLip3 : ‖f tn3 yn3 - f tn3 zn3‖ ≤ L * ‖yn3 - zn3‖ := hf tn3 yn3 zn3
  have hLip2 : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ := hf tn2 yn2 zn2
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ := hf tn1 yn1 zn1
  have hLip0 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ := hf tn yn zn
  have h2082753_nn : (0 : ℝ) ≤ 2082753 / 7257600 := by norm_num
  have h9449717_nn : (0 : ℝ) ≤ 9449717 / 7257600 := by norm_num
  have h11271304_nn : (0 : ℝ) ≤ 11271304 / 7257600 := by norm_num
  have h16002320_nn : (0 : ℝ) ≤ 16002320 / 7257600 := by norm_num
  have h17283646_nn : (0 : ℝ) ≤ 17283646 / 7257600 := by norm_num
  have h13510082_nn : (0 : ℝ) ≤ 13510082 / 7257600 := by norm_num
  have h7394032_nn : (0 : ℝ) ≤ 7394032 / 7257600 := by norm_num
  have h2687864_nn : (0 : ℝ) ≤ 2687864 / 7257600 := by norm_num
  have h583435_nn : (0 : ℝ) ≤ 583435 / 7257600 := by norm_num
  have h57281_nn : (0 : ℝ) ≤ 57281 / 7257600 := by norm_num
  set A : E := yn8 - zn8 with hA_def
  set B2082753 : E := h • ((2082753 / 7257600 : ℝ) • (f tn9 yn9 - f tn9 zn9))
    with hB2082753_def
  set B9449717 : E := h • ((9449717 / 7257600 : ℝ) • (f tn8 yn8 - f tn8 zn8))
    with hB9449717_def
  set B11271304 : E := h • ((11271304 / 7257600 : ℝ) • (f tn7 yn7 - f tn7 zn7))
    with hB11271304_def
  set B16002320 : E := h • ((16002320 / 7257600 : ℝ) • (f tn6 yn6 - f tn6 zn6))
    with hB16002320_def
  set B17283646 : E := h • ((17283646 / 7257600 : ℝ) • (f tn5 yn5 - f tn5 zn5))
    with hB17283646_def
  set B13510082 : E := h • ((13510082 / 7257600 : ℝ) • (f tn4 yn4 - f tn4 zn4))
    with hB13510082_def
  set B7394032 : E := h • ((7394032 / 7257600 : ℝ) • (f tn3 yn3 - f tn3 zn3))
    with hB7394032_def
  set B2687864 : E := h • ((2687864 / 7257600 : ℝ) • (f tn2 yn2 - f tn2 zn2))
    with hB2687864_def
  set B583435 : E := h • ((583435 / 7257600 : ℝ) • (f tn1 yn1 - f tn1 zn1))
    with hB583435_def
  set B57281 : E := h • ((57281 / 7257600 : ℝ) • (f tn yn - f tn zn))
    with hB57281_def
  have halg' :
      yn9 - zn9 = A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032 + B2687864 - B583435 + B57281 - τ := by
    simpa [hA_def, hB2082753_def, hB9449717_def, hB11271304_def, hB16002320_def,
      hB17283646_def, hB13510082_def, hB7394032_def, hB2687864_def, hB583435_def,
      hB57281_def] using halg
  have h2082753_norm :
      ‖B2082753‖ ≤ (2082753 / 7257600 : ℝ) * h * L * ‖yn9 - zn9‖ := by
    rw [hB2082753_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h2082753_nn]
    have : h * ((2082753 / 7257600 : ℝ) * ‖f tn9 yn9 - f tn9 zn9‖)
        ≤ h * ((2082753 / 7257600 : ℝ) * (L * ‖yn9 - zn9‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip9 h2082753_nn
    calc h * ((2082753 / 7257600 : ℝ) * ‖f tn9 yn9 - f tn9 zn9‖)
        ≤ h * ((2082753 / 7257600 : ℝ) * (L * ‖yn9 - zn9‖)) := this
      _ = (2082753 / 7257600 : ℝ) * h * L * ‖yn9 - zn9‖ := by ring
  have h9449717_norm :
      ‖B9449717‖ ≤ (9449717 / 7257600 : ℝ) * h * L * ‖yn8 - zn8‖ := by
    rw [hB9449717_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h9449717_nn]
    have : h * ((9449717 / 7257600 : ℝ) * ‖f tn8 yn8 - f tn8 zn8‖)
        ≤ h * ((9449717 / 7257600 : ℝ) * (L * ‖yn8 - zn8‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip8 h9449717_nn
    calc h * ((9449717 / 7257600 : ℝ) * ‖f tn8 yn8 - f tn8 zn8‖)
        ≤ h * ((9449717 / 7257600 : ℝ) * (L * ‖yn8 - zn8‖)) := this
      _ = (9449717 / 7257600 : ℝ) * h * L * ‖yn8 - zn8‖ := by ring
  have h11271304_norm :
      ‖B11271304‖ ≤ (11271304 / 7257600 : ℝ) * h * L * ‖yn7 - zn7‖ := by
    rw [hB11271304_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h11271304_nn]
    have : h * ((11271304 / 7257600 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((11271304 / 7257600 : ℝ) * (L * ‖yn7 - zn7‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip7 h11271304_nn
    calc h * ((11271304 / 7257600 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((11271304 / 7257600 : ℝ) * (L * ‖yn7 - zn7‖)) := this
      _ = (11271304 / 7257600 : ℝ) * h * L * ‖yn7 - zn7‖ := by ring
  have h16002320_norm :
      ‖B16002320‖ ≤ (16002320 / 7257600 : ℝ) * h * L * ‖yn6 - zn6‖ := by
    rw [hB16002320_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h16002320_nn]
    have : h * ((16002320 / 7257600 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((16002320 / 7257600 : ℝ) * (L * ‖yn6 - zn6‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip6 h16002320_nn
    calc h * ((16002320 / 7257600 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((16002320 / 7257600 : ℝ) * (L * ‖yn6 - zn6‖)) := this
      _ = (16002320 / 7257600 : ℝ) * h * L * ‖yn6 - zn6‖ := by ring
  have h17283646_norm :
      ‖B17283646‖ ≤ (17283646 / 7257600 : ℝ) * h * L * ‖yn5 - zn5‖ := by
    rw [hB17283646_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h17283646_nn]
    have : h * ((17283646 / 7257600 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((17283646 / 7257600 : ℝ) * (L * ‖yn5 - zn5‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip5 h17283646_nn
    calc h * ((17283646 / 7257600 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((17283646 / 7257600 : ℝ) * (L * ‖yn5 - zn5‖)) := this
      _ = (17283646 / 7257600 : ℝ) * h * L * ‖yn5 - zn5‖ := by ring
  have h13510082_norm :
      ‖B13510082‖ ≤ (13510082 / 7257600 : ℝ) * h * L * ‖yn4 - zn4‖ := by
    rw [hB13510082_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h13510082_nn]
    have : h * ((13510082 / 7257600 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((13510082 / 7257600 : ℝ) * (L * ‖yn4 - zn4‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip4 h13510082_nn
    calc h * ((13510082 / 7257600 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((13510082 / 7257600 : ℝ) * (L * ‖yn4 - zn4‖)) := this
      _ = (13510082 / 7257600 : ℝ) * h * L * ‖yn4 - zn4‖ := by ring
  have h7394032_norm :
      ‖B7394032‖ ≤ (7394032 / 7257600 : ℝ) * h * L * ‖yn3 - zn3‖ := by
    rw [hB7394032_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h7394032_nn]
    have : h * ((7394032 / 7257600 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((7394032 / 7257600 : ℝ) * (L * ‖yn3 - zn3‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip3 h7394032_nn
    calc h * ((7394032 / 7257600 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((7394032 / 7257600 : ℝ) * (L * ‖yn3 - zn3‖)) := this
      _ = (7394032 / 7257600 : ℝ) * h * L * ‖yn3 - zn3‖ := by ring
  have h2687864_norm :
      ‖B2687864‖ ≤ (2687864 / 7257600 : ℝ) * h * L * ‖yn2 - zn2‖ := by
    rw [hB2687864_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h2687864_nn]
    have : h * ((2687864 / 7257600 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((2687864 / 7257600 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 h2687864_nn
    calc h * ((2687864 / 7257600 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((2687864 / 7257600 : ℝ) * (L * ‖yn2 - zn2‖)) := this
      _ = (2687864 / 7257600 : ℝ) * h * L * ‖yn2 - zn2‖ := by ring
  have h583435_norm :
      ‖B583435‖ ≤ (583435 / 7257600 : ℝ) * h * L * ‖yn1 - zn1‖ := by
    rw [hB583435_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h583435_nn]
    have : h * ((583435 / 7257600 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((583435 / 7257600 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 h583435_nn
    calc h * ((583435 / 7257600 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((583435 / 7257600 : ℝ) * (L * ‖yn1 - zn1‖)) := this
      _ = (583435 / 7257600 : ℝ) * h * L * ‖yn1 - zn1‖ := by ring
  have h57281_norm :
      ‖B57281‖ ≤ (57281 / 7257600 : ℝ) * h * L * ‖yn - zn‖ := by
    rw [hB57281_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h57281_nn]
    have : h * ((57281 / 7257600 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((57281 / 7257600 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 h57281_nn
    calc h * ((57281 / 7257600 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((57281 / 7257600 : ℝ) * (L * ‖yn - zn‖)) := this
      _ = (57281 / 7257600 : ℝ) * h * L * ‖yn - zn‖ := by ring
  have htri :
      ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032 + B2687864 - B583435 + B57281 - τ‖
        ≤ ‖A‖ + ‖B2082753‖ + ‖B9449717‖ + ‖B11271304‖ + ‖B16002320‖
            + ‖B17283646‖ + ‖B13510082‖ + ‖B7394032‖ + ‖B2687864‖
            + ‖B583435‖ + ‖B57281‖ + ‖τ‖ := by
    have h1 : ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032 + B2687864 - B583435 + B57281 - τ‖
        ≤ ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032 + B2687864 - B583435 + B57281‖ + ‖τ‖ :=
      norm_sub_le _ _
    have h2 : ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032 + B2687864 - B583435 + B57281‖
        ≤ ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032 + B2687864 - B583435‖ + ‖B57281‖ :=
      norm_add_le _ _
    have h3 : ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032 + B2687864 - B583435‖
        ≤ ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032 + B2687864‖ + ‖B583435‖ := norm_sub_le _ _
    have h4 : ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032 + B2687864‖
        ≤ ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032‖ + ‖B2687864‖ := norm_add_le _ _
    have h5 : ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082 - B7394032‖
        ≤ ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082‖ + ‖B7394032‖ := norm_sub_le _ _
    have h6 : ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
          + B13510082‖
        ≤ ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646‖
          + ‖B13510082‖ := norm_add_le _ _
    have h7 : ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646‖
        ≤ ‖A + B2082753 + B9449717 - B11271304 + B16002320‖
          + ‖B17283646‖ := norm_sub_le _ _
    have h8 : ‖A + B2082753 + B9449717 - B11271304 + B16002320‖
        ≤ ‖A + B2082753 + B9449717 - B11271304‖ + ‖B16002320‖ := norm_add_le _ _
    have h9 : ‖A + B2082753 + B9449717 - B11271304‖
        ≤ ‖A + B2082753 + B9449717‖ + ‖B11271304‖ := norm_sub_le _ _
    have h10 : ‖A + B2082753 + B9449717‖
        ≤ ‖A + B2082753‖ + ‖B9449717‖ := norm_add_le _ _
    have h11 : ‖A + B2082753‖ ≤ ‖A‖ + ‖B2082753‖ := norm_add_le _ _
    linarith
  have hmain :
      ‖yn9 - zn9‖
        ≤ ‖yn8 - zn8‖
          + (2082753 / 7257600 : ℝ) * h * L * ‖yn9 - zn9‖
          + (9449717 / 7257600 : ℝ) * h * L * ‖yn8 - zn8‖
          + (11271304 / 7257600 : ℝ) * h * L * ‖yn7 - zn7‖
          + (16002320 / 7257600 : ℝ) * h * L * ‖yn6 - zn6‖
          + (17283646 / 7257600 : ℝ) * h * L * ‖yn5 - zn5‖
          + (13510082 / 7257600 : ℝ) * h * L * ‖yn4 - zn4‖
          + (7394032 / 7257600 : ℝ) * h * L * ‖yn3 - zn3‖
          + (2687864 / 7257600 : ℝ) * h * L * ‖yn2 - zn2‖
          + (583435 / 7257600 : ℝ) * h * L * ‖yn1 - zn1‖
          + (57281 / 7257600 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    calc ‖yn9 - zn9‖
        = ‖A + B2082753 + B9449717 - B11271304 + B16002320 - B17283646
            + B13510082 - B7394032 + B2687864 - B583435 + B57281 - τ‖ := by
            rw [halg']
      _ ≤ ‖A‖ + ‖B2082753‖ + ‖B9449717‖ + ‖B11271304‖ + ‖B16002320‖
          + ‖B17283646‖ + ‖B13510082‖ + ‖B7394032‖ + ‖B2687864‖
          + ‖B583435‖ + ‖B57281‖ + ‖τ‖ := htri
      _ ≤ ‖yn8 - zn8‖
          + (2082753 / 7257600 : ℝ) * h * L * ‖yn9 - zn9‖
          + (9449717 / 7257600 : ℝ) * h * L * ‖yn8 - zn8‖
          + (11271304 / 7257600 : ℝ) * h * L * ‖yn7 - zn7‖
          + (16002320 / 7257600 : ℝ) * h * L * ‖yn6 - zn6‖
          + (17283646 / 7257600 : ℝ) * h * L * ‖yn5 - zn5‖
          + (13510082 / 7257600 : ℝ) * h * L * ‖yn4 - zn4‖
          + (7394032 / 7257600 : ℝ) * h * L * ‖yn3 - zn3‖
          + (2687864 / 7257600 : ℝ) * h * L * ‖yn2 - zn2‖
          + (583435 / 7257600 : ℝ) * h * L * ‖yn1 - zn1‖
          + (57281 / 7257600 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
        rw [hA_def]
        linarith [h2082753_norm, h9449717_norm, h11271304_norm, h16002320_norm,
          h17283646_norm, h13510082_norm, h7394032_norm, h2687864_norm,
          h583435_norm, h57281_norm]
  linarith [hmain]

/-- Divided one-step AM9 vector error bound. -/
theorem am9Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (2082753 / 7257600 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM9TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
      ≤ (1 + h * (23 * L))
            * max (max (max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
                ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
                ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
        + 2 * ‖am9VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
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
  set en9 : ℝ :=
    ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖ with hen9_def
  set τabs : ℝ :=
    ‖am9VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7) en8
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
  have hen9_nn : 0 ≤ en9 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _) (le_max_left _ _))))))))
  have hen_le_E : en ≤ Emax :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
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
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _) (le_max_left _ _)))))))
  have hen2_le_E : en2 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen3_le_E : en3 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen4_le_E : en4 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen5_le_E : en5 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen6_le_E : en6 ≤ Emax :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen7_le_E : en7 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen8_le_E : en8 ≤ Emax := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 3628800 / 2082753 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (2082753 / 7257600 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (2082753 / 7257600 : ℝ) * h * L) * en9
        ≤ en8
          + (9449717 / 7257600 : ℝ) * h * L * en8
          + (11271304 / 7257600 : ℝ) * h * L * en7
          + (16002320 / 7257600 : ℝ) * h * L * en6
          + (17283646 / 7257600 : ℝ) * h * L * en5
          + (13510082 / 7257600 : ℝ) * h * L * en4
          + (7394032 / 7257600 : ℝ) * h * L * en3
          + (2687864 / 7257600 : ℝ) * h * L * en2
          + (583435 / 7257600 : ℝ) * h * L * en1
          + (57281 / 7257600 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hen9_def, hτabs_def]
      using
      (am9Vec_one_step_lipschitz (E := E) (h := h) (L := L)
        hh hsmall hf t₀ hy y hyf n)
  have h9449717_nn : 0 ≤ (9449717 / 7257600 : ℝ) * h * L := by positivity
  have h11271304_nn : 0 ≤ (11271304 / 7257600 : ℝ) * h * L := by positivity
  have h16002320_nn : 0 ≤ (16002320 / 7257600 : ℝ) * h * L := by positivity
  have h17283646_nn : 0 ≤ (17283646 / 7257600 : ℝ) * h * L := by positivity
  have h13510082_nn : 0 ≤ (13510082 / 7257600 : ℝ) * h * L := by positivity
  have h7394032_nn : 0 ≤ (7394032 / 7257600 : ℝ) * h * L := by positivity
  have h2687864_nn : 0 ≤ (2687864 / 7257600 : ℝ) * h * L := by positivity
  have h583435_nn : 0 ≤ (583435 / 7257600 : ℝ) * h * L := by positivity
  have h57281_nn : 0 ≤ (57281 / 7257600 : ℝ) * h * L := by positivity
  have h9449717_le :
      (9449717 / 7257600 : ℝ) * h * L * en8
        ≤ (9449717 / 7257600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen8_le_E h9449717_nn
  have h11271304_le :
      (11271304 / 7257600 : ℝ) * h * L * en7
        ≤ (11271304 / 7257600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen7_le_E h11271304_nn
  have h16002320_le :
      (16002320 / 7257600 : ℝ) * h * L * en6
        ≤ (16002320 / 7257600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen6_le_E h16002320_nn
  have h17283646_le :
      (17283646 / 7257600 : ℝ) * h * L * en5
        ≤ (17283646 / 7257600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen5_le_E h17283646_nn
  have h13510082_le :
      (13510082 / 7257600 : ℝ) * h * L * en4
        ≤ (13510082 / 7257600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen4_le_E h13510082_nn
  have h7394032_le :
      (7394032 / 7257600 : ℝ) * h * L * en3
        ≤ (7394032 / 7257600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen3_le_E h7394032_nn
  have h2687864_le :
      (2687864 / 7257600 : ℝ) * h * L * en2
        ≤ (2687864 / 7257600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen2_le_E h2687864_nn
  have h583435_le :
      (583435 / 7257600 : ℝ) * h * L * en1
        ≤ (583435 / 7257600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen1_le_E h583435_nn
  have h57281_le :
      (57281 / 7257600 : ℝ) * h * L * en
        ≤ (57281 / 7257600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen_le_E h57281_nn
  have hR_le :
      en8
          + (9449717 / 7257600 : ℝ) * h * L * en8
          + (11271304 / 7257600 : ℝ) * h * L * en7
          + (16002320 / 7257600 : ℝ) * h * L * en6
          + (17283646 / 7257600 : ℝ) * h * L * en5
          + (13510082 / 7257600 : ℝ) * h * L * en4
          + (7394032 / 7257600 : ℝ) * h * L * en3
          + (2687864 / 7257600 : ℝ) * h * L * en2
          + (583435 / 7257600 : ℝ) * h * L * en1
          + (57281 / 7257600 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (78239681 / 7257600 : ℝ) * (h * L)) * Emax + τabs := by
    have h_alg :
        Emax + (9449717 / 7257600 : ℝ) * h * L * Emax
            + (11271304 / 7257600 : ℝ) * h * L * Emax
            + (16002320 / 7257600 : ℝ) * h * L * Emax
            + (17283646 / 7257600 : ℝ) * h * L * Emax
            + (13510082 / 7257600 : ℝ) * h * L * Emax
            + (7394032 / 7257600 : ℝ) * h * L * Emax
            + (2687864 / 7257600 : ℝ) * h * L * Emax
            + (583435 / 7257600 : ℝ) * h * L * Emax
            + (57281 / 7257600 : ℝ) * h * L * Emax + τabs
          = (1 + (78239681 / 7257600 : ℝ) * (h * L)) * Emax + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (78239681 / 7257600 : ℝ) * (h * L)
        ≤ (1 - (2082753 / 7257600 : ℝ) * h * L) * (1 + h * (23 * L)) := by
    have hxL_eq :
        (1 - (2082753 / 7257600 : ℝ) * h * L) * (1 + h * (23 * L))
          - (1 + (78239681 / 7257600 : ℝ) * (h * L))
          = (h * L) / 7257600 * (86602366 - 47903319 * (h * L)) := by ring
    have hpos : 0 ≤ 86602366 - 47903319 * (h * L) := by
      have hbound : 47903319 * (h * L) ≤ 47903319 * (3628800 / 2082753) := by
        have h47903319_nn : (0 : ℝ) ≤ 47903319 := by norm_num
        exact mul_le_mul_of_nonneg_left hx_small h47903319_nn
      have hnum : (47903319 : ℝ) * (3628800 / 2082753) ≤ 86602366 := by
        norm_num
      linarith
    have hprod : 0 ≤ (h * L) / 7257600 * (86602366 - 47903319 * (h * L)) := by
      apply mul_nonneg
      · positivity
      · exact hpos
    linarith
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (2082753 / 7257600 : ℝ) * h * L) * 2 := by
    linarith [hsmall]
  have hE_part :
      (1 + (78239681 / 7257600 : ℝ) * (h * L)) * Emax
        ≤ ((1 - (2082753 / 7257600 : ℝ) * h * L) * (1 + h * (23 * L))) * Emax :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (2082753 / 7257600 : ℝ) * h * L) * 2) * τabs :=
    by simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (78239681 / 7257600 : ℝ) * (h * L)) * Emax + τabs
        ≤ (1 - (2082753 / 7257600 : ℝ) * h * L)
            * ((1 + h * (23 * L)) * Emax + 2 * τabs) := by
    have hsplit :
        (1 - (2082753 / 7257600 : ℝ) * h * L)
            * ((1 + h * (23 * L)) * Emax + 2 * τabs)
          = ((1 - (2082753 / 7257600 : ℝ) * h * L) * (1 + h * (23 * L))) * Emax
              + ((1 - (2082753 / 7257600 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (2082753 / 7257600 : ℝ) * h * L) * en9
        ≤ (1 - (2082753 / 7257600 : ℝ) * h * L)
            * ((1 + h * (23 * L)) * Emax + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  exact le_of_mul_le_mul_left hprod hA_pos

theorem am9Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (2082753 / 7257600 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM9TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max (max
          ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
          ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
          ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
          ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖)
          ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
      ≤ (1 + h * (23 * L))
            * max (max (max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
                ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
                ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
        + 2 * ‖am9VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
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
  set en9 : ℝ :=
    ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖ with hen9_def
  set τabs : ℝ :=
    ‖am9VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7) en8
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
  have hen9_nn : 0 ≤ en9 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _) (le_max_left _ _))))))))
  have hen1_le_E : en1 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _) (le_max_left _ _)))))))
  have hen2_le_E : en2 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen3_le_E : en3 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen4_le_E : en4 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen5_le_E : en5 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen6_le_E : en6 ≤ Emax :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen7_le_E : en7 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen8_le_E : en8 ≤ Emax := le_max_right _ _
  have h23hL_nn : 0 ≤ h * (23 * L) := by positivity
  have hen9_bd :
      en9 ≤ (1 + h * (23 * L)) * Emax + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hen9_def, hτabs_def, hE_def]
      using
      (am9Vec_one_step_error_bound (E := E) (h := h) (L := L)
        hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : Emax ≤ (1 + h * (23 * L)) * Emax := by
    have hone : (1 : ℝ) * Emax ≤ (1 + h * (23 * L)) * Emax :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (23 * L)) * Emax + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (23 * L)) * Emax + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (23 * L)) * Emax + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  have hen4_bd : en4 ≤ (1 + h * (23 * L)) * Emax + 2 * τabs := by
    linarith [hen4_le_E, hE_le_grow]
  have hen5_bd : en5 ≤ (1 + h * (23 * L)) * Emax + 2 * τabs := by
    linarith [hen5_le_E, hE_le_grow]
  have hen6_bd : en6 ≤ (1 + h * (23 * L)) * Emax + 2 * τabs := by
    linarith [hen6_le_E, hE_le_grow]
  have hen7_bd : en7 ≤ (1 + h * (23 * L)) * Emax + 2 * τabs := by
    linarith [hen7_le_E, hE_le_grow]
  have hen8_bd : en8 ≤ (1 + h * (23 * L)) * Emax + 2 * τabs := by
    linarith [hen8_le_E, hE_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le
    hen1_bd hen2_bd) hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd)
    hen9_bd

/-- Pure module-algebra identity for the AM9 vector residual: the
truncation residual equals an eleven-term abstract split where each chunk
is an order-10 (or order-11) Taylor remainder. -/
private lemma am9Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y8 y9 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
        dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd
        dddddddddd : E) (h : ℝ) :
    y9 - y8
        - h • ((2082753 / 7257600 : ℝ) • d9
              + (9449717 / 7257600 : ℝ) • d8
              - (11271304 / 7257600 : ℝ) • d7
              + (16002320 / 7257600 : ℝ) • d6
              - (17283646 / 7257600 : ℝ) • d5
              + (13510082 / 7257600 : ℝ) • d4
              - (7394032 / 7257600 : ℝ) • d3
              + (2687864 / 7257600 : ℝ) • d2
              - (583435 / 7257600 : ℝ) • d1
              + (57281 / 7257600 : ℝ) • d0)
      = (y9 - y0 - (9 * h) • d0
            - ((9 * h) ^ 2 / 2) • dd
            - ((9 * h) ^ 3 / 6) • ddd
            - ((9 * h) ^ 4 / 24) • dddd
            - ((9 * h) ^ 5 / 120) • ddddd
            - ((9 * h) ^ 6 / 720) • dddddd
            - ((9 * h) ^ 7 / 5040) • ddddddd
            - ((9 * h) ^ 8 / 40320) • dddddddd
            - ((9 * h) ^ 9 / 362880) • ddddddddd
            - ((9 * h) ^ 10 / 3628800) • dddddddddd)
        - (y8 - y0 - (8 * h) • d0
            - ((8 * h) ^ 2 / 2) • dd
            - ((8 * h) ^ 3 / 6) • ddd
            - ((8 * h) ^ 4 / 24) • dddd
            - ((8 * h) ^ 5 / 120) • ddddd
            - ((8 * h) ^ 6 / 720) • dddddd
            - ((8 * h) ^ 7 / 5040) • ddddddd
            - ((8 * h) ^ 8 / 40320) • dddddddd
            - ((8 * h) ^ 9 / 362880) • ddddddddd
            - ((8 * h) ^ 10 / 3628800) • dddddddddd)
        - (2082753 * h / 7257600 : ℝ)
            • (d9 - d0 - (9 * h) • dd
                - ((9 * h) ^ 2 / 2) • ddd
                - ((9 * h) ^ 3 / 6) • dddd
                - ((9 * h) ^ 4 / 24) • ddddd
                - ((9 * h) ^ 5 / 120) • dddddd
                - ((9 * h) ^ 6 / 720) • ddddddd
                - ((9 * h) ^ 7 / 5040) • dddddddd
                - ((9 * h) ^ 8 / 40320) • ddddddddd
                - ((9 * h) ^ 9 / 362880) • dddddddddd)
        - (9449717 * h / 7257600 : ℝ)
            • (d8 - d0 - (8 * h) • dd
                - ((8 * h) ^ 2 / 2) • ddd
                - ((8 * h) ^ 3 / 6) • dddd
                - ((8 * h) ^ 4 / 24) • ddddd
                - ((8 * h) ^ 5 / 120) • dddddd
                - ((8 * h) ^ 6 / 720) • ddddddd
                - ((8 * h) ^ 7 / 5040) • dddddddd
                - ((8 * h) ^ 8 / 40320) • ddddddddd
                - ((8 * h) ^ 9 / 362880) • dddddddddd)
        + (11271304 * h / 7257600 : ℝ)
            • (d7 - d0 - (7 * h) • dd
                - ((7 * h) ^ 2 / 2) • ddd
                - ((7 * h) ^ 3 / 6) • dddd
                - ((7 * h) ^ 4 / 24) • ddddd
                - ((7 * h) ^ 5 / 120) • dddddd
                - ((7 * h) ^ 6 / 720) • ddddddd
                - ((7 * h) ^ 7 / 5040) • dddddddd
                - ((7 * h) ^ 8 / 40320) • ddddddddd
                - ((7 * h) ^ 9 / 362880) • dddddddddd)
        - (16002320 * h / 7257600 : ℝ)
            • (d6 - d0 - (6 * h) • dd
                - ((6 * h) ^ 2 / 2) • ddd
                - ((6 * h) ^ 3 / 6) • dddd
                - ((6 * h) ^ 4 / 24) • ddddd
                - ((6 * h) ^ 5 / 120) • dddddd
                - ((6 * h) ^ 6 / 720) • ddddddd
                - ((6 * h) ^ 7 / 5040) • dddddddd
                - ((6 * h) ^ 8 / 40320) • ddddddddd
                - ((6 * h) ^ 9 / 362880) • dddddddddd)
        + (17283646 * h / 7257600 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd
                - ((5 * h) ^ 6 / 720) • ddddddd
                - ((5 * h) ^ 7 / 5040) • dddddddd
                - ((5 * h) ^ 8 / 40320) • ddddddddd
                - ((5 * h) ^ 9 / 362880) • dddddddddd)
        - (13510082 * h / 7257600 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd
                - ((4 * h) ^ 6 / 720) • ddddddd
                - ((4 * h) ^ 7 / 5040) • dddddddd
                - ((4 * h) ^ 8 / 40320) • ddddddddd
                - ((4 * h) ^ 9 / 362880) • dddddddddd)
        + (7394032 * h / 7257600 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd
                - ((3 * h) ^ 6 / 720) • ddddddd
                - ((3 * h) ^ 7 / 5040) • dddddddd
                - ((3 * h) ^ 8 / 40320) • ddddddddd
                - ((3 * h) ^ 9 / 362880) • dddddddddd)
        - (2687864 * h / 7257600 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd
                - ((2 * h) ^ 6 / 720) • ddddddd
                - ((2 * h) ^ 7 / 5040) • dddddddd
                - ((2 * h) ^ 8 / 40320) • ddddddddd
                - ((2 * h) ^ 9 / 362880) • dddddddddd)
        + (583435 * h / 7257600 : ℝ)
            • (d1 - d0 - h • dd
                - (h ^ 2 / 2) • ddd
                - (h ^ 3 / 6) • dddd
                - (h ^ 4 / 24) • ddddd
                - (h ^ 5 / 120) • dddddd
                - (h ^ 6 / 720) • ddddddd
                - (h ^ 7 / 5040) • dddddddd
                - (h ^ 8 / 40320) • ddddddddd
                - (h ^ 9 / 362880) • dddddddddd) := by
  simp only [smul_sub, smul_add, smul_smul]
  module

/-- Pure ring identity for the upper bound on the AM9 vector residual. -/
private lemma am9Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 39916800 * (9 * h) ^ 11 + M / 39916800 * (8 * h) ^ 11
      + (2082753 * h / 7257600) * (M / 3628800 * (9 * h) ^ 10)
      + (9449717 * h / 7257600) * (M / 3628800 * (8 * h) ^ 10)
      + (11271304 * h / 7257600) * (M / 3628800 * (7 * h) ^ 10)
      + (16002320 * h / 7257600) * (M / 3628800 * (6 * h) ^ 10)
      + (17283646 * h / 7257600) * (M / 3628800 * (5 * h) ^ 10)
      + (13510082 * h / 7257600) * (M / 3628800 * (4 * h) ^ 10)
      + (7394032 * h / 7257600) * (M / 3628800 * (3 * h) ^ 10)
      + (2687864 * h / 7257600) * (M / 3628800 * (2 * h) ^ 10)
      + (583435 * h / 7257600) * (M / 3628800 * h ^ 10)
      = (88212037990481513 / 48283361280000 : ℝ) * M * h ^ 11 := by
  ring

/-- Triangle inequality for the eleven-term AM9 vector residual chunk. -/
private lemma am9Vec_residual_eleven_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G I J K L P : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (2082753 * h / 7257600 : ℝ) • C
        - (9449717 * h / 7257600 : ℝ) • D
        + (11271304 * h / 7257600 : ℝ) • F
        - (16002320 * h / 7257600 : ℝ) • G
        + (17283646 * h / 7257600 : ℝ) • I
        - (13510082 * h / 7257600 : ℝ) • J
        + (7394032 * h / 7257600 : ℝ) • K
        - (2687864 * h / 7257600 : ℝ) • L
        + (583435 * h / 7257600 : ℝ) • P‖
      ≤ ‖A‖ + ‖B‖ + (2082753 * h / 7257600) * ‖C‖
          + (9449717 * h / 7257600) * ‖D‖
          + (11271304 * h / 7257600) * ‖F‖
          + (16002320 * h / 7257600) * ‖G‖
          + (17283646 * h / 7257600) * ‖I‖
          + (13510082 * h / 7257600) * ‖J‖
          + (7394032 * h / 7257600) * ‖K‖
          + (2687864 * h / 7257600) * ‖L‖
          + (583435 * h / 7257600) * ‖P‖ := by
  have hc9_nn : 0 ≤ (2082753 * h / 7257600 : ℝ) := by linarith
  have hc8_nn : 0 ≤ (9449717 * h / 7257600 : ℝ) := by linarith
  have hc7_nn : 0 ≤ (11271304 * h / 7257600 : ℝ) := by linarith
  have hc6_nn : 0 ≤ (16002320 * h / 7257600 : ℝ) := by linarith
  have hc5_nn : 0 ≤ (17283646 * h / 7257600 : ℝ) := by linarith
  have hc4_nn : 0 ≤ (13510082 * h / 7257600 : ℝ) := by linarith
  have hc3_nn : 0 ≤ (7394032 * h / 7257600 : ℝ) := by linarith
  have hc2_nn : 0 ≤ (2687864 * h / 7257600 : ℝ) := by linarith
  have hc1_nn : 0 ≤ (583435 * h / 7257600 : ℝ) := by linarith
  have hC_norm : ‖(2082753 * h / 7257600 : ℝ) • C‖
      = (2082753 * h / 7257600) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc9_nn]
  have hD_norm : ‖(9449717 * h / 7257600 : ℝ) • D‖
      = (9449717 * h / 7257600) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc8_nn]
  have hF_norm : ‖(11271304 * h / 7257600 : ℝ) • F‖
      = (11271304 * h / 7257600) * ‖F‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc7_nn]
  have hG_norm : ‖(16002320 * h / 7257600 : ℝ) • G‖
      = (16002320 * h / 7257600) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc6_nn]
  have hI_norm : ‖(17283646 * h / 7257600 : ℝ) • I‖
      = (17283646 * h / 7257600) * ‖I‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc5_nn]
  have hJ_norm : ‖(13510082 * h / 7257600 : ℝ) • J‖
      = (13510082 * h / 7257600) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc4_nn]
  have hK_norm : ‖(7394032 * h / 7257600 : ℝ) • K‖
      = (7394032 * h / 7257600) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc3_nn]
  have hL_norm : ‖(2687864 * h / 7257600 : ℝ) • L‖
      = (2687864 * h / 7257600) * ‖L‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc2_nn]
  have hP_norm : ‖(583435 * h / 7257600 : ℝ) • P‖
      = (583435 * h / 7257600) * ‖P‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc1_nn]
  -- 11-term triangle: 11 norm bounds via norm_add_le / norm_sub_le
  have h1 :
      ‖A - B - (2082753 * h / 7257600 : ℝ) • C
          - (9449717 * h / 7257600 : ℝ) • D
          + (11271304 * h / 7257600 : ℝ) • F
          - (16002320 * h / 7257600 : ℝ) • G
          + (17283646 * h / 7257600 : ℝ) • I
          - (13510082 * h / 7257600 : ℝ) • J
          + (7394032 * h / 7257600 : ℝ) • K
          - (2687864 * h / 7257600 : ℝ) • L
          + (583435 * h / 7257600 : ℝ) • P‖
        ≤ ‖A - B - (2082753 * h / 7257600 : ℝ) • C
            - (9449717 * h / 7257600 : ℝ) • D
            + (11271304 * h / 7257600 : ℝ) • F
            - (16002320 * h / 7257600 : ℝ) • G
            + (17283646 * h / 7257600 : ℝ) • I
            - (13510082 * h / 7257600 : ℝ) • J
            + (7394032 * h / 7257600 : ℝ) • K
            - (2687864 * h / 7257600 : ℝ) • L‖
          + ‖(583435 * h / 7257600 : ℝ) • P‖ := norm_add_le _ _
  have h2 :
      ‖A - B - (2082753 * h / 7257600 : ℝ) • C
          - (9449717 * h / 7257600 : ℝ) • D
          + (11271304 * h / 7257600 : ℝ) • F
          - (16002320 * h / 7257600 : ℝ) • G
          + (17283646 * h / 7257600 : ℝ) • I
          - (13510082 * h / 7257600 : ℝ) • J
          + (7394032 * h / 7257600 : ℝ) • K
          - (2687864 * h / 7257600 : ℝ) • L‖
        ≤ ‖A - B - (2082753 * h / 7257600 : ℝ) • C
            - (9449717 * h / 7257600 : ℝ) • D
            + (11271304 * h / 7257600 : ℝ) • F
            - (16002320 * h / 7257600 : ℝ) • G
            + (17283646 * h / 7257600 : ℝ) • I
            - (13510082 * h / 7257600 : ℝ) • J
            + (7394032 * h / 7257600 : ℝ) • K‖
          + ‖(2687864 * h / 7257600 : ℝ) • L‖ := norm_sub_le _ _
  have h3 :
      ‖A - B - (2082753 * h / 7257600 : ℝ) • C
          - (9449717 * h / 7257600 : ℝ) • D
          + (11271304 * h / 7257600 : ℝ) • F
          - (16002320 * h / 7257600 : ℝ) • G
          + (17283646 * h / 7257600 : ℝ) • I
          - (13510082 * h / 7257600 : ℝ) • J
          + (7394032 * h / 7257600 : ℝ) • K‖
        ≤ ‖A - B - (2082753 * h / 7257600 : ℝ) • C
            - (9449717 * h / 7257600 : ℝ) • D
            + (11271304 * h / 7257600 : ℝ) • F
            - (16002320 * h / 7257600 : ℝ) • G
            + (17283646 * h / 7257600 : ℝ) • I
            - (13510082 * h / 7257600 : ℝ) • J‖
          + ‖(7394032 * h / 7257600 : ℝ) • K‖ := norm_add_le _ _
  have h4 :
      ‖A - B - (2082753 * h / 7257600 : ℝ) • C
          - (9449717 * h / 7257600 : ℝ) • D
          + (11271304 * h / 7257600 : ℝ) • F
          - (16002320 * h / 7257600 : ℝ) • G
          + (17283646 * h / 7257600 : ℝ) • I
          - (13510082 * h / 7257600 : ℝ) • J‖
        ≤ ‖A - B - (2082753 * h / 7257600 : ℝ) • C
            - (9449717 * h / 7257600 : ℝ) • D
            + (11271304 * h / 7257600 : ℝ) • F
            - (16002320 * h / 7257600 : ℝ) • G
            + (17283646 * h / 7257600 : ℝ) • I‖
          + ‖(13510082 * h / 7257600 : ℝ) • J‖ := norm_sub_le _ _
  have h5 :
      ‖A - B - (2082753 * h / 7257600 : ℝ) • C
          - (9449717 * h / 7257600 : ℝ) • D
          + (11271304 * h / 7257600 : ℝ) • F
          - (16002320 * h / 7257600 : ℝ) • G
          + (17283646 * h / 7257600 : ℝ) • I‖
        ≤ ‖A - B - (2082753 * h / 7257600 : ℝ) • C
            - (9449717 * h / 7257600 : ℝ) • D
            + (11271304 * h / 7257600 : ℝ) • F
            - (16002320 * h / 7257600 : ℝ) • G‖
          + ‖(17283646 * h / 7257600 : ℝ) • I‖ := norm_add_le _ _
  have h6 :
      ‖A - B - (2082753 * h / 7257600 : ℝ) • C
          - (9449717 * h / 7257600 : ℝ) • D
          + (11271304 * h / 7257600 : ℝ) • F
          - (16002320 * h / 7257600 : ℝ) • G‖
        ≤ ‖A - B - (2082753 * h / 7257600 : ℝ) • C
            - (9449717 * h / 7257600 : ℝ) • D
            + (11271304 * h / 7257600 : ℝ) • F‖
          + ‖(16002320 * h / 7257600 : ℝ) • G‖ := norm_sub_le _ _
  have h7 :
      ‖A - B - (2082753 * h / 7257600 : ℝ) • C
          - (9449717 * h / 7257600 : ℝ) • D
          + (11271304 * h / 7257600 : ℝ) • F‖
        ≤ ‖A - B - (2082753 * h / 7257600 : ℝ) • C
            - (9449717 * h / 7257600 : ℝ) • D‖
          + ‖(11271304 * h / 7257600 : ℝ) • F‖ := norm_add_le _ _
  have h8 :
      ‖A - B - (2082753 * h / 7257600 : ℝ) • C
          - (9449717 * h / 7257600 : ℝ) • D‖
        ≤ ‖A - B - (2082753 * h / 7257600 : ℝ) • C‖
          + ‖(9449717 * h / 7257600 : ℝ) • D‖ := norm_sub_le _ _
  have h9 :
      ‖A - B - (2082753 * h / 7257600 : ℝ) • C‖
        ≤ ‖A - B‖ + ‖(2082753 * h / 7257600 : ℝ) • C‖ := norm_sub_le _ _
  have h10 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith [hC_norm.le, hC_norm.ge, hD_norm.le, hD_norm.ge,
    hF_norm.le, hF_norm.ge, hG_norm.le, hG_norm.ge, hI_norm.le,
    hI_norm.ge, hJ_norm.le, hJ_norm.ge, hK_norm.le, hK_norm.ge,
    hL_norm.le, hL_norm.ge, hP_norm.le, hP_norm.ge]

/-- Combine the eleven-term triangle inequality with the norm bounds on
each piece to obtain the `1827 · M · h^11` final AM9 vector residual bound. -/
private lemma am9Vec_residual_combine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D F G I J K L P : E)
    (htri : ‖A - B - (2082753 * h / 7257600 : ℝ) • C
              - (9449717 * h / 7257600 : ℝ) • D
              + (11271304 * h / 7257600 : ℝ) • F
              - (16002320 * h / 7257600 : ℝ) • G
              + (17283646 * h / 7257600 : ℝ) • I
              - (13510082 * h / 7257600 : ℝ) • J
              + (7394032 * h / 7257600 : ℝ) • K
              - (2687864 * h / 7257600 : ℝ) • L
              + (583435 * h / 7257600 : ℝ) • P‖
            ≤ ‖A‖ + ‖B‖ + (2082753 * h / 7257600) * ‖C‖
              + (9449717 * h / 7257600) * ‖D‖
              + (11271304 * h / 7257600) * ‖F‖
              + (16002320 * h / 7257600) * ‖G‖
              + (17283646 * h / 7257600) * ‖I‖
              + (13510082 * h / 7257600) * ‖J‖
              + (7394032 * h / 7257600) * ‖K‖
              + (2687864 * h / 7257600) * ‖L‖
              + (583435 * h / 7257600) * ‖P‖)
    (hA_bd : ‖A‖ ≤ M / 39916800 * (9 * h) ^ 11)
    (hB_bd : ‖B‖ ≤ M / 39916800 * (8 * h) ^ 11)
    (hC_bd : ‖C‖ ≤ M / 3628800 * (9 * h) ^ 10)
    (hD_bd : ‖D‖ ≤ M / 3628800 * (8 * h) ^ 10)
    (hF_bd : ‖F‖ ≤ M / 3628800 * (7 * h) ^ 10)
    (hG_bd : ‖G‖ ≤ M / 3628800 * (6 * h) ^ 10)
    (hI_bd : ‖I‖ ≤ M / 3628800 * (5 * h) ^ 10)
    (hJ_bd : ‖J‖ ≤ M / 3628800 * (4 * h) ^ 10)
    (hK_bd : ‖K‖ ≤ M / 3628800 * (3 * h) ^ 10)
    (hL_bd : ‖L‖ ≤ M / 3628800 * (2 * h) ^ 10)
    (hP_bd : ‖P‖ ≤ M / 3628800 * h ^ 10) :
    ‖A - B - (2082753 * h / 7257600 : ℝ) • C
        - (9449717 * h / 7257600 : ℝ) • D
        + (11271304 * h / 7257600 : ℝ) • F
        - (16002320 * h / 7257600 : ℝ) • G
        + (17283646 * h / 7257600 : ℝ) • I
        - (13510082 * h / 7257600 : ℝ) • J
        + (7394032 * h / 7257600 : ℝ) • K
        - (2687864 * h / 7257600 : ℝ) • L
        + (583435 * h / 7257600 : ℝ) • P‖
      ≤ (1827 : ℝ) * M * h ^ 11 := by
  have hc9_nn : 0 ≤ (2082753 * h / 7257600 : ℝ) := by linarith
  have hc8_nn : 0 ≤ (9449717 * h / 7257600 : ℝ) := by linarith
  have hc7_nn : 0 ≤ (11271304 * h / 7257600 : ℝ) := by linarith
  have hc6_nn : 0 ≤ (16002320 * h / 7257600 : ℝ) := by linarith
  have hc5_nn : 0 ≤ (17283646 * h / 7257600 : ℝ) := by linarith
  have hc4_nn : 0 ≤ (13510082 * h / 7257600 : ℝ) := by linarith
  have hc3_nn : 0 ≤ (7394032 * h / 7257600 : ℝ) := by linarith
  have hc2_nn : 0 ≤ (2687864 * h / 7257600 : ℝ) := by linarith
  have hc1_nn : 0 ≤ (583435 * h / 7257600 : ℝ) := by linarith
  have hCbd_s : (2082753 * h / 7257600) * ‖C‖
      ≤ (2082753 * h / 7257600) * (M / 3628800 * (9 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hC_bd hc9_nn
  have hDbd_s : (9449717 * h / 7257600) * ‖D‖
      ≤ (9449717 * h / 7257600) * (M / 3628800 * (8 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hD_bd hc8_nn
  have hFbd_s : (11271304 * h / 7257600) * ‖F‖
      ≤ (11271304 * h / 7257600) * (M / 3628800 * (7 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hF_bd hc7_nn
  have hGbd_s : (16002320 * h / 7257600) * ‖G‖
      ≤ (16002320 * h / 7257600) * (M / 3628800 * (6 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hG_bd hc6_nn
  have hIbd_s : (17283646 * h / 7257600) * ‖I‖
      ≤ (17283646 * h / 7257600) * (M / 3628800 * (5 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hI_bd hc5_nn
  have hJbd_s : (13510082 * h / 7257600) * ‖J‖
      ≤ (13510082 * h / 7257600) * (M / 3628800 * (4 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hJ_bd hc4_nn
  have hKbd_s : (7394032 * h / 7257600) * ‖K‖
      ≤ (7394032 * h / 7257600) * (M / 3628800 * (3 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hK_bd hc3_nn
  have hLbd_s : (2687864 * h / 7257600) * ‖L‖
      ≤ (2687864 * h / 7257600) * (M / 3628800 * (2 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hL_bd hc2_nn
  have hPbd_s : (583435 * h / 7257600) * ‖P‖
      ≤ (583435 * h / 7257600) * (M / 3628800 * h ^ 10) :=
    mul_le_mul_of_nonneg_left hP_bd hc1_nn
  have hbound_alg := am9Vec_residual_bound_alg_identity M h
  have hh11_nn : 0 ≤ h ^ 11 := by positivity
  have hMh11_nn : 0 ≤ M * h ^ 11 := mul_nonneg hMnn hh11_nn
  have hslack :
      (88212037990481513 / 48283361280000 : ℝ) * M * h ^ 11
        ≤ 1827 * M * h ^ 11 := by
    have hle : (88212037990481513 / 48283361280000 : ℝ) ≤ 1827 := by norm_num
    have hbase :
        (88212037990481513 / 48283361280000 : ℝ) * (M * h ^ 11)
          ≤ 1827 * (M * h ^ 11) :=
      mul_le_mul_of_nonneg_right hle hMh11_nn
    have hL' : (88212037990481513 / 48283361280000 : ℝ) * M * h ^ 11
        = (88212037990481513 / 48283361280000 : ℝ) * (M * h ^ 11) := by ring
    have hR : (1827 : ℝ) * M * h ^ 11 = 1827 * (M * h ^ 11) := by ring
    rw [hL', hR]
    exact hbase
  linarith [htri, hA_bd, hB_bd, hCbd_s, hDbd_s, hFbd_s, hGbd_s, hIbd_s,
    hJbd_s, hKbd_s, hLbd_s, hPbd_s, hbound_alg.le, hbound_alg.ge, hslack]

theorem am9Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 11 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 11 y t‖ ≤ M)
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
    (hh : 0 ≤ h) :
    ‖y (t + 9 * h) - y (t + 8 * h)
        - h • ((2082753 / 7257600 : ℝ) • deriv y (t + 9 * h)
              + (9449717 / 7257600 : ℝ) • deriv y (t + 8 * h)
              - (11271304 / 7257600 : ℝ) • deriv y (t + 7 * h)
              + (16002320 / 7257600 : ℝ) • deriv y (t + 6 * h)
              - (17283646 / 7257600 : ℝ) • deriv y (t + 5 * h)
              + (13510082 / 7257600 : ℝ) • deriv y (t + 4 * h)
              - (7394032 / 7257600 : ℝ) • deriv y (t + 3 * h)
              + (2687864 / 7257600 : ℝ) • deriv y (t + 2 * h)
              - (583435 / 7257600 : ℝ) • deriv y (t + h)
              + (57281 / 7257600 : ℝ) • deriv y t)‖
      ≤ (1827 : ℝ) * M * h ^ 11 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have h9h : 0 ≤ 9 * h := by linarith
  have hRy8 :=
    y_eleventh_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRy9 :=
    y_eleventh_order_taylor_remainder_vec hy hbnd ht ht9h h9h
  have hRyp1 :=
    derivY_tenth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_tenth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_tenth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_tenth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_tenth_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_tenth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_tenth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_tenth_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_tenth_order_taylor_remainder_vec hy hbnd ht ht9h h9h
  set y0 : E := y t with hy0_def
  set y8 : E := y (t + 8 * h) with hy8_def
  set y9 : E := y (t + 9 * h) with hy9_def
  set d0 : E := deriv y t with hd0_def
  set d1 : E := deriv y (t + h) with hd1_def
  set d2 : E := deriv y (t + 2 * h) with hd2_def
  set d3 : E := deriv y (t + 3 * h) with hd3_def
  set d4 : E := deriv y (t + 4 * h) with hd4_def
  set d5 : E := deriv y (t + 5 * h) with hd5_def
  set d6 : E := deriv y (t + 6 * h) with hd6_def
  set d7 : E := deriv y (t + 7 * h) with hd7_def
  set d8 : E := deriv y (t + 8 * h) with hd8_def
  set d9 : E := deriv y (t + 9 * h) with hd9_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  set ddddd : E := iteratedDeriv 5 y t with hddddd_def
  set dddddd : E := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd : E := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd : E := iteratedDeriv 8 y t with hdddddddd_def
  set ddddddddd : E := iteratedDeriv 9 y t with hddddddddd_def
  set dddddddddd : E := iteratedDeriv 10 y t with hdddddddddd_def
  clear_value y0 y8 y9 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
    dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd dddddddddd
  have hLTE_eq :=
    am9Vec_residual_alg_identity y0 y8 y9 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
      dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd dddddddddd h
  rw [hLTE_eq]
  set A : E := y9 - y0 - (9 * h) • d0
            - ((9 * h) ^ 2 / 2) • dd
            - ((9 * h) ^ 3 / 6) • ddd
            - ((9 * h) ^ 4 / 24) • dddd
            - ((9 * h) ^ 5 / 120) • ddddd
            - ((9 * h) ^ 6 / 720) • dddddd
            - ((9 * h) ^ 7 / 5040) • ddddddd
            - ((9 * h) ^ 8 / 40320) • dddddddd
            - ((9 * h) ^ 9 / 362880) • ddddddddd
            - ((9 * h) ^ 10 / 3628800) • dddddddddd with hA_def
  set B : E := y8 - y0 - (8 * h) • d0
            - ((8 * h) ^ 2 / 2) • dd
            - ((8 * h) ^ 3 / 6) • ddd
            - ((8 * h) ^ 4 / 24) • dddd
            - ((8 * h) ^ 5 / 120) • ddddd
            - ((8 * h) ^ 6 / 720) • dddddd
            - ((8 * h) ^ 7 / 5040) • ddddddd
            - ((8 * h) ^ 8 / 40320) • dddddddd
            - ((8 * h) ^ 9 / 362880) • ddddddddd
            - ((8 * h) ^ 10 / 3628800) • dddddddddd with hB_def
  set C : E := d9 - d0 - (9 * h) • dd
            - ((9 * h) ^ 2 / 2) • ddd
            - ((9 * h) ^ 3 / 6) • dddd
            - ((9 * h) ^ 4 / 24) • ddddd
            - ((9 * h) ^ 5 / 120) • dddddd
            - ((9 * h) ^ 6 / 720) • ddddddd
            - ((9 * h) ^ 7 / 5040) • dddddddd
            - ((9 * h) ^ 8 / 40320) • ddddddddd
            - ((9 * h) ^ 9 / 362880) • dddddddddd with hC_def
  set D : E := d8 - d0 - (8 * h) • dd
            - ((8 * h) ^ 2 / 2) • ddd
            - ((8 * h) ^ 3 / 6) • dddd
            - ((8 * h) ^ 4 / 24) • ddddd
            - ((8 * h) ^ 5 / 120) • dddddd
            - ((8 * h) ^ 6 / 720) • ddddddd
            - ((8 * h) ^ 7 / 5040) • dddddddd
            - ((8 * h) ^ 8 / 40320) • ddddddddd
            - ((8 * h) ^ 9 / 362880) • dddddddddd with hD_def
  set F : E := d7 - d0 - (7 * h) • dd
            - ((7 * h) ^ 2 / 2) • ddd
            - ((7 * h) ^ 3 / 6) • dddd
            - ((7 * h) ^ 4 / 24) • ddddd
            - ((7 * h) ^ 5 / 120) • dddddd
            - ((7 * h) ^ 6 / 720) • ddddddd
            - ((7 * h) ^ 7 / 5040) • dddddddd
            - ((7 * h) ^ 8 / 40320) • ddddddddd
            - ((7 * h) ^ 9 / 362880) • dddddddddd with hF_def
  set G : E := d6 - d0 - (6 * h) • dd
            - ((6 * h) ^ 2 / 2) • ddd
            - ((6 * h) ^ 3 / 6) • dddd
            - ((6 * h) ^ 4 / 24) • ddddd
            - ((6 * h) ^ 5 / 120) • dddddd
            - ((6 * h) ^ 6 / 720) • ddddddd
            - ((6 * h) ^ 7 / 5040) • dddddddd
            - ((6 * h) ^ 8 / 40320) • ddddddddd
            - ((6 * h) ^ 9 / 362880) • dddddddddd with hG_def
  set I : E := d5 - d0 - (5 * h) • dd
            - ((5 * h) ^ 2 / 2) • ddd
            - ((5 * h) ^ 3 / 6) • dddd
            - ((5 * h) ^ 4 / 24) • ddddd
            - ((5 * h) ^ 5 / 120) • dddddd
            - ((5 * h) ^ 6 / 720) • ddddddd
            - ((5 * h) ^ 7 / 5040) • dddddddd
            - ((5 * h) ^ 8 / 40320) • ddddddddd
            - ((5 * h) ^ 9 / 362880) • dddddddddd with hI_def
  set J : E := d4 - d0 - (4 * h) • dd
            - ((4 * h) ^ 2 / 2) • ddd
            - ((4 * h) ^ 3 / 6) • dddd
            - ((4 * h) ^ 4 / 24) • ddddd
            - ((4 * h) ^ 5 / 120) • dddddd
            - ((4 * h) ^ 6 / 720) • ddddddd
            - ((4 * h) ^ 7 / 5040) • dddddddd
            - ((4 * h) ^ 8 / 40320) • ddddddddd
            - ((4 * h) ^ 9 / 362880) • dddddddddd with hJ_def
  set K : E := d3 - d0 - (3 * h) • dd
            - ((3 * h) ^ 2 / 2) • ddd
            - ((3 * h) ^ 3 / 6) • dddd
            - ((3 * h) ^ 4 / 24) • ddddd
            - ((3 * h) ^ 5 / 120) • dddddd
            - ((3 * h) ^ 6 / 720) • ddddddd
            - ((3 * h) ^ 7 / 5040) • dddddddd
            - ((3 * h) ^ 8 / 40320) • ddddddddd
            - ((3 * h) ^ 9 / 362880) • dddddddddd with hK_def
  set L : E := d2 - d0 - (2 * h) • dd
            - ((2 * h) ^ 2 / 2) • ddd
            - ((2 * h) ^ 3 / 6) • dddd
            - ((2 * h) ^ 4 / 24) • ddddd
            - ((2 * h) ^ 5 / 120) • dddddd
            - ((2 * h) ^ 6 / 720) • ddddddd
            - ((2 * h) ^ 7 / 5040) • dddddddd
            - ((2 * h) ^ 8 / 40320) • ddddddddd
            - ((2 * h) ^ 9 / 362880) • dddddddddd with hL_def
  set P : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd
            - (h ^ 4 / 24) • ddddd
            - (h ^ 5 / 120) • dddddd
            - (h ^ 6 / 720) • ddddddd
            - (h ^ 7 / 5040) • dddddddd
            - (h ^ 8 / 40320) • ddddddddd
            - (h ^ 9 / 362880) • dddddddddd with hP_def
  clear_value A B C D F G I J K L P
  have htri := am9Vec_residual_eleven_term_triangle A B C D F G I J K L P h hh
  have hA_bd : ‖A‖ ≤ M / 39916800 * (9 * h) ^ 11 := hRy9
  have hB_bd : ‖B‖ ≤ M / 39916800 * (8 * h) ^ 11 := hRy8
  have hC_bd : ‖C‖ ≤ M / 3628800 * (9 * h) ^ 10 := hRyp9
  have hD_bd : ‖D‖ ≤ M / 3628800 * (8 * h) ^ 10 := hRyp8
  have hF_bd : ‖F‖ ≤ M / 3628800 * (7 * h) ^ 10 := hRyp7
  have hG_bd : ‖G‖ ≤ M / 3628800 * (6 * h) ^ 10 := hRyp6
  have hI_bd : ‖I‖ ≤ M / 3628800 * (5 * h) ^ 10 := hRyp5
  have hJ_bd : ‖J‖ ≤ M / 3628800 * (4 * h) ^ 10 := hRyp4
  have hK_bd : ‖K‖ ≤ M / 3628800 * (3 * h) ^ 10 := hRyp3
  have hL_bd : ‖L‖ ≤ M / 3628800 * (2 * h) ^ 10 := hRyp2
  have hP_bd : ‖P‖ ≤ M / 3628800 * h ^ 10 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  exact am9Vec_residual_combine hh hMnn A B C D F G I J K L P htri
    hA_bd hB_bd hC_bd hD_bd hF_bd hG_bd hI_bd hJ_bd hK_bd hL_bd hP_bd

theorem am9Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 11 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 9) * h ≤ T →
        ‖am9VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 11 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_eleven_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(1827 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 9) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 9 * h = ((n : ℝ) + 9) * h := by ring
    linarith
  show ‖am9VecResidual h t y‖ ≤ 1827 * M * h ^ 11
  unfold am9VecResidual
  exact am9Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem hh.le

theorem am9Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 11 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (2082753 / 7257600 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsAM9TrajectoryVec h f t₀ yseq →
      0 ≤ ε₀ →
      ‖yseq 0 - y t₀‖ ≤ ε₀ →
      ‖yseq 1 - y (t₀ + h)‖ ≤ ε₀ →
      ‖yseq 2 - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖yseq 3 - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖yseq 4 - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖yseq 5 - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖yseq 6 - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ‖yseq 7 - y (t₀ + 7 * h)‖ ≤ ε₀ →
      ‖yseq 8 - y (t₀ + 8 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 8) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((23 * L) * T) * ε₀ + K * h ^ 10 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am9Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((23 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd he7_bd he8_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => ‖yseq k - y (t₀ + (k : ℝ) * h)‖ with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (max (max (max (max
        (eN k) (eN (k + 1))) (eN (k + 2))) (eN (k + 3))) (eN (k + 4)))
        (eN (k + 5))) (eN (k + 6))) (eN (k + 7))) (eN (k + 8))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => norm_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
        (le_max_of_le_left (le_max_of_le_left (heN_nn k))))))))
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (max (max (max (max
        (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4)) (eN 5)) (eN 6)) (eN 7)) (eN 8)
        ≤ ε₀
    refine max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
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
    · show ‖yseq 8 - y (t₀ + ((8 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((8 : ℕ) : ℝ) * h = 8 * h := by push_cast; ring
      rw [hcast]; simpa using he8_bd
  have h23L_nn : (0 : ℝ) ≤ 23 * L := by linarith
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 9) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (23 * L)) * EN n + (2 * C) * h ^ 11 := by
    intro n hnh_le
    have honestep := am9Vec_one_step_error_pair_bound
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
    have hcast9 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) =
        (n : ℝ) + 9 := by
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
    have heq_eN_n9 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast9]
    show max (max (max (max (max (max (max (max
            (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * (23 * L))
            * max (max (max (max (max (max (max (max (eN n) (eN (n + 1)))
                  (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
          + (2 * C) * h ^ 11
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5,
      heq_eN_n6, heq_eN_n7, heq_eN_n8, heq_eN_n9]
    have h2τ : 2 * ‖am9VecResidual h (t₀ + (n : ℝ) * h) y‖
        ≤ (2 * C) * h ^ 11 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith [this]
    linarith [honestep, h2τ]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((23 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((23 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh10_nn : 0 ≤ h ^ 10 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((23 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((23 * L) * T) * ε₀
            + T * Real.exp ((23 * L) * T) * (2 * C) * h ^ 10 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((23 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((23 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh10_nn : 0 ≤ T * Real.exp ((23 * L) * T) * (2 * C) * h ^ 10 :=
      mul_nonneg hKnn hh10_nn
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
  | 8, _ =>
    have hbase : ‖yseq 8 - y (t₀ + ((8 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((8 : ℕ) : ℝ) * h = 8 * h := by push_cast; ring
      rw [hcast]; simpa using he8_bd
    exact hbase_to_headline _ hbase
  | N' + 9, hNh =>
    have hcast : (((N' + 9 : ℕ) : ℝ) + 8) = (N' : ℝ) + 17 := by
      push_cast; ring
    have hN_hyp : ((N' : ℝ) + 17) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (23 * L)) * EN n + (2 * C) * h ^ (10 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (10 + 1) = (2 * C) * h ^ 11 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 9 ≤ (N' : ℝ) + 17 := by linarith
      have h_mul : ((n : ℝ) + 9) * h ≤ ((N' : ℝ) + 17) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have hle : (N' : ℝ) + 1 ≤ (N' : ℝ) + 17 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 23 * L) (C := 2 * C) (T := T) (p := 10)
        (e := EN) (N := N' + 1)
        hh.le h23L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 9) ≤ EN (N' + 1) := by
      show eN (N' + 9)
        ≤ max (max (max (max (max (max (max (max
              (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4)))
              (eN (N' + 1 + 5))) (eN (N' + 1 + 6))) (eN (N' + 1 + 7))) (eN (N' + 1 + 8))
      have heq : N' + 9 = N' + 1 + 8 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((23 * L) * T) * EN 0 ≤ Real.exp ((23 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show ‖yseq (N' + 9) - y (t₀ + ((N' + 9 : ℕ) : ℝ) * h)‖
        ≤ Real.exp ((23 * L) * T) * ε₀
          + T * Real.exp ((23 * L) * T) * (2 * C) * h ^ 10
    have heN_eq :
        eN (N' + 9)
          = ‖yseq (N' + 9) - y (t₀ + ((N' + 9 : ℕ) : ℝ) * h)‖ := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
