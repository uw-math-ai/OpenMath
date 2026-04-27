import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB11VectorConvergence

/-! ## Adams--Moulton 10-step Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the AM10 scalar quantitative convergence chain in
`OpenMath/LMMAM10Convergence.lean`.  The implicit AM10 update is parameterised
by a supplied trajectory; existence of such a trajectory is a separate
fixed-point problem and is not part of this chain.

The AM10 coefficients are obtained by integrating the Lagrange basis on
nodes `0,…,10` over `[9, 10]`; over the common denominator `479001600` they
are `[-3250433, 36284876, -184776195, 567450984, -1170597042, 1710774528,
 -1823311566, 1446205080, -890175549, 656185652, 134211265]`, summing to
`479001600`.

The absolute-weight sum of the explicit ten coefficients is `17149519/967680`,
so after division by the implicit new-point factor the growth is slackened to
`37L`.  The exact twelfth-order residual coefficient is approximately
`5044.91`, slackened to `5045`.
-/

namespace LMM

/-- AM10 vector trajectory predicate.  The new value appears inside `f`, so
existence of such a trajectory is a separate fixed-point problem. -/
structure IsAM10TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 10)
      = y (n + 9)
        + h • ((134211265 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 10) * h) (y (n + 10))
             + (656185652 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 9) * h) (y (n + 9))
             - (890175549 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h) (y (n + 8))
             + (1446205080 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h) (y (n + 7))
             - (1823311566 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             + (1710774528 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             - (1170597042 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             + (567450984 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             - (184776195 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             + (36284876 / 479001600 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             - (3250433 / 479001600 : ℝ) • f (t₀ + (n : ℝ) * h) (y n))

/-- Textbook AM10 vector residual: the value of the local truncation error of
the AM10 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def am10VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 10 * h) - y (t + 9 * h)
    - h • ((134211265 / 479001600 : ℝ) • deriv y (t + 10 * h)
          + (656185652 / 479001600 : ℝ) • deriv y (t + 9 * h)
          - (890175549 / 479001600 : ℝ) • deriv y (t + 8 * h)
          + (1446205080 / 479001600 : ℝ) • deriv y (t + 7 * h)
          - (1823311566 / 479001600 : ℝ) • deriv y (t + 6 * h)
          + (1710774528 / 479001600 : ℝ) • deriv y (t + 5 * h)
          - (1170597042 / 479001600 : ℝ) • deriv y (t + 4 * h)
          + (567450984 / 479001600 : ℝ) • deriv y (t + 3 * h)
          - (184776195 / 479001600 : ℝ) • deriv y (t + 2 * h)
          + (36284876 / 479001600 : ℝ) • deriv y (t + h)
          - (3250433 / 479001600 : ℝ) • deriv y t)

theorem am10Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am10VecResidual h t y
      = y (t + 10 * h) - y (t + 9 * h)
          - h • ((134211265 / 479001600 : ℝ) • deriv y (t + 10 * h)
                + (656185652 / 479001600 : ℝ) • deriv y (t + 9 * h)
                - (890175549 / 479001600 : ℝ) • deriv y (t + 8 * h)
                + (1446205080 / 479001600 : ℝ) • deriv y (t + 7 * h)
                - (1823311566 / 479001600 : ℝ) • deriv y (t + 6 * h)
                + (1710774528 / 479001600 : ℝ) • deriv y (t + 5 * h)
                - (1170597042 / 479001600 : ℝ) • deriv y (t + 4 * h)
                + (567450984 / 479001600 : ℝ) • deriv y (t + 3 * h)
                - (184776195 / 479001600 : ℝ) • deriv y (t + 2 * h)
                + (36284876 / 479001600 : ℝ) • deriv y (t + h)
                - (3250433 / 479001600 : ℝ) • deriv y t) := by
  rfl

theorem am10Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (134211265 / 479001600 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM10TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (134211265 / 479001600 : ℝ) * h * L)
        * ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖
      ≤ ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
        + (656185652 / 479001600 : ℝ) * h * L
            * ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
        + (890175549 / 479001600 : ℝ) * h * L
            * ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
        + (1446205080 / 479001600 : ℝ) * h * L
            * ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
        + (1823311566 / 479001600 : ℝ) * h * L
            * ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (1710774528 / 479001600 : ℝ) * h * L
            * ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (1170597042 / 479001600 : ℝ) * h * L
            * ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (567450984 / 479001600 : ℝ) * h * L
            * ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (184776195 / 479001600 : ℝ) * h * L
            * ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (36284876 / 479001600 : ℝ) * h * L
            * ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (3250433 / 479001600 : ℝ) * h * L
            * ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + ‖am10VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
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
  set yn10 : E := yseq (n + 10) with hyn10_def
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
  set tn10 : ℝ := t₀ + ((n : ℝ) + 10) * h with htn10_def
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
  set zn10 : E := y tn10 with hzn10_def
  set τ : E := am10VecResidual h tn y with hτ_def
  have _hsmall_record : (134211265 / 479001600 : ℝ) * h * L ≤ 1 / 2 := hsmall
  have hstep : yn10
      = yn9
        + h • ((134211265 / 479001600 : ℝ) • f tn10 yn10
             + (656185652 / 479001600 : ℝ) • f tn9 yn9
             - (890175549 / 479001600 : ℝ) • f tn8 yn8
             + (1446205080 / 479001600 : ℝ) • f tn7 yn7
             - (1823311566 / 479001600 : ℝ) • f tn6 yn6
             + (1710774528 / 479001600 : ℝ) • f tn5 yn5
             - (1170597042 / 479001600 : ℝ) • f tn4 yn4
             + (567450984 / 479001600 : ℝ) • f tn3 yn3
             - (184776195 / 479001600 : ℝ) • f tn2 yn2
             + (36284876 / 479001600 : ℝ) • f tn1 yn1
             - (3250433 / 479001600 : ℝ) • f tn yn) := by
    simpa [hyn10_def, hyn9_def, hyn8_def, hyn7_def, hyn6_def, hyn5_def, hyn4_def,
      hyn3_def, hyn2_def, hyn1_def, hyn_def, htn10_def, htn9_def, htn8_def, htn7_def,
      htn6_def, htn5_def, htn4_def, htn3_def, htn2_def, htn1_def, htn_def]
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
  have htn_10h : tn + 10 * h = tn10 := by
    simp [htn_def, htn10_def]; ring
  have hτ_eq : τ = zn10 - zn9
      - h • ((134211265 / 479001600 : ℝ) • f tn10 zn10
             + (656185652 / 479001600 : ℝ) • f tn9 zn9
             - (890175549 / 479001600 : ℝ) • f tn8 zn8
             + (1446205080 / 479001600 : ℝ) • f tn7 zn7
             - (1823311566 / 479001600 : ℝ) • f tn6 zn6
             + (1710774528 / 479001600 : ℝ) • f tn5 zn5
             - (1170597042 / 479001600 : ℝ) • f tn4 zn4
             + (567450984 / 479001600 : ℝ) • f tn3 zn3
             - (184776195 / 479001600 : ℝ) • f tn2 zn2
             + (36284876 / 479001600 : ℝ) • f tn1 zn1
             - (3250433 / 479001600 : ℝ) • f tn zn) := by
    show am10VecResidual h tn y = _
    unfold am10VecResidual
    rw [htn1_h, htn_2h, htn_3h, htn_4h, htn_5h, htn_6h, htn_7h, htn_8h, htn_9h,
      htn_10h, hyf tn10, hyf tn9, hyf tn8, hyf tn7, hyf tn6, hyf tn5, hyf tn4,
      hyf tn3, hyf tn2, hyf tn1, hyf tn]
  have halg : yn10 - zn10
      = (yn9 - zn9)
        + h • ((134211265 / 479001600 : ℝ) • (f tn10 yn10 - f tn10 zn10))
        + h • ((656185652 / 479001600 : ℝ) • (f tn9 yn9 - f tn9 zn9))
        - h • ((890175549 / 479001600 : ℝ) • (f tn8 yn8 - f tn8 zn8))
        + h • ((1446205080 / 479001600 : ℝ) • (f tn7 yn7 - f tn7 zn7))
        - h • ((1823311566 / 479001600 : ℝ) • (f tn6 yn6 - f tn6 zn6))
        + h • ((1710774528 / 479001600 : ℝ) • (f tn5 yn5 - f tn5 zn5))
        - h • ((1170597042 / 479001600 : ℝ) • (f tn4 yn4 - f tn4 zn4))
        + h • ((567450984 / 479001600 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        - h • ((184776195 / 479001600 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        + h • ((36284876 / 479001600 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        - h • ((3250433 / 479001600 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_add]
    abel
  have hLip10 : ‖f tn10 yn10 - f tn10 zn10‖ ≤ L * ‖yn10 - zn10‖ := hf tn10 yn10 zn10
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
  have hc10_nn : (0 : ℝ) ≤ 134211265 / 479001600 := by norm_num
  have hc9_nn : (0 : ℝ) ≤ 656185652 / 479001600 := by norm_num
  have hc8_nn : (0 : ℝ) ≤ 890175549 / 479001600 := by norm_num
  have hc7_nn : (0 : ℝ) ≤ 1446205080 / 479001600 := by norm_num
  have hc6_nn : (0 : ℝ) ≤ 1823311566 / 479001600 := by norm_num
  have hc5_nn : (0 : ℝ) ≤ 1710774528 / 479001600 := by norm_num
  have hc4_nn : (0 : ℝ) ≤ 1170597042 / 479001600 := by norm_num
  have hc3_nn : (0 : ℝ) ≤ 567450984 / 479001600 := by norm_num
  have hc2_nn : (0 : ℝ) ≤ 184776195 / 479001600 := by norm_num
  have hc1_nn : (0 : ℝ) ≤ 36284876 / 479001600 := by norm_num
  have hc0_nn : (0 : ℝ) ≤ 3250433 / 479001600 := by norm_num
  set A : E := yn9 - zn9 with hA_def
  set B10 : E := h • ((134211265 / 479001600 : ℝ) • (f tn10 yn10 - f tn10 zn10))
    with hB10_def
  set B9 : E := h • ((656185652 / 479001600 : ℝ) • (f tn9 yn9 - f tn9 zn9))
    with hB9_def
  set B8 : E := h • ((890175549 / 479001600 : ℝ) • (f tn8 yn8 - f tn8 zn8))
    with hB8_def
  set B7 : E := h • ((1446205080 / 479001600 : ℝ) • (f tn7 yn7 - f tn7 zn7))
    with hB7_def
  set B6 : E := h • ((1823311566 / 479001600 : ℝ) • (f tn6 yn6 - f tn6 zn6))
    with hB6_def
  set B5 : E := h • ((1710774528 / 479001600 : ℝ) • (f tn5 yn5 - f tn5 zn5))
    with hB5_def
  set B4 : E := h • ((1170597042 / 479001600 : ℝ) • (f tn4 yn4 - f tn4 zn4))
    with hB4_def
  set B3 : E := h • ((567450984 / 479001600 : ℝ) • (f tn3 yn3 - f tn3 zn3))
    with hB3_def
  set B2 : E := h • ((184776195 / 479001600 : ℝ) • (f tn2 yn2 - f tn2 zn2))
    with hB2_def
  set B1 : E := h • ((36284876 / 479001600 : ℝ) • (f tn1 yn1 - f tn1 zn1))
    with hB1_def
  set B0 : E := h • ((3250433 / 479001600 : ℝ) • (f tn yn - f tn zn))
    with hB0_def
  have halg' :
      yn10 - zn10 = A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2 + B1 - B0 - τ := by
    simpa [hA_def, hB10_def, hB9_def, hB8_def, hB7_def, hB6_def, hB5_def,
      hB4_def, hB3_def, hB2_def, hB1_def, hB0_def] using halg
  have h10_norm :
      ‖B10‖ ≤ (134211265 / 479001600 : ℝ) * h * L * ‖yn10 - zn10‖ := by
    rw [hB10_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc10_nn]
    have : h * ((134211265 / 479001600 : ℝ) * ‖f tn10 yn10 - f tn10 zn10‖)
        ≤ h * ((134211265 / 479001600 : ℝ) * (L * ‖yn10 - zn10‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip10 hc10_nn
    calc h * ((134211265 / 479001600 : ℝ) * ‖f tn10 yn10 - f tn10 zn10‖)
        ≤ h * ((134211265 / 479001600 : ℝ) * (L * ‖yn10 - zn10‖)) := this
      _ = (134211265 / 479001600 : ℝ) * h * L * ‖yn10 - zn10‖ := by ring
  have h9_norm :
      ‖B9‖ ≤ (656185652 / 479001600 : ℝ) * h * L * ‖yn9 - zn9‖ := by
    rw [hB9_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc9_nn]
    have : h * ((656185652 / 479001600 : ℝ) * ‖f tn9 yn9 - f tn9 zn9‖)
        ≤ h * ((656185652 / 479001600 : ℝ) * (L * ‖yn9 - zn9‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip9 hc9_nn
    calc h * ((656185652 / 479001600 : ℝ) * ‖f tn9 yn9 - f tn9 zn9‖)
        ≤ h * ((656185652 / 479001600 : ℝ) * (L * ‖yn9 - zn9‖)) := this
      _ = (656185652 / 479001600 : ℝ) * h * L * ‖yn9 - zn9‖ := by ring
  have h8_norm :
      ‖B8‖ ≤ (890175549 / 479001600 : ℝ) * h * L * ‖yn8 - zn8‖ := by
    rw [hB8_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc8_nn]
    have : h * ((890175549 / 479001600 : ℝ) * ‖f tn8 yn8 - f tn8 zn8‖)
        ≤ h * ((890175549 / 479001600 : ℝ) * (L * ‖yn8 - zn8‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip8 hc8_nn
    calc h * ((890175549 / 479001600 : ℝ) * ‖f tn8 yn8 - f tn8 zn8‖)
        ≤ h * ((890175549 / 479001600 : ℝ) * (L * ‖yn8 - zn8‖)) := this
      _ = (890175549 / 479001600 : ℝ) * h * L * ‖yn8 - zn8‖ := by ring
  have h7_norm :
      ‖B7‖ ≤ (1446205080 / 479001600 : ℝ) * h * L * ‖yn7 - zn7‖ := by
    rw [hB7_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc7_nn]
    have : h * ((1446205080 / 479001600 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((1446205080 / 479001600 : ℝ) * (L * ‖yn7 - zn7‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip7 hc7_nn
    calc h * ((1446205080 / 479001600 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((1446205080 / 479001600 : ℝ) * (L * ‖yn7 - zn7‖)) := this
      _ = (1446205080 / 479001600 : ℝ) * h * L * ‖yn7 - zn7‖ := by ring
  have h6_norm :
      ‖B6‖ ≤ (1823311566 / 479001600 : ℝ) * h * L * ‖yn6 - zn6‖ := by
    rw [hB6_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc6_nn]
    have : h * ((1823311566 / 479001600 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((1823311566 / 479001600 : ℝ) * (L * ‖yn6 - zn6‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip6 hc6_nn
    calc h * ((1823311566 / 479001600 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((1823311566 / 479001600 : ℝ) * (L * ‖yn6 - zn6‖)) := this
      _ = (1823311566 / 479001600 : ℝ) * h * L * ‖yn6 - zn6‖ := by ring
  have h5_norm :
      ‖B5‖ ≤ (1710774528 / 479001600 : ℝ) * h * L * ‖yn5 - zn5‖ := by
    rw [hB5_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc5_nn]
    have : h * ((1710774528 / 479001600 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((1710774528 / 479001600 : ℝ) * (L * ‖yn5 - zn5‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip5 hc5_nn
    calc h * ((1710774528 / 479001600 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((1710774528 / 479001600 : ℝ) * (L * ‖yn5 - zn5‖)) := this
      _ = (1710774528 / 479001600 : ℝ) * h * L * ‖yn5 - zn5‖ := by ring
  have h4_norm :
      ‖B4‖ ≤ (1170597042 / 479001600 : ℝ) * h * L * ‖yn4 - zn4‖ := by
    rw [hB4_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc4_nn]
    have : h * ((1170597042 / 479001600 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((1170597042 / 479001600 : ℝ) * (L * ‖yn4 - zn4‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip4 hc4_nn
    calc h * ((1170597042 / 479001600 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((1170597042 / 479001600 : ℝ) * (L * ‖yn4 - zn4‖)) := this
      _ = (1170597042 / 479001600 : ℝ) * h * L * ‖yn4 - zn4‖ := by ring
  have h3_norm :
      ‖B3‖ ≤ (567450984 / 479001600 : ℝ) * h * L * ‖yn3 - zn3‖ := by
    rw [hB3_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc3_nn]
    have : h * ((567450984 / 479001600 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((567450984 / 479001600 : ℝ) * (L * ‖yn3 - zn3‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip3 hc3_nn
    calc h * ((567450984 / 479001600 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((567450984 / 479001600 : ℝ) * (L * ‖yn3 - zn3‖)) := this
      _ = (567450984 / 479001600 : ℝ) * h * L * ‖yn3 - zn3‖ := by ring
  have h2_norm :
      ‖B2‖ ≤ (184776195 / 479001600 : ℝ) * h * L * ‖yn2 - zn2‖ := by
    rw [hB2_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc2_nn]
    have : h * ((184776195 / 479001600 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((184776195 / 479001600 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 hc2_nn
    calc h * ((184776195 / 479001600 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((184776195 / 479001600 : ℝ) * (L * ‖yn2 - zn2‖)) := this
      _ = (184776195 / 479001600 : ℝ) * h * L * ‖yn2 - zn2‖ := by ring
  have h1_norm :
      ‖B1‖ ≤ (36284876 / 479001600 : ℝ) * h * L * ‖yn1 - zn1‖ := by
    rw [hB1_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc1_nn]
    have : h * ((36284876 / 479001600 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((36284876 / 479001600 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 hc1_nn
    calc h * ((36284876 / 479001600 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((36284876 / 479001600 : ℝ) * (L * ‖yn1 - zn1‖)) := this
      _ = (36284876 / 479001600 : ℝ) * h * L * ‖yn1 - zn1‖ := by ring
  have h0_norm :
      ‖B0‖ ≤ (3250433 / 479001600 : ℝ) * h * L * ‖yn - zn‖ := by
    rw [hB0_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc0_nn]
    have : h * ((3250433 / 479001600 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((3250433 / 479001600 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 hc0_nn
    calc h * ((3250433 / 479001600 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((3250433 / 479001600 : ℝ) * (L * ‖yn - zn‖)) := this
      _ = (3250433 / 479001600 : ℝ) * h * L * ‖yn - zn‖ := by ring
  have htri :
      ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2 + B1 - B0 - τ‖
        ≤ ‖A‖ + ‖B10‖ + ‖B9‖ + ‖B8‖ + ‖B7‖ + ‖B6‖ + ‖B5‖ + ‖B4‖
            + ‖B3‖ + ‖B2‖ + ‖B1‖ + ‖B0‖ + ‖τ‖ := by
    have h1 : ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2 + B1 - B0 - τ‖
        ≤ ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2 + B1 - B0‖ + ‖τ‖ :=
      norm_sub_le _ _
    have h2 : ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2 + B1 - B0‖
        ≤ ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2 + B1‖ + ‖B0‖ :=
      norm_sub_le _ _
    have h3 : ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2 + B1‖
        ≤ ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2‖ + ‖B1‖ :=
      norm_add_le _ _
    have h4 : ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2‖
        ≤ ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3‖ + ‖B2‖ :=
      norm_sub_le _ _
    have h5 : ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3‖
        ≤ ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4‖ + ‖B3‖ :=
      norm_add_le _ _
    have h6 : ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4‖
        ≤ ‖A + B10 + B9 - B8 + B7 - B6 + B5‖ + ‖B4‖ :=
      norm_sub_le _ _
    have h7 : ‖A + B10 + B9 - B8 + B7 - B6 + B5‖
        ≤ ‖A + B10 + B9 - B8 + B7 - B6‖ + ‖B5‖ :=
      norm_add_le _ _
    have h8 : ‖A + B10 + B9 - B8 + B7 - B6‖
        ≤ ‖A + B10 + B9 - B8 + B7‖ + ‖B6‖ :=
      norm_sub_le _ _
    have h9 : ‖A + B10 + B9 - B8 + B7‖
        ≤ ‖A + B10 + B9 - B8‖ + ‖B7‖ :=
      norm_add_le _ _
    have h10 : ‖A + B10 + B9 - B8‖
        ≤ ‖A + B10 + B9‖ + ‖B8‖ :=
      norm_sub_le _ _
    have h11 : ‖A + B10 + B9‖
        ≤ ‖A + B10‖ + ‖B9‖ := norm_add_le _ _
    have h12 : ‖A + B10‖ ≤ ‖A‖ + ‖B10‖ := norm_add_le _ _
    linarith
  have hmain :
      ‖yn10 - zn10‖
        ≤ ‖yn9 - zn9‖
          + (134211265 / 479001600 : ℝ) * h * L * ‖yn10 - zn10‖
          + (656185652 / 479001600 : ℝ) * h * L * ‖yn9 - zn9‖
          + (890175549 / 479001600 : ℝ) * h * L * ‖yn8 - zn8‖
          + (1446205080 / 479001600 : ℝ) * h * L * ‖yn7 - zn7‖
          + (1823311566 / 479001600 : ℝ) * h * L * ‖yn6 - zn6‖
          + (1710774528 / 479001600 : ℝ) * h * L * ‖yn5 - zn5‖
          + (1170597042 / 479001600 : ℝ) * h * L * ‖yn4 - zn4‖
          + (567450984 / 479001600 : ℝ) * h * L * ‖yn3 - zn3‖
          + (184776195 / 479001600 : ℝ) * h * L * ‖yn2 - zn2‖
          + (36284876 / 479001600 : ℝ) * h * L * ‖yn1 - zn1‖
          + (3250433 / 479001600 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    calc ‖yn10 - zn10‖
        = ‖A + B10 + B9 - B8 + B7 - B6 + B5 - B4 + B3 - B2 + B1 - B0 - τ‖ := by
            rw [halg']
      _ ≤ ‖A‖ + ‖B10‖ + ‖B9‖ + ‖B8‖ + ‖B7‖ + ‖B6‖ + ‖B5‖ + ‖B4‖
          + ‖B3‖ + ‖B2‖ + ‖B1‖ + ‖B0‖ + ‖τ‖ := htri
      _ ≤ ‖yn9 - zn9‖
          + (134211265 / 479001600 : ℝ) * h * L * ‖yn10 - zn10‖
          + (656185652 / 479001600 : ℝ) * h * L * ‖yn9 - zn9‖
          + (890175549 / 479001600 : ℝ) * h * L * ‖yn8 - zn8‖
          + (1446205080 / 479001600 : ℝ) * h * L * ‖yn7 - zn7‖
          + (1823311566 / 479001600 : ℝ) * h * L * ‖yn6 - zn6‖
          + (1710774528 / 479001600 : ℝ) * h * L * ‖yn5 - zn5‖
          + (1170597042 / 479001600 : ℝ) * h * L * ‖yn4 - zn4‖
          + (567450984 / 479001600 : ℝ) * h * L * ‖yn3 - zn3‖
          + (184776195 / 479001600 : ℝ) * h * L * ‖yn2 - zn2‖
          + (36284876 / 479001600 : ℝ) * h * L * ‖yn1 - zn1‖
          + (3250433 / 479001600 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
        rw [hA_def]
        linarith [h10_norm, h9_norm, h8_norm, h7_norm, h6_norm, h5_norm,
          h4_norm, h3_norm, h2_norm, h1_norm, h0_norm]
  linarith [hmain]

theorem am10Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (134211265 / 479001600 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM10TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖
      ≤ (1 + h * (37 * L))
            * max (max (max (max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
                ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
                ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖)
                ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
        + 2 * ‖am10VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
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
  set en10 : ℝ :=
    ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖ with hen10_def
  set τabs : ℝ :=
    ‖am10VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max (max (max (max en en1) en2) en3) en4) en5)
      en6) en7) en8) en9
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
  have hen10_nn : 0 ≤ en10 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _)
                  (le_trans (le_max_left _ _) (le_max_left _ _)))))))))
  have hen_le_E : en ≤ Emax :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
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
                (le_trans (le_max_left _ _)
                  (le_trans (le_max_left _ _) (le_max_left _ _))))))))
  have hen2_le_E : en2 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _) (le_max_left _ _)))))))
  have hen3_le_E : en3 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen4_le_E : en4 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen5_le_E : en5 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen6_le_E : en6 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen7_le_E : en7 ≤ Emax :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen8_le_E : en8 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen9_le_E : en9 ≤ Emax := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 239500800 / 134211265 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (134211265 / 479001600 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (134211265 / 479001600 : ℝ) * h * L) * en10
        ≤ en9
          + (656185652 / 479001600 : ℝ) * h * L * en9
          + (890175549 / 479001600 : ℝ) * h * L * en8
          + (1446205080 / 479001600 : ℝ) * h * L * en7
          + (1823311566 / 479001600 : ℝ) * h * L * en6
          + (1710774528 / 479001600 : ℝ) * h * L * en5
          + (1170597042 / 479001600 : ℝ) * h * L * en4
          + (567450984 / 479001600 : ℝ) * h * L * en3
          + (184776195 / 479001600 : ℝ) * h * L * en2
          + (36284876 / 479001600 : ℝ) * h * L * en1
          + (3250433 / 479001600 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hen9_def, hen10_def, hτabs_def]
      using
      (am10Vec_one_step_lipschitz (E := E) (h := h) (L := L)
        hh hsmall hf t₀ hy y hyf n)
  have h656185652_nn : 0 ≤ (656185652 / 479001600 : ℝ) * h * L := by positivity
  have h890175549_nn : 0 ≤ (890175549 / 479001600 : ℝ) * h * L := by positivity
  have h1446205080_nn : 0 ≤ (1446205080 / 479001600 : ℝ) * h * L := by positivity
  have h1823311566_nn : 0 ≤ (1823311566 / 479001600 : ℝ) * h * L := by positivity
  have h1710774528_nn : 0 ≤ (1710774528 / 479001600 : ℝ) * h * L := by positivity
  have h1170597042_nn : 0 ≤ (1170597042 / 479001600 : ℝ) * h * L := by positivity
  have h567450984_nn : 0 ≤ (567450984 / 479001600 : ℝ) * h * L := by positivity
  have h184776195_nn : 0 ≤ (184776195 / 479001600 : ℝ) * h * L := by positivity
  have h36284876_nn : 0 ≤ (36284876 / 479001600 : ℝ) * h * L := by positivity
  have h3250433_nn : 0 ≤ (3250433 / 479001600 : ℝ) * h * L := by positivity
  have h656_le :
      (656185652 / 479001600 : ℝ) * h * L * en9
        ≤ (656185652 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen9_le_E h656185652_nn
  have h890_le :
      (890175549 / 479001600 : ℝ) * h * L * en8
        ≤ (890175549 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen8_le_E h890175549_nn
  have h1446_le :
      (1446205080 / 479001600 : ℝ) * h * L * en7
        ≤ (1446205080 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen7_le_E h1446205080_nn
  have h1823_le :
      (1823311566 / 479001600 : ℝ) * h * L * en6
        ≤ (1823311566 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen6_le_E h1823311566_nn
  have h1710_le :
      (1710774528 / 479001600 : ℝ) * h * L * en5
        ≤ (1710774528 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen5_le_E h1710774528_nn
  have h1170_le :
      (1170597042 / 479001600 : ℝ) * h * L * en4
        ≤ (1170597042 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen4_le_E h1170597042_nn
  have h567_le :
      (567450984 / 479001600 : ℝ) * h * L * en3
        ≤ (567450984 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen3_le_E h567450984_nn
  have h184_le :
      (184776195 / 479001600 : ℝ) * h * L * en2
        ≤ (184776195 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen2_le_E h184776195_nn
  have h36_le :
      (36284876 / 479001600 : ℝ) * h * L * en1
        ≤ (36284876 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen1_le_E h36284876_nn
  have h3_le :
      (3250433 / 479001600 : ℝ) * h * L * en
        ≤ (3250433 / 479001600 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen_le_E h3250433_nn
  have hR_le :
      en9
          + (656185652 / 479001600 : ℝ) * h * L * en9
          + (890175549 / 479001600 : ℝ) * h * L * en8
          + (1446205080 / 479001600 : ℝ) * h * L * en7
          + (1823311566 / 479001600 : ℝ) * h * L * en6
          + (1710774528 / 479001600 : ℝ) * h * L * en5
          + (1170597042 / 479001600 : ℝ) * h * L * en4
          + (567450984 / 479001600 : ℝ) * h * L * en3
          + (184776195 / 479001600 : ℝ) * h * L * en2
          + (36284876 / 479001600 : ℝ) * h * L * en1
          + (3250433 / 479001600 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (8489011905 / 479001600 : ℝ) * (h * L)) * Emax + τabs := by
    have h_alg :
        Emax + (656185652 / 479001600 : ℝ) * h * L * Emax
            + (890175549 / 479001600 : ℝ) * h * L * Emax
            + (1446205080 / 479001600 : ℝ) * h * L * Emax
            + (1823311566 / 479001600 : ℝ) * h * L * Emax
            + (1710774528 / 479001600 : ℝ) * h * L * Emax
            + (1170597042 / 479001600 : ℝ) * h * L * Emax
            + (567450984 / 479001600 : ℝ) * h * L * Emax
            + (184776195 / 479001600 : ℝ) * h * L * Emax
            + (36284876 / 479001600 : ℝ) * h * L * Emax
            + (3250433 / 479001600 : ℝ) * h * L * Emax + τabs
          = (1 + (8489011905 / 479001600 : ℝ) * (h * L)) * Emax + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (8489011905 / 479001600 : ℝ) * (h * L)
        ≤ (1 - (134211265 / 479001600 : ℝ) * h * L) * (1 + h * (37 * L)) := by
    have hxL_eq :
        (1 - (134211265 / 479001600 : ℝ) * h * L) * (1 + h * (37 * L))
          - (1 + (8489011905 / 479001600 : ℝ) * (h * L))
          = (h * L) / 479001600 * (9099836030 - 4965816805 * (h * L)) := by ring
    have hpos : 0 ≤ 9099836030 - 4965816805 * (h * L) := by
      have hbound : 4965816805 * (h * L) ≤ 4965816805 * (239500800 / 134211265) := by
        have hnn : (0 : ℝ) ≤ 4965816805 := by norm_num
        exact mul_le_mul_of_nonneg_left hx_small hnn
      have hnum : (4965816805 : ℝ) * (239500800 / 134211265) ≤ 9099836030 := by
        norm_num
      linarith
    have hprod : 0 ≤ (h * L) / 479001600 * (9099836030 - 4965816805 * (h * L)) := by
      apply mul_nonneg
      · positivity
      · exact hpos
    linarith
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (134211265 / 479001600 : ℝ) * h * L) * 2 := by
    linarith [hsmall]
  have hE_part :
      (1 + (8489011905 / 479001600 : ℝ) * (h * L)) * Emax
        ≤ ((1 - (134211265 / 479001600 : ℝ) * h * L) * (1 + h * (37 * L))) * Emax :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (134211265 / 479001600 : ℝ) * h * L) * 2) * τabs :=
    le_mul_of_one_le_left hτ_nn hcoeffτ_le
  have hfactor :
      (1 + (8489011905 / 479001600 : ℝ) * (h * L)) * Emax + τabs
        ≤ (1 - (134211265 / 479001600 : ℝ) * h * L)
            * ((1 + h * (37 * L)) * Emax + 2 * τabs) := by
    have hsplit :
        (1 - (134211265 / 479001600 : ℝ) * h * L)
            * ((1 + h * (37 * L)) * Emax + 2 * τabs)
          = ((1 - (134211265 / 479001600 : ℝ) * h * L) * (1 + h * (37 * L))) * Emax
              + ((1 - (134211265 / 479001600 : ℝ) * h * L) * 2) * τabs := by
      ring
    calc (1 + (8489011905 / 479001600 : ℝ) * (h * L)) * Emax + τabs
        ≤ ((1 - (134211265 / 479001600 : ℝ) * h * L) * (1 + h * (37 * L)))
              * Emax
            + ((1 - (134211265 / 479001600 : ℝ) * h * L) * 2) * τabs :=
            add_le_add hE_part hτ_part
      _ = (1 - (134211265 / 479001600 : ℝ) * h * L)
            * ((1 + h * (37 * L)) * Emax + 2 * τabs) := hsplit.symm
  have hprod :
      (1 - (134211265 / 479001600 : ℝ) * h * L) * en10
        ≤ (1 - (134211265 / 479001600 : ℝ) * h * L)
            * ((1 + h * (37 * L)) * Emax + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  exact le_of_mul_le_mul_left hprod hA_pos

theorem am10Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (134211265 / 479001600 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM10TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max (max (max
          ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
          ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
          ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
          ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖)
          ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖)
          ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖
      ≤ (1 + h * (37 * L))
            * max (max (max (max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
                ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
                ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖)
                ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
        + 2 * ‖am10VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
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
  set en10 : ℝ :=
    ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖ with hen10_def
  set τabs : ℝ :=
    ‖am10VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max (max (max (max en en1) en2) en3) en4) en5)
      en6) en7) en8) en9
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
  have hen10_nn : 0 ≤ en10 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _)
                  (le_trans (le_max_left _ _) (le_max_left _ _)))))))))
  have hen1_le_E : en1 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _)
                  (le_trans (le_max_left _ _) (le_max_left _ _))))))))
  have hen2_le_E : en2 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _) (le_max_left _ _)))))))
  have hen3_le_E : en3 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen4_le_E : en4 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen5_le_E : en5 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen6_le_E : en6 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen7_le_E : en7 ≤ Emax :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen8_le_E : en8 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen9_le_E : en9 ≤ Emax := le_max_right _ _
  have h37hL_nn : 0 ≤ h * (37 * L) := by positivity
  have hen10_bd :
      en10 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hen9_def, hen10_def, hτabs_def, hE_def]
      using
      (am10Vec_one_step_error_bound (E := E) (h := h) (L := L)
        hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : Emax ≤ (1 + h * (37 * L)) * Emax := by
    have hone : (1 : ℝ) * Emax ≤ (1 + h * (37 * L)) * Emax :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  have hen4_bd : en4 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    linarith [hen4_le_E, hE_le_grow]
  have hen5_bd : en5 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    linarith [hen5_le_E, hE_le_grow]
  have hen6_bd : en6 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    linarith [hen6_le_E, hE_le_grow]
  have hen7_bd : en7 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    linarith [hen7_le_E, hE_le_grow]
  have hen8_bd : en8 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    linarith [hen8_le_E, hE_le_grow]
  have hen9_bd : en9 ≤ (1 + h * (37 * L)) * Emax + 2 * τabs := by
    linarith [hen9_le_E, hE_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le
    hen1_bd hen2_bd) hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd)
    hen9_bd) hen10_bd

/-- Param-style residual algebra identity for AM10 vector. Takes the twelve
Taylor-remainder structures `A B C D E F G H I J K L` as abstract parameters
with defining equalities, keeping the lemma statement small enough to
elaborate within the `maxHeartbeats` budget. -/
private lemma am10Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
        d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t : E) (h : ℝ)
    (A B C D F G I J K L P Q : E)
    (hA : A = y10 - y0 - (10 * h) • d0
              - ((10 * h) ^ 2 / 2) • d2t
              - ((10 * h) ^ 3 / 6) • d3t
              - ((10 * h) ^ 4 / 24) • d4t
              - ((10 * h) ^ 5 / 120) • d5t
              - ((10 * h) ^ 6 / 720) • d6t
              - ((10 * h) ^ 7 / 5040) • d7t
              - ((10 * h) ^ 8 / 40320) • d8t
              - ((10 * h) ^ 9 / 362880) • d9t
              - ((10 * h) ^ 10 / 3628800) • d10t
              - ((10 * h) ^ 11 / 39916800) • d11t)
    (hB : B = y9 - y0 - (9 * h) • d0
              - ((9 * h) ^ 2 / 2) • d2t
              - ((9 * h) ^ 3 / 6) • d3t
              - ((9 * h) ^ 4 / 24) • d4t
              - ((9 * h) ^ 5 / 120) • d5t
              - ((9 * h) ^ 6 / 720) • d6t
              - ((9 * h) ^ 7 / 5040) • d7t
              - ((9 * h) ^ 8 / 40320) • d8t
              - ((9 * h) ^ 9 / 362880) • d9t
              - ((9 * h) ^ 10 / 3628800) • d10t
              - ((9 * h) ^ 11 / 39916800) • d11t)
    (hC : C = d10 - d0 - (10 * h) • d2t
              - ((10 * h) ^ 2 / 2) • d3t
              - ((10 * h) ^ 3 / 6) • d4t
              - ((10 * h) ^ 4 / 24) • d5t
              - ((10 * h) ^ 5 / 120) • d6t
              - ((10 * h) ^ 6 / 720) • d7t
              - ((10 * h) ^ 7 / 5040) • d8t
              - ((10 * h) ^ 8 / 40320) • d9t
              - ((10 * h) ^ 9 / 362880) • d10t
              - ((10 * h) ^ 10 / 3628800) • d11t)
    (hD : D = d9 - d0 - (9 * h) • d2t
              - ((9 * h) ^ 2 / 2) • d3t
              - ((9 * h) ^ 3 / 6) • d4t
              - ((9 * h) ^ 4 / 24) • d5t
              - ((9 * h) ^ 5 / 120) • d6t
              - ((9 * h) ^ 6 / 720) • d7t
              - ((9 * h) ^ 7 / 5040) • d8t
              - ((9 * h) ^ 8 / 40320) • d9t
              - ((9 * h) ^ 9 / 362880) • d10t
              - ((9 * h) ^ 10 / 3628800) • d11t)
    (hF : F = d8 - d0 - (8 * h) • d2t
              - ((8 * h) ^ 2 / 2) • d3t
              - ((8 * h) ^ 3 / 6) • d4t
              - ((8 * h) ^ 4 / 24) • d5t
              - ((8 * h) ^ 5 / 120) • d6t
              - ((8 * h) ^ 6 / 720) • d7t
              - ((8 * h) ^ 7 / 5040) • d8t
              - ((8 * h) ^ 8 / 40320) • d9t
              - ((8 * h) ^ 9 / 362880) • d10t
              - ((8 * h) ^ 10 / 3628800) • d11t)
    (hG : G = d7 - d0 - (7 * h) • d2t
              - ((7 * h) ^ 2 / 2) • d3t
              - ((7 * h) ^ 3 / 6) • d4t
              - ((7 * h) ^ 4 / 24) • d5t
              - ((7 * h) ^ 5 / 120) • d6t
              - ((7 * h) ^ 6 / 720) • d7t
              - ((7 * h) ^ 7 / 5040) • d8t
              - ((7 * h) ^ 8 / 40320) • d9t
              - ((7 * h) ^ 9 / 362880) • d10t
              - ((7 * h) ^ 10 / 3628800) • d11t)
    (hI : I = d6 - d0 - (6 * h) • d2t
              - ((6 * h) ^ 2 / 2) • d3t
              - ((6 * h) ^ 3 / 6) • d4t
              - ((6 * h) ^ 4 / 24) • d5t
              - ((6 * h) ^ 5 / 120) • d6t
              - ((6 * h) ^ 6 / 720) • d7t
              - ((6 * h) ^ 7 / 5040) • d8t
              - ((6 * h) ^ 8 / 40320) • d9t
              - ((6 * h) ^ 9 / 362880) • d10t
              - ((6 * h) ^ 10 / 3628800) • d11t)
    (hJ : J = d5 - d0 - (5 * h) • d2t
              - ((5 * h) ^ 2 / 2) • d3t
              - ((5 * h) ^ 3 / 6) • d4t
              - ((5 * h) ^ 4 / 24) • d5t
              - ((5 * h) ^ 5 / 120) • d6t
              - ((5 * h) ^ 6 / 720) • d7t
              - ((5 * h) ^ 7 / 5040) • d8t
              - ((5 * h) ^ 8 / 40320) • d9t
              - ((5 * h) ^ 9 / 362880) • d10t
              - ((5 * h) ^ 10 / 3628800) • d11t)
    (hK : K = d4 - d0 - (4 * h) • d2t
              - ((4 * h) ^ 2 / 2) • d3t
              - ((4 * h) ^ 3 / 6) • d4t
              - ((4 * h) ^ 4 / 24) • d5t
              - ((4 * h) ^ 5 / 120) • d6t
              - ((4 * h) ^ 6 / 720) • d7t
              - ((4 * h) ^ 7 / 5040) • d8t
              - ((4 * h) ^ 8 / 40320) • d9t
              - ((4 * h) ^ 9 / 362880) • d10t
              - ((4 * h) ^ 10 / 3628800) • d11t)
    (hL : L = d3 - d0 - (3 * h) • d2t
              - ((3 * h) ^ 2 / 2) • d3t
              - ((3 * h) ^ 3 / 6) • d4t
              - ((3 * h) ^ 4 / 24) • d5t
              - ((3 * h) ^ 5 / 120) • d6t
              - ((3 * h) ^ 6 / 720) • d7t
              - ((3 * h) ^ 7 / 5040) • d8t
              - ((3 * h) ^ 8 / 40320) • d9t
              - ((3 * h) ^ 9 / 362880) • d10t
              - ((3 * h) ^ 10 / 3628800) • d11t)
    (hP : P = d2 - d0 - (2 * h) • d2t
              - ((2 * h) ^ 2 / 2) • d3t
              - ((2 * h) ^ 3 / 6) • d4t
              - ((2 * h) ^ 4 / 24) • d5t
              - ((2 * h) ^ 5 / 120) • d6t
              - ((2 * h) ^ 6 / 720) • d7t
              - ((2 * h) ^ 7 / 5040) • d8t
              - ((2 * h) ^ 8 / 40320) • d9t
              - ((2 * h) ^ 9 / 362880) • d10t
              - ((2 * h) ^ 10 / 3628800) • d11t)
    (hQ : Q = d1 - d0 - h • d2t
              - (h ^ 2 / 2) • d3t
              - (h ^ 3 / 6) • d4t
              - (h ^ 4 / 24) • d5t
              - (h ^ 5 / 120) • d6t
              - (h ^ 6 / 720) • d7t
              - (h ^ 7 / 5040) • d8t
              - (h ^ 8 / 40320) • d9t
              - (h ^ 9 / 362880) • d10t
              - (h ^ 10 / 3628800) • d11t) :
    y10 - y9 - h • ((134211265 / 479001600 : ℝ) • d10
                  + (656185652 / 479001600 : ℝ) • d9
                  - (890175549 / 479001600 : ℝ) • d8
                  + (1446205080 / 479001600 : ℝ) • d7
                  - (1823311566 / 479001600 : ℝ) • d6
                  + (1710774528 / 479001600 : ℝ) • d5
                  - (1170597042 / 479001600 : ℝ) • d4
                  + (567450984 / 479001600 : ℝ) • d3
                  - (184776195 / 479001600 : ℝ) • d2
                  + (36284876 / 479001600 : ℝ) • d1
                  - (3250433 / 479001600 : ℝ) • d0)
      = A - B - (134211265 * h / 479001600 : ℝ) • C
        - (656185652 * h / 479001600 : ℝ) • D
        + (890175549 * h / 479001600 : ℝ) • F
        - (1446205080 * h / 479001600 : ℝ) • G
        + (1823311566 * h / 479001600 : ℝ) • I
        - (1710774528 * h / 479001600 : ℝ) • J
        + (1170597042 * h / 479001600 : ℝ) • K
        - (567450984 * h / 479001600 : ℝ) • L
        + (184776195 * h / 479001600 : ℝ) • P
        - (36284876 * h / 479001600 : ℝ) • Q := by
  subst hA; subst hB; subst hC; subst hD; subst hF; subst hG
  subst hI; subst hJ; subst hK; subst hL; subst hP; subst hQ
  module

private lemma am10Vec_residual_bound_alg_identity (M h : ℝ) :
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

private lemma am10Vec_triangle_aux
    {E : Type*} [NormedAddCommGroup E]
    (A B C D F G I J K L P Q : E) :
    ‖A - B - C - D + F - G + I - J + K - L + P - Q‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖F‖ + ‖G‖ + ‖I‖ + ‖J‖
          + ‖K‖ + ‖L‖ + ‖P‖ + ‖Q‖ := by
  have h1 : ‖A - B - C - D + F - G + I - J + K - L + P - Q‖
      ≤ ‖A - B - C - D + F - G + I - J + K - L + P‖ + ‖Q‖ := norm_sub_le _ _
  have h2 : ‖A - B - C - D + F - G + I - J + K - L + P‖
      ≤ ‖A - B - C - D + F - G + I - J + K - L‖ + ‖P‖ := norm_add_le _ _
  have h3 : ‖A - B - C - D + F - G + I - J + K - L‖
      ≤ ‖A - B - C - D + F - G + I - J + K‖ + ‖L‖ := norm_sub_le _ _
  have h4 : ‖A - B - C - D + F - G + I - J + K‖
      ≤ ‖A - B - C - D + F - G + I - J‖ + ‖K‖ := norm_add_le _ _
  have h5 : ‖A - B - C - D + F - G + I - J‖
      ≤ ‖A - B - C - D + F - G + I‖ + ‖J‖ := norm_sub_le _ _
  have h6 : ‖A - B - C - D + F - G + I‖
      ≤ ‖A - B - C - D + F - G‖ + ‖I‖ := norm_add_le _ _
  have h7 : ‖A - B - C - D + F - G‖
      ≤ ‖A - B - C - D + F‖ + ‖G‖ := norm_sub_le _ _
  have h8 : ‖A - B - C - D + F‖ ≤ ‖A - B - C - D‖ + ‖F‖ := norm_add_le _ _
  have h9 : ‖A - B - C - D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_sub_le _ _
  have h10 : ‖A - B - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le _ _
  have h11 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith

private lemma am10Vec_residual_twelve_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G I J K L P Q : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (134211265 * h / 479001600 : ℝ) • C
        - (656185652 * h / 479001600 : ℝ) • D
        + (890175549 * h / 479001600 : ℝ) • F
        - (1446205080 * h / 479001600 : ℝ) • G
        + (1823311566 * h / 479001600 : ℝ) • I
        - (1710774528 * h / 479001600 : ℝ) • J
        + (1170597042 * h / 479001600 : ℝ) • K
        - (567450984 * h / 479001600 : ℝ) • L
        + (184776195 * h / 479001600 : ℝ) • P
        - (36284876 * h / 479001600 : ℝ) • Q‖
      ≤ ‖A‖ + ‖B‖ + (134211265 * h / 479001600) * ‖C‖
          + (656185652 * h / 479001600) * ‖D‖
          + (890175549 * h / 479001600) * ‖F‖
          + (1446205080 * h / 479001600) * ‖G‖
          + (1823311566 * h / 479001600) * ‖I‖
          + (1710774528 * h / 479001600) * ‖J‖
          + (1170597042 * h / 479001600) * ‖K‖
          + (567450984 * h / 479001600) * ‖L‖
          + (184776195 * h / 479001600) * ‖P‖
          + (36284876 * h / 479001600) * ‖Q‖ := by
  have hcC_nn : 0 ≤ (134211265 * h / 479001600 : ℝ) := by linarith
  have hcD_nn : 0 ≤ (656185652 * h / 479001600 : ℝ) := by linarith
  have hcF_nn : 0 ≤ (890175549 * h / 479001600 : ℝ) := by linarith
  have hcG_nn : 0 ≤ (1446205080 * h / 479001600 : ℝ) := by linarith
  have hcI_nn : 0 ≤ (1823311566 * h / 479001600 : ℝ) := by linarith
  have hcJ_nn : 0 ≤ (1710774528 * h / 479001600 : ℝ) := by linarith
  have hcK_nn : 0 ≤ (1170597042 * h / 479001600 : ℝ) := by linarith
  have hcL_nn : 0 ≤ (567450984 * h / 479001600 : ℝ) := by linarith
  have hcP_nn : 0 ≤ (184776195 * h / 479001600 : ℝ) := by linarith
  have hcQ_nn : 0 ≤ (36284876 * h / 479001600 : ℝ) := by linarith
  have hC_norm :
      ‖(134211265 * h / 479001600 : ℝ) • C‖
        = (134211265 * h / 479001600) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcC_nn]
  have hD_norm :
      ‖(656185652 * h / 479001600 : ℝ) • D‖
        = (656185652 * h / 479001600) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcD_nn]
  have hF_norm :
      ‖(890175549 * h / 479001600 : ℝ) • F‖
        = (890175549 * h / 479001600) * ‖F‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcF_nn]
  have hG_norm :
      ‖(1446205080 * h / 479001600 : ℝ) • G‖
        = (1446205080 * h / 479001600) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcG_nn]
  have hI_norm :
      ‖(1823311566 * h / 479001600 : ℝ) • I‖
        = (1823311566 * h / 479001600) * ‖I‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcI_nn]
  have hJ_norm :
      ‖(1710774528 * h / 479001600 : ℝ) • J‖
        = (1710774528 * h / 479001600) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcJ_nn]
  have hK_norm :
      ‖(1170597042 * h / 479001600 : ℝ) • K‖
        = (1170597042 * h / 479001600) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcK_nn]
  have hL_norm :
      ‖(567450984 * h / 479001600 : ℝ) • L‖
        = (567450984 * h / 479001600) * ‖L‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcL_nn]
  have hP_norm :
      ‖(184776195 * h / 479001600 : ℝ) • P‖
        = (184776195 * h / 479001600) * ‖P‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcP_nn]
  have hQ_norm :
      ‖(36284876 * h / 479001600 : ℝ) • Q‖
        = (36284876 * h / 479001600) * ‖Q‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcQ_nn]
  have htri := am10Vec_triangle_aux A B
    ((134211265 * h / 479001600 : ℝ) • C)
    ((656185652 * h / 479001600 : ℝ) • D)
    ((890175549 * h / 479001600 : ℝ) • F)
    ((1446205080 * h / 479001600 : ℝ) • G)
    ((1823311566 * h / 479001600 : ℝ) • I)
    ((1710774528 * h / 479001600 : ℝ) • J)
    ((1170597042 * h / 479001600 : ℝ) • K)
    ((567450984 * h / 479001600 : ℝ) • L)
    ((184776195 * h / 479001600 : ℝ) • P)
    ((36284876 * h / 479001600 : ℝ) • Q)
  rw [hC_norm, hD_norm, hF_norm, hG_norm, hI_norm, hJ_norm, hK_norm, hL_norm,
    hP_norm, hQ_norm] at htri
  exact htri

private lemma am10Vec_residual_combine_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G I J K L P Q : E) (M h : ℝ) (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (hA_bd : ‖A‖ ≤ M / 479001600 * (10 * h) ^ 12)
    (hB_bd : ‖B‖ ≤ M / 479001600 * (9 * h) ^ 12)
    (hC_bd : ‖C‖ ≤ M / 39916800 * (10 * h) ^ 11)
    (hD_bd : ‖D‖ ≤ M / 39916800 * (9 * h) ^ 11)
    (hF_bd : ‖F‖ ≤ M / 39916800 * (8 * h) ^ 11)
    (hG_bd : ‖G‖ ≤ M / 39916800 * (7 * h) ^ 11)
    (hI_bd : ‖I‖ ≤ M / 39916800 * (6 * h) ^ 11)
    (hJ_bd : ‖J‖ ≤ M / 39916800 * (5 * h) ^ 11)
    (hK_bd : ‖K‖ ≤ M / 39916800 * (4 * h) ^ 11)
    (hL_bd : ‖L‖ ≤ M / 39916800 * (3 * h) ^ 11)
    (hP_bd : ‖P‖ ≤ M / 39916800 * (2 * h) ^ 11)
    (hQ_bd : ‖Q‖ ≤ M / 39916800 * h ^ 11) :
    ‖A - B - (134211265 * h / 479001600 : ℝ) • C
        - (656185652 * h / 479001600 : ℝ) • D
        + (890175549 * h / 479001600 : ℝ) • F
        - (1446205080 * h / 479001600 : ℝ) • G
        + (1823311566 * h / 479001600 : ℝ) • I
        - (1710774528 * h / 479001600 : ℝ) • J
        + (1170597042 * h / 479001600 : ℝ) • K
        - (567450984 * h / 479001600 : ℝ) • L
        + (184776195 * h / 479001600 : ℝ) • P
        - (36284876 * h / 479001600 : ℝ) • Q‖
      ≤ 5045 * M * h ^ 12 := by
  have htri := am10Vec_residual_twelve_term_triangle A B C D F G I J K L P Q h hh
  have hcC_nn : 0 ≤ 134211265 * h / 479001600 := by linarith
  have hcD_nn : 0 ≤ 656185652 * h / 479001600 := by linarith
  have hcF_nn : 0 ≤ 890175549 * h / 479001600 := by linarith
  have hcG_nn : 0 ≤ 1446205080 * h / 479001600 := by linarith
  have hcI_nn : 0 ≤ 1823311566 * h / 479001600 := by linarith
  have hcJ_nn : 0 ≤ 1710774528 * h / 479001600 := by linarith
  have hcK_nn : 0 ≤ 1170597042 * h / 479001600 := by linarith
  have hcL_nn : 0 ≤ 567450984 * h / 479001600 := by linarith
  have hcP_nn : 0 ≤ 184776195 * h / 479001600 := by linarith
  have hcQ_nn : 0 ≤ 36284876 * h / 479001600 := by linarith
  have hCbd_s : (134211265 * h / 479001600) * ‖C‖
      ≤ (134211265 * h / 479001600) * (M / 39916800 * (10 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hC_bd hcC_nn
  have hDbd_s : (656185652 * h / 479001600) * ‖D‖
      ≤ (656185652 * h / 479001600) * (M / 39916800 * (9 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hD_bd hcD_nn
  have hFbd_s : (890175549 * h / 479001600) * ‖F‖
      ≤ (890175549 * h / 479001600) * (M / 39916800 * (8 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hF_bd hcF_nn
  have hGbd_s : (1446205080 * h / 479001600) * ‖G‖
      ≤ (1446205080 * h / 479001600) * (M / 39916800 * (7 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hG_bd hcG_nn
  have hIbd_s : (1823311566 * h / 479001600) * ‖I‖
      ≤ (1823311566 * h / 479001600) * (M / 39916800 * (6 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hI_bd hcI_nn
  have hJbd_s : (1710774528 * h / 479001600) * ‖J‖
      ≤ (1710774528 * h / 479001600) * (M / 39916800 * (5 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hJ_bd hcJ_nn
  have hKbd_s : (1170597042 * h / 479001600) * ‖K‖
      ≤ (1170597042 * h / 479001600) * (M / 39916800 * (4 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hK_bd hcK_nn
  have hLbd_s : (567450984 * h / 479001600) * ‖L‖
      ≤ (567450984 * h / 479001600) * (M / 39916800 * (3 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hL_bd hcL_nn
  have hPbd_s : (184776195 * h / 479001600) * ‖P‖
      ≤ (184776195 * h / 479001600) * (M / 39916800 * (2 * h) ^ 11) :=
    mul_le_mul_of_nonneg_left hP_bd hcP_nn
  have hQbd_s : (36284876 * h / 479001600) * ‖Q‖
      ≤ (36284876 * h / 479001600) * (M / 39916800 * h ^ 11) :=
    mul_le_mul_of_nonneg_left hQ_bd hcQ_nn
  have hbound_alg := am10Vec_residual_bound_alg_identity M h
  have hh12_nn : 0 ≤ h ^ 12 := by positivity
  have hMh12_nn : 0 ≤ M * h ^ 12 := mul_nonneg hMnn hh12_nn
  have hslack : (251196920117213671 / 49792216320000 : ℝ) * M * h ^ 12
      ≤ 5045 * M * h ^ 12 := by
    rw [mul_assoc, mul_assoc (5045 : ℝ)]
    have hle : (251196920117213671 / 49792216320000 : ℝ) ≤ 5045 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh12_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hFbd_s,
    hGbd_s, hIbd_s, hJbd_s, hKbd_s, hLbd_s, hPbd_s, hQbd_s]

theorem am10Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 12 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 12 y t‖ ≤ M)
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
    ‖am10VecResidual h t y‖ ≤ (5045 : ℝ) * M * h ^ 12 := by
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
    y_twelfth_order_taylor_remainder_vec hy hbnd ht ht9h h9h
  have hRy10 :=
    y_twelfth_order_taylor_remainder_vec hy hbnd ht ht10h h10h
  have hRyp1 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht ht9h h9h
  have hRyp10 :=
    derivY_eleventh_order_taylor_remainder_vec hy hbnd ht ht10h h10h
  unfold am10VecResidual
  set y0 : E := y t with hy0_def
  set y9 : E := y (t + 9 * h) with hy9_def
  set y10 : E := y (t + 10 * h) with hy10_def
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
  set d10 : E := deriv y (t + 10 * h) with hd10_def
  set d2t : E := iteratedDeriv 2 y t with hd2t_def
  set d3t : E := iteratedDeriv 3 y t with hd3t_def
  set d4t : E := iteratedDeriv 4 y t with hd4t_def
  set d5t : E := iteratedDeriv 5 y t with hd5t_def
  set d6t : E := iteratedDeriv 6 y t with hd6t_def
  set d7t : E := iteratedDeriv 7 y t with hd7t_def
  set d8t : E := iteratedDeriv 8 y t with hd8t_def
  set d9t : E := iteratedDeriv 9 y t with hd9t_def
  set d10t : E := iteratedDeriv 10 y t with hd10t_def
  set d11t : E := iteratedDeriv 11 y t with hd11t_def
  clear_value y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t
  set A : E := y10 - y0 - (10 * h) • d0
            - ((10 * h) ^ 2 / 2) • d2t
            - ((10 * h) ^ 3 / 6) • d3t
            - ((10 * h) ^ 4 / 24) • d4t
            - ((10 * h) ^ 5 / 120) • d5t
            - ((10 * h) ^ 6 / 720) • d6t
            - ((10 * h) ^ 7 / 5040) • d7t
            - ((10 * h) ^ 8 / 40320) • d8t
            - ((10 * h) ^ 9 / 362880) • d9t
            - ((10 * h) ^ 10 / 3628800) • d10t
            - ((10 * h) ^ 11 / 39916800) • d11t with hA_def
  set B : E := y9 - y0 - (9 * h) • d0
            - ((9 * h) ^ 2 / 2) • d2t
            - ((9 * h) ^ 3 / 6) • d3t
            - ((9 * h) ^ 4 / 24) • d4t
            - ((9 * h) ^ 5 / 120) • d5t
            - ((9 * h) ^ 6 / 720) • d6t
            - ((9 * h) ^ 7 / 5040) • d7t
            - ((9 * h) ^ 8 / 40320) • d8t
            - ((9 * h) ^ 9 / 362880) • d9t
            - ((9 * h) ^ 10 / 3628800) • d10t
            - ((9 * h) ^ 11 / 39916800) • d11t with hB_def
  set C : E := d10 - d0 - (10 * h) • d2t
            - ((10 * h) ^ 2 / 2) • d3t
            - ((10 * h) ^ 3 / 6) • d4t
            - ((10 * h) ^ 4 / 24) • d5t
            - ((10 * h) ^ 5 / 120) • d6t
            - ((10 * h) ^ 6 / 720) • d7t
            - ((10 * h) ^ 7 / 5040) • d8t
            - ((10 * h) ^ 8 / 40320) • d9t
            - ((10 * h) ^ 9 / 362880) • d10t
            - ((10 * h) ^ 10 / 3628800) • d11t with hC_def
  set D : E := d9 - d0 - (9 * h) • d2t
            - ((9 * h) ^ 2 / 2) • d3t
            - ((9 * h) ^ 3 / 6) • d4t
            - ((9 * h) ^ 4 / 24) • d5t
            - ((9 * h) ^ 5 / 120) • d6t
            - ((9 * h) ^ 6 / 720) • d7t
            - ((9 * h) ^ 7 / 5040) • d8t
            - ((9 * h) ^ 8 / 40320) • d9t
            - ((9 * h) ^ 9 / 362880) • d10t
            - ((9 * h) ^ 10 / 3628800) • d11t with hD_def
  set F : E := d8 - d0 - (8 * h) • d2t
            - ((8 * h) ^ 2 / 2) • d3t
            - ((8 * h) ^ 3 / 6) • d4t
            - ((8 * h) ^ 4 / 24) • d5t
            - ((8 * h) ^ 5 / 120) • d6t
            - ((8 * h) ^ 6 / 720) • d7t
            - ((8 * h) ^ 7 / 5040) • d8t
            - ((8 * h) ^ 8 / 40320) • d9t
            - ((8 * h) ^ 9 / 362880) • d10t
            - ((8 * h) ^ 10 / 3628800) • d11t with hF_def
  set G : E := d7 - d0 - (7 * h) • d2t
            - ((7 * h) ^ 2 / 2) • d3t
            - ((7 * h) ^ 3 / 6) • d4t
            - ((7 * h) ^ 4 / 24) • d5t
            - ((7 * h) ^ 5 / 120) • d6t
            - ((7 * h) ^ 6 / 720) • d7t
            - ((7 * h) ^ 7 / 5040) • d8t
            - ((7 * h) ^ 8 / 40320) • d9t
            - ((7 * h) ^ 9 / 362880) • d10t
            - ((7 * h) ^ 10 / 3628800) • d11t with hG_def
  set I : E := d6 - d0 - (6 * h) • d2t
            - ((6 * h) ^ 2 / 2) • d3t
            - ((6 * h) ^ 3 / 6) • d4t
            - ((6 * h) ^ 4 / 24) • d5t
            - ((6 * h) ^ 5 / 120) • d6t
            - ((6 * h) ^ 6 / 720) • d7t
            - ((6 * h) ^ 7 / 5040) • d8t
            - ((6 * h) ^ 8 / 40320) • d9t
            - ((6 * h) ^ 9 / 362880) • d10t
            - ((6 * h) ^ 10 / 3628800) • d11t with hI_def
  set J : E := d5 - d0 - (5 * h) • d2t
            - ((5 * h) ^ 2 / 2) • d3t
            - ((5 * h) ^ 3 / 6) • d4t
            - ((5 * h) ^ 4 / 24) • d5t
            - ((5 * h) ^ 5 / 120) • d6t
            - ((5 * h) ^ 6 / 720) • d7t
            - ((5 * h) ^ 7 / 5040) • d8t
            - ((5 * h) ^ 8 / 40320) • d9t
            - ((5 * h) ^ 9 / 362880) • d10t
            - ((5 * h) ^ 10 / 3628800) • d11t with hJ_def
  set K : E := d4 - d0 - (4 * h) • d2t
            - ((4 * h) ^ 2 / 2) • d3t
            - ((4 * h) ^ 3 / 6) • d4t
            - ((4 * h) ^ 4 / 24) • d5t
            - ((4 * h) ^ 5 / 120) • d6t
            - ((4 * h) ^ 6 / 720) • d7t
            - ((4 * h) ^ 7 / 5040) • d8t
            - ((4 * h) ^ 8 / 40320) • d9t
            - ((4 * h) ^ 9 / 362880) • d10t
            - ((4 * h) ^ 10 / 3628800) • d11t with hK_def
  set L : E := d3 - d0 - (3 * h) • d2t
            - ((3 * h) ^ 2 / 2) • d3t
            - ((3 * h) ^ 3 / 6) • d4t
            - ((3 * h) ^ 4 / 24) • d5t
            - ((3 * h) ^ 5 / 120) • d6t
            - ((3 * h) ^ 6 / 720) • d7t
            - ((3 * h) ^ 7 / 5040) • d8t
            - ((3 * h) ^ 8 / 40320) • d9t
            - ((3 * h) ^ 9 / 362880) • d10t
            - ((3 * h) ^ 10 / 3628800) • d11t with hL_def
  set P : E := d2 - d0 - (2 * h) • d2t
            - ((2 * h) ^ 2 / 2) • d3t
            - ((2 * h) ^ 3 / 6) • d4t
            - ((2 * h) ^ 4 / 24) • d5t
            - ((2 * h) ^ 5 / 120) • d6t
            - ((2 * h) ^ 6 / 720) • d7t
            - ((2 * h) ^ 7 / 5040) • d8t
            - ((2 * h) ^ 8 / 40320) • d9t
            - ((2 * h) ^ 9 / 362880) • d10t
            - ((2 * h) ^ 10 / 3628800) • d11t with hP_def
  set Q : E := d1 - d0 - h • d2t
            - (h ^ 2 / 2) • d3t
            - (h ^ 3 / 6) • d4t
            - (h ^ 4 / 24) • d5t
            - (h ^ 5 / 120) • d6t
            - (h ^ 6 / 720) • d7t
            - (h ^ 7 / 5040) • d8t
            - (h ^ 8 / 40320) • d9t
            - (h ^ 9 / 362880) • d10t
            - (h ^ 10 / 3628800) • d11t with hQ_def
  clear_value A B C D F G I J K L P Q
  have hLTE_eq :=
    am10Vec_residual_alg_identity y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
      d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t h A B C D F G I J K L P Q
      hA_def hB_def hC_def hD_def hF_def hG_def hI_def hJ_def hK_def hL_def
      hP_def hQ_def
  rw [hLTE_eq]
  have hA_bd : ‖A‖ ≤ M / 479001600 * (10 * h) ^ 12 := hRy10
  have hB_bd : ‖B‖ ≤ M / 479001600 * (9 * h) ^ 12 := hRy9
  have hC_bd : ‖C‖ ≤ M / 39916800 * (10 * h) ^ 11 := hRyp10
  have hD_bd : ‖D‖ ≤ M / 39916800 * (9 * h) ^ 11 := hRyp9
  have hF_bd : ‖F‖ ≤ M / 39916800 * (8 * h) ^ 11 := hRyp8
  have hG_bd : ‖G‖ ≤ M / 39916800 * (7 * h) ^ 11 := hRyp7
  have hI_bd : ‖I‖ ≤ M / 39916800 * (6 * h) ^ 11 := hRyp6
  have hJ_bd : ‖J‖ ≤ M / 39916800 * (5 * h) ^ 11 := hRyp5
  have hK_bd : ‖K‖ ≤ M / 39916800 * (4 * h) ^ 11 := hRyp4
  have hL_bd : ‖L‖ ≤ M / 39916800 * (3 * h) ^ 11 := hRyp3
  have hP_bd : ‖P‖ ≤ M / 39916800 * (2 * h) ^ 11 := hRyp2
  have hQ_bd : ‖Q‖ ≤ M / 39916800 * h ^ 11 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  exact am10Vec_residual_combine_aux A B C D F G I J K L P Q M h hh hMnn
    hA_bd hB_bd hC_bd hD_bd hF_bd hG_bd hI_bd hJ_bd hK_bd hL_bd hP_bd hQ_bd

theorem am10Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 12 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 10) * h ≤ T →
        ‖am10VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 12 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_twelve_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
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
  show ‖am10VecResidual h t y‖ ≤ 5045 * M * h ^ 12
  exact am10Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem
    ht10h_mem hh.le

theorem am10Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 12 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (134211265 / 479001600 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsAM10TrajectoryVec h f t₀ yseq →
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
      ‖yseq 9 - y (t₀ + 9 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 9) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((37 * L) * T) * ε₀ + K * h ^ 10 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am10Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((37 * L) * T) * (2 * C), min δ 1, ?_,
    lt_min hδ_pos (by norm_num), ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδg_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd N hNh
  have hδ_le : h ≤ δ := le_trans hδg_le (min_le_left δ 1)
  have h_le_one : h ≤ 1 := le_trans hδg_le (min_le_right δ 1)
  have hh12_le_h11 : h ^ 12 ≤ h ^ 11 := by
    calc
      h ^ 12 = h ^ 11 * h := by ring
      _ ≤ h ^ 11 * 1 :=
        mul_le_mul_of_nonneg_left h_le_one (by positivity)
      _ = h ^ 11 := by ring
  set eN : ℕ → ℝ :=
    fun k => ‖yseq k - y (t₀ + (k : ℝ) * h)‖ with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (max (max (max (max (max
        (eN k) (eN (k + 1))) (eN (k + 2))) (eN (k + 3))) (eN (k + 4)))
        (eN (k + 5))) (eN (k + 6))) (eN (k + 7))) (eN (k + 8))) (eN (k + 9))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => norm_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
        (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
          (heN_nn k)))))))))
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (max (max (max (max (max
        (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4)) (eN 5)) (eN 6)) (eN 7)) (eN 8)) (eN 9)
        ≤ ε₀
    refine max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
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
    · show ‖yseq 9 - y (t₀ + ((9 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((9 : ℕ) : ℝ) * h = 9 * h := by push_cast; ring
      rw [hcast]; simpa using he9_bd
  have h37L_nn : (0 : ℝ) ≤ 37 * L := by linarith
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 10) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (37 * L)) * EN n + (2 * C) * h ^ 11 := by
    intro n hnh_le
    have honestep := am10Vec_one_step_error_pair_bound
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
    have hcast10 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) =
        (n : ℝ) + 10 := by
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
    have heq_eN_n10 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast10]
    show max (max (max (max (max (max (max (max (max
            (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * (37 * L))
            * max (max (max (max (max (max (max (max (max (eN n) (eN (n + 1)))
                  (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
          + (2 * C) * h ^ 11
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5,
      heq_eN_n6, heq_eN_n7, heq_eN_n8, heq_eN_n9, heq_eN_n10]
    have h2τ : 2 * ‖am10VecResidual h (t₀ + (n : ℝ) * h) y‖
        ≤ (2 * C) * h ^ 11 := by
      have h2res : 2 * ‖am10VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ 2 * (C * h ^ 12) :=
        mul_le_mul_of_nonneg_left hres (by norm_num)
      have hC2_nn : (0 : ℝ) ≤ 2 * C := by positivity
      have hweak : 2 * (C * h ^ 12) ≤ (2 * C) * h ^ 11 := by
        have := mul_le_mul_of_nonneg_left hh12_le_h11 hC2_nn
        linarith
      linarith
    linarith [honestep, h2τ]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((37 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((37 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh10_nn : 0 ≤ h ^ 10 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((37 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((37 * L) * T) * ε₀
            + T * Real.exp ((37 * L) * T) * (2 * C) * h ^ 10 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((37 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((37 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh10_nn : 0 ≤ T * Real.exp ((37 * L) * T) * (2 * C) * h ^ 10 :=
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
  | 9, _ =>
    have hbase : ‖yseq 9 - y (t₀ + ((9 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((9 : ℕ) : ℝ) * h = 9 * h := by push_cast; ring
      rw [hcast]; simpa using he9_bd
    exact hbase_to_headline _ hbase
  | N' + 10, hNh =>
    have hcast : (((N' + 10 : ℕ) : ℝ) + 9) = (N' : ℝ) + 19 := by
      push_cast; ring
    have hN_hyp : ((N' : ℝ) + 19) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (37 * L)) * EN n + (2 * C) * h ^ (10 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (10 + 1) = (2 * C) * h ^ 11 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 10 ≤ (N' : ℝ) + 19 := by linarith
      have h_mul : ((n : ℝ) + 10) * h ≤ ((N' : ℝ) + 19) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have hle : (N' : ℝ) + 1 ≤ (N' : ℝ) + 19 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 37 * L) (C := 2 * C) (T := T) (p := 10)
        (e := EN) (N := N' + 1)
        hh.le h37L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 10) ≤ EN (N' + 1) := by
      show eN (N' + 10)
        ≤ max (max (max (max (max (max (max (max (max
              (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4)))
              (eN (N' + 1 + 5))) (eN (N' + 1 + 6))) (eN (N' + 1 + 7)))
              (eN (N' + 1 + 8))) (eN (N' + 1 + 9))
      have heq : N' + 10 = N' + 1 + 9 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((37 * L) * T) * EN 0 ≤ Real.exp ((37 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show ‖yseq (N' + 10) - y (t₀ + ((N' + 10 : ℕ) : ℝ) * h)‖
        ≤ Real.exp ((37 * L) * T) * ε₀
          + T * Real.exp ((37 * L) * T) * (2 * C) * h ^ 10
    have heN_eq :
        eN (N' + 10)
          = ‖yseq (N' + 10) - y (t₀ + ((N' + 10 : ℕ) : ℝ) * h)‖ := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
