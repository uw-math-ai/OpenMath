import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB6VectorConvergence
import OpenMath.LMMAB7Convergence

/-! ## Adams-Bashforth 7-step Vector Quantitative Convergence Chain (Iserles §1.2)

Finite-dimensional vector-valued analogue of the scalar AB7 quantitative
convergence chain in `OpenMath.LMMAB7Convergence`.
-/

namespace LMM

/-- AB7 vector iteration with seven starting samples. -/
noncomputable def ab7IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) : ℕ → E
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | 6 => y₆
  | n + 7 =>
      ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
        + h • ((198721 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6))
              - (447288 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5))
              + (705549 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4))
              - (688256 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3))
              + (407139 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2))
              - (134472 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1))
              + (19087 / 60480 : ℝ) • f (t₀ + (n : ℝ) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n))

@[simp] lemma ab7IterVec_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) :
    ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 0 = y₀ := rfl

@[simp] lemma ab7IterVec_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) :
    ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 1 = y₁ := rfl

@[simp] lemma ab7IterVec_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) :
    ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 2 = y₂ := rfl

@[simp] lemma ab7IterVec_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) :
    ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 3 = y₃ := rfl

@[simp] lemma ab7IterVec_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) :
    ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 4 = y₄ := rfl

@[simp] lemma ab7IterVec_five
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) :
    ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 5 = y₅ := rfl

@[simp] lemma ab7IterVec_six
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) :
    ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 6 = y₆ := rfl

lemma ab7IterVec_succ_seven
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) (n : ℕ) :
    ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7)
      = ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
          + h • ((198721 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                  (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6))
                - (447288 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                    (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5))
                + (705549 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                    (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4))
                - (688256 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                    (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3))
                + (407139 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                    (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2))
                - (134472 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                    (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1))
                + (19087 / 60480 : ℝ) • f (t₀ + (n : ℝ) * h)
                    (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n)) := rfl

/-- Vector AB7 local truncation residual. -/
noncomputable def ab7VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 7 * h) - y (t + 6 * h)
    - h • ((198721 / 60480 : ℝ) • deriv y (t + 6 * h)
          - (447288 / 60480 : ℝ) • deriv y (t + 5 * h)
          + (705549 / 60480 : ℝ) • deriv y (t + 4 * h)
          - (688256 / 60480 : ℝ) • deriv y (t + 3 * h)
          + (407139 / 60480 : ℝ) • deriv y (t + 2 * h)
          - (134472 / 60480 : ℝ) • deriv y (t + h)
          + (19087 / 60480 : ℝ) • deriv y t)

theorem ab7Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab7VecResidual h t y
      = y (t + 7 * h) - y (t + 6 * h)
          - h • ((198721 / 60480 : ℝ) • deriv y (t + 6 * h)
                - (447288 / 60480 : ℝ) • deriv y (t + 5 * h)
                + (705549 / 60480 : ℝ) • deriv y (t + 4 * h)
                - (688256 / 60480 : ℝ) • deriv y (t + 3 * h)
                + (407139 / 60480 : ℝ) • deriv y (t + 2 * h)
                - (134472 / 60480 : ℝ) • deriv y (t + h)
                + (19087 / 60480 : ℝ) • deriv y t) := rfl

theorem ab7Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7)
        - y (t₀ + ((n : ℝ) + 7) * h)‖
      ≤ ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
            - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (198721 / 60480) * h * L
            * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
                - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (447288 / 60480) * h * L
            * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (705549 / 60480) * h * L
            * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (688256 / 60480) * h * L
            * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (407139 / 60480) * h * L
            * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (134472 / 60480) * h * L
            * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (19087 / 60480) * h * L
            * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n
                - y (t₀ + (n : ℝ) * h)‖
        + ‖ab7VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n with hyn_def
  set yn1 : E := ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1) with hyn1_def
  set yn2 : E := ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2) with hyn2_def
  set yn3 : E := ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3) with hyn3_def
  set yn4 : E := ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4) with hyn4_def
  set yn5 : E := ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5) with hyn5_def
  set yn6 : E := ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6) with hyn6_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set zn3 : E := y tn3 with hzn3_def
  set zn4 : E := y tn4 with hzn4_def
  set zn5 : E := y tn5 with hzn5_def
  set zn6 : E := y tn6 with hzn6_def
  set zn7 : E := y tn7 with hzn7_def
  set τ : E := ab7VecResidual h tn y with hτ_def
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  have htn_6h : tn + 6 * h = tn6 := by simp [htn_def, htn6_def]; ring
  have htn_7h : tn + 7 * h = tn7 := by simp [htn_def, htn7_def]; ring
  have hτ_eq :
      τ = zn7 - zn6
            - h • ((198721 / 60480 : ℝ) • f tn6 zn6
                  - (447288 / 60480 : ℝ) • f tn5 zn5
                  + (705549 / 60480 : ℝ) • f tn4 zn4
                  - (688256 / 60480 : ℝ) • f tn3 zn3
                  + (407139 / 60480 : ℝ) • f tn2 zn2
                  - (134472 / 60480 : ℝ) • f tn1 zn1
                  + (19087 / 60480 : ℝ) • f tn zn) := by
    show ab7VecResidual h tn y = _
    unfold ab7VecResidual
    rw [htn1_h, htn_2h, htn_3h, htn_4h, htn_5h, htn_6h, htn_7h,
      hyf tn6, hyf tn5, hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  have hstep : ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7)
      = yn6 + h • ((198721 / 60480 : ℝ) • f tn6 yn6
                    - (447288 / 60480 : ℝ) • f tn5 yn5
                    + (705549 / 60480 : ℝ) • f tn4 yn4
                    - (688256 / 60480 : ℝ) • f tn3 yn3
                    + (407139 / 60480 : ℝ) • f tn2 yn2
                    - (134472 / 60480 : ℝ) • f tn1 yn1
                    + (19087 / 60480 : ℝ) • f tn yn) := by
    show ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) = _
    rw [ab7IterVec_succ_seven]
  have halg : ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - zn7
      = (yn6 - zn6)
        + h • ((198721 / 60480 : ℝ) • (f tn6 yn6 - f tn6 zn6))
        - h • ((447288 / 60480 : ℝ) • (f tn5 yn5 - f tn5 zn5))
        + h • ((705549 / 60480 : ℝ) • (f tn4 yn4 - f tn4 zn4))
        - h • ((688256 / 60480 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        + h • ((407139 / 60480 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        - h • ((134472 / 60480 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        + h • ((19087 / 60480 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    rw [hstep, hτ_eq]
    simp only [smul_sub, smul_add]
    abel_nf
  have hLip6 : ‖f tn6 yn6 - f tn6 zn6‖ ≤ L * ‖yn6 - zn6‖ := hf tn6 yn6 zn6
  have hLip5 : ‖f tn5 yn5 - f tn5 zn5‖ ≤ L * ‖yn5 - zn5‖ := hf tn5 yn5 zn5
  have hLip4 : ‖f tn4 yn4 - f tn4 zn4‖ ≤ L * ‖yn4 - zn4‖ := hf tn4 yn4 zn4
  have hLip3 : ‖f tn3 yn3 - f tn3 zn3‖ ≤ L * ‖yn3 - zn3‖ := hf tn3 yn3 zn3
  have hLip2 : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ := hf tn2 yn2 zn2
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ := hf tn1 yn1 zn1
  have hLip0 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ := hf tn yn zn
  have h198721_nn : (0 : ℝ) ≤ 198721 / 60480 := by norm_num
  have h447288_nn : (0 : ℝ) ≤ 447288 / 60480 := by norm_num
  have h705549_nn : (0 : ℝ) ≤ 705549 / 60480 := by norm_num
  have h688256_nn : (0 : ℝ) ≤ 688256 / 60480 := by norm_num
  have h407139_nn : (0 : ℝ) ≤ 407139 / 60480 := by norm_num
  have h134472_nn : (0 : ℝ) ≤ 134472 / 60480 := by norm_num
  have h19087_nn : (0 : ℝ) ≤ 19087 / 60480 := by norm_num
  have h198721_norm :
      ‖h • ((198721 / 60480 : ℝ) • (f tn6 yn6 - f tn6 zn6))‖
        ≤ (198721 / 60480) * h * L * ‖yn6 - zn6‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h198721_nn]
    have : h * ((198721 / 60480 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((198721 / 60480 : ℝ) * (L * ‖yn6 - zn6‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip6 h198721_nn
    calc
      h * ((198721 / 60480 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
          ≤ h * ((198721 / 60480 : ℝ) * (L * ‖yn6 - zn6‖)) := this
      _ = (198721 / 60480) * h * L * ‖yn6 - zn6‖ := by ring
  have h447288_norm :
      ‖h • ((447288 / 60480 : ℝ) • (f tn5 yn5 - f tn5 zn5))‖
        ≤ (447288 / 60480) * h * L * ‖yn5 - zn5‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h447288_nn]
    have : h * ((447288 / 60480 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((447288 / 60480 : ℝ) * (L * ‖yn5 - zn5‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip5 h447288_nn
    calc
      h * ((447288 / 60480 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
          ≤ h * ((447288 / 60480 : ℝ) * (L * ‖yn5 - zn5‖)) := this
      _ = (447288 / 60480) * h * L * ‖yn5 - zn5‖ := by ring
  have h705549_norm :
      ‖h • ((705549 / 60480 : ℝ) • (f tn4 yn4 - f tn4 zn4))‖
        ≤ (705549 / 60480) * h * L * ‖yn4 - zn4‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h705549_nn]
    have : h * ((705549 / 60480 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((705549 / 60480 : ℝ) * (L * ‖yn4 - zn4‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip4 h705549_nn
    calc
      h * ((705549 / 60480 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
          ≤ h * ((705549 / 60480 : ℝ) * (L * ‖yn4 - zn4‖)) := this
      _ = (705549 / 60480) * h * L * ‖yn4 - zn4‖ := by ring
  have h688256_norm :
      ‖h • ((688256 / 60480 : ℝ) • (f tn3 yn3 - f tn3 zn3))‖
        ≤ (688256 / 60480) * h * L * ‖yn3 - zn3‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h688256_nn]
    have : h * ((688256 / 60480 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((688256 / 60480 : ℝ) * (L * ‖yn3 - zn3‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip3 h688256_nn
    calc
      h * ((688256 / 60480 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
          ≤ h * ((688256 / 60480 : ℝ) * (L * ‖yn3 - zn3‖)) := this
      _ = (688256 / 60480) * h * L * ‖yn3 - zn3‖ := by ring
  have h407139_norm :
      ‖h • ((407139 / 60480 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
        ≤ (407139 / 60480) * h * L * ‖yn2 - zn2‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h407139_nn]
    have : h * ((407139 / 60480 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((407139 / 60480 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 h407139_nn
    calc
      h * ((407139 / 60480 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
          ≤ h * ((407139 / 60480 : ℝ) * (L * ‖yn2 - zn2‖)) := this
      _ = (407139 / 60480) * h * L * ‖yn2 - zn2‖ := by ring
  have h134472_norm :
      ‖h • ((134472 / 60480 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
        ≤ (134472 / 60480) * h * L * ‖yn1 - zn1‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h134472_nn]
    have : h * ((134472 / 60480 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((134472 / 60480 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 h134472_nn
    calc
      h * ((134472 / 60480 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
          ≤ h * ((134472 / 60480 : ℝ) * (L * ‖yn1 - zn1‖)) := this
      _ = (134472 / 60480) * h * L * ‖yn1 - zn1‖ := by ring
  have h19087_norm :
      ‖h • ((19087 / 60480 : ℝ) • (f tn yn - f tn zn))‖
        ≤ (19087 / 60480) * h * L * ‖yn - zn‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h19087_nn]
    have : h * ((19087 / 60480 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((19087 / 60480 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 h19087_nn
    calc
      h * ((19087 / 60480 : ℝ) * ‖f tn yn - f tn zn‖)
          ≤ h * ((19087 / 60480 : ℝ) * (L * ‖yn - zn‖)) := this
      _ = (19087 / 60480) * h * L * ‖yn - zn‖ := by ring
  set A : E := yn6 - zn6 with hA_def
  set B : E := h • ((198721 / 60480 : ℝ) • (f tn6 yn6 - f tn6 zn6)) with hB_def
  set C : E := h • ((447288 / 60480 : ℝ) • (f tn5 yn5 - f tn5 zn5)) with hC_def
  set D : E := h • ((705549 / 60480 : ℝ) • (f tn4 yn4 - f tn4 zn4)) with hD_def
  set G : E := h • ((688256 / 60480 : ℝ) • (f tn3 yn3 - f tn3 zn3)) with hG_def
  set J : E := h • ((407139 / 60480 : ℝ) • (f tn2 yn2 - f tn2 zn2)) with hJ_def
  set K : E := h • ((134472 / 60480 : ℝ) • (f tn1 yn1 - f tn1 zn1)) with hK_def
  set R : E := h • ((19087 / 60480 : ℝ) • (f tn yn - f tn zn)) with hR_def
  have htri : ‖A + B - C + D - G + J - K + R - τ‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖G‖ + ‖J‖ + ‖K‖ + ‖R‖ + ‖τ‖ := by
    have h1 : ‖A + B - C + D - G + J - K + R - τ‖
        ≤ ‖A + B - C + D - G + J - K + R‖ + ‖τ‖ := norm_sub_le _ _
    have h2 : ‖A + B - C + D - G + J - K + R‖
        ≤ ‖A + B - C + D - G + J - K‖ + ‖R‖ := norm_add_le _ _
    have h3 : ‖A + B - C + D - G + J - K‖
        ≤ ‖A + B - C + D - G + J‖ + ‖K‖ := norm_sub_le _ _
    have h4 : ‖A + B - C + D - G + J‖
        ≤ ‖A + B - C + D - G‖ + ‖J‖ := norm_add_le _ _
    have h5 : ‖A + B - C + D - G‖
        ≤ ‖A + B - C + D‖ + ‖G‖ := norm_sub_le _ _
    have h6 : ‖A + B - C + D‖
        ≤ ‖A + B - C‖ + ‖D‖ := norm_add_le _ _
    have h7 : ‖A + B - C‖ ≤ ‖A + B‖ + ‖C‖ := norm_sub_le _ _
    have h8 : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    linarith
  have hB_bd : ‖B‖ ≤ (198721 / 60480) * h * L * ‖yn6 - zn6‖ := by
    simpa [hB_def] using h198721_norm
  have hC_bd : ‖C‖ ≤ (447288 / 60480) * h * L * ‖yn5 - zn5‖ := by
    simpa [hC_def] using h447288_norm
  have hD_bd : ‖D‖ ≤ (705549 / 60480) * h * L * ‖yn4 - zn4‖ := by
    simpa [hD_def] using h705549_norm
  have hG_bd : ‖G‖ ≤ (688256 / 60480) * h * L * ‖yn3 - zn3‖ := by
    simpa [hG_def] using h688256_norm
  have hJ_bd : ‖J‖ ≤ (407139 / 60480) * h * L * ‖yn2 - zn2‖ := by
    simpa [hJ_def] using h407139_norm
  have hK_bd : ‖K‖ ≤ (134472 / 60480) * h * L * ‖yn1 - zn1‖ := by
    simpa [hK_def] using h134472_norm
  have hR_bd : ‖R‖ ≤ (19087 / 60480) * h * L * ‖yn - zn‖ := by
    simpa [hR_def] using h19087_norm
  have hcalc :
      ‖A + B - C + D - G + J - K + R - τ‖
        ≤ ‖yn6 - zn6‖
          + (198721 / 60480) * h * L * ‖yn6 - zn6‖
          + (447288 / 60480) * h * L * ‖yn5 - zn5‖
          + (705549 / 60480) * h * L * ‖yn4 - zn4‖
          + (688256 / 60480) * h * L * ‖yn3 - zn3‖
          + (407139 / 60480) * h * L * ‖yn2 - zn2‖
          + (134472 / 60480) * h * L * ‖yn1 - zn1‖
          + (19087 / 60480) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    have hA_norm : ‖A‖ = ‖yn6 - zn6‖ := by rw [hA_def]
    linarith [htri, hA_norm, hB_bd, hC_bd, hD_bd, hG_bd, hJ_bd, hK_bd, hR_bd]
  calc
    ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - zn7‖
        = ‖A + B - C + D - G + J - K + R - τ‖ := by
          rw [halg, hA_def, hB_def, hC_def, hD_def, hG_def, hJ_def, hK_def, hR_def]
    _ ≤ ‖yn6 - zn6‖
          + (198721 / 60480) * h * L * ‖yn6 - zn6‖
          + (447288 / 60480) * h * L * ‖yn5 - zn5‖
          + (705549 / 60480) * h * L * ‖yn4 - zn4‖
          + (688256 / 60480) * h * L * ‖yn3 - zn3‖
          + (407139 / 60480) * h * L * ‖yn2 - zn2‖
          + (134472 / 60480) * h * L * ‖yn1 - zn1‖
          + (19087 / 60480) * h * L * ‖yn - zn‖
          + ‖τ‖ := hcalc

theorem ab7Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max
          ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1)
              - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2)
              - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3)
              - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4)
              - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5)
              - y (t₀ + ((n : ℝ) + 5) * h)‖)
          ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
              - y (t₀ + ((n : ℝ) + 6) * h)‖)
        ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7)
            - y (t₀ + ((n : ℝ) + 7) * h)‖
      ≤ (1 + h * ((40633 / 945) * L))
            * max (max (max (max (max (max
                  ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n
                      - y (t₀ + (n : ℝ) * h)‖
                  ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)‖)
                  ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)‖)
                  ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)‖)
                  ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)‖)
                  ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5)
                      - y (t₀ + ((n : ℝ) + 5) * h)‖)
                  ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
                      - y (t₀ + ((n : ℝ) + 6) * h)‖
        + ‖ab7VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n - y (t₀ + (n : ℝ) * h)‖
    with hen_def
  set en1 : ℝ :=
    ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
    with hen1_def
  set en2 : ℝ :=
    ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
    with hen2_def
  set en3 : ℝ :=
    ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
    with hen3_def
  set en4 : ℝ :=
    ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖
    with hen4_def
  set en5 : ℝ :=
    ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
    with hen5_def
  set en6 : ℝ :=
    ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
    with hen6_def
  set en7 : ℝ :=
    ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
    with hen7_def
  set τabs : ℝ :=
    ‖ab7VecResidual h (t₀ + (n : ℝ) * h) y‖
    with hτabs_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hen4_nn : 0 ≤ en4 := norm_nonneg _
  have hen5_nn : 0 ≤ en5 := norm_nonneg _
  have hen6_nn : 0 ≤ en6 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  -- One-step Lipschitz bound (from `ab7Vec_one_step_lipschitz`).
  have hstep :
      en7 ≤ en6 + (198721 / 60480) * h * L * en6
                + (447288 / 60480) * h * L * en5
                + (705549 / 60480) * h * L * en4
                + (688256 / 60480) * h * L * en3
                + (407139 / 60480) * h * L * en2
                + (134472 / 60480) * h * L * en1
                + (19087 / 60480) * h * L * en + τabs := by
    have := ab7Vec_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y hyf n
    show ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
        ≤ ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
          + (198721 / 60480) * h * L
              * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
                  - y (t₀ + ((n : ℝ) + 6) * h)‖
          + (447288 / 60480) * h * L
              * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5)
                  - y (t₀ + ((n : ℝ) + 5) * h)‖
          + (705549 / 60480) * h * L
              * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)‖
          + (688256 / 60480) * h * L
              * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)‖
          + (407139 / 60480) * h * L
              * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)‖
          + (134472 / 60480) * h * L
              * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)‖
          + (19087 / 60480) * h * L
              * ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n - y (t₀ + (n : ℝ) * h)‖
          + ‖ab7VecResidual h (t₀ + (n : ℝ) * h) y‖
    exact this
  set EN_n : ℝ := max (max (max (max (max (max en en1) en2) en3) en4) en5) en6
    with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen5_le_EN : en5 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen6_le_EN : en6 ≤ EN_n := le_max_right _ _
  have h198721_nn : 0 ≤ (198721 / 60480) * h * L := by positivity
  have h447288_nn : 0 ≤ (447288 / 60480) * h * L := by positivity
  have h705549_nn : 0 ≤ (705549 / 60480) * h * L := by positivity
  have h688256_nn : 0 ≤ (688256 / 60480) * h * L := by positivity
  have h407139_nn : 0 ≤ (407139 / 60480) * h * L := by positivity
  have h134472_nn : 0 ≤ (134472 / 60480) * h * L := by positivity
  have h19087_nn : 0 ≤ (19087 / 60480) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((40633 / 945) * L) := by positivity
  have hen7_bd : en7 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    have h1 : (198721 / 60480) * h * L * en6 ≤ (198721 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen6_le_EN h198721_nn
    have h2 : (447288 / 60480) * h * L * en5 ≤ (447288 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen5_le_EN h447288_nn
    have h3 : (705549 / 60480) * h * L * en4 ≤ (705549 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN h705549_nn
    have h4 : (688256 / 60480) * h * L * en3 ≤ (688256 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN h688256_nn
    have h5 : (407139 / 60480) * h * L * en2 ≤ (407139 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h407139_nn
    have h6 : (134472 / 60480) * h * L * en1 ≤ (134472 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h134472_nn
    have h7 : (19087 / 60480) * h * L * en ≤ (19087 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h19087_nn
    have h_alg :
        EN_n + (198721 / 60480) * h * L * EN_n
              + (447288 / 60480) * h * L * EN_n
              + (705549 / 60480) * h * L * EN_n
              + (688256 / 60480) * h * L * EN_n
              + (407139 / 60480) * h * L * EN_n
              + (134472 / 60480) * h * L * EN_n
              + (19087 / 60480) * h * L * EN_n + τabs
          = (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen6_le_EN, h1, h2, h3, h4, h5, h6, h7, h_alg.le]
  have hEN_le_grow : EN_n ≤ (1 + h * ((40633 / 945) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((40633 / 945) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  have hen5_bd : en5 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen5_le_EN, hEN_le_grow]
  have hen6_bd : en6 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen6_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd)
    hen4_bd) hen5_bd) hen6_bd) hen7_bd

theorem iteratedDeriv_eight_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 8 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 8 y t‖ ≤ M := by
  have h_cont : Continuous (iteratedDeriv 8 y) :=
    hy.continuous_iteratedDeriv 8 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

theorem y_eighth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 8 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 8 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖y (t + r) - y t - r • deriv y t
        - (r ^ 2 / 2) • iteratedDeriv 2 y t
        - (r ^ 3 / 6) • iteratedDeriv 3 y t
        - (r ^ 4 / 24) • iteratedDeriv 4 y t
        - (r ^ 5 / 120) • iteratedDeriv 5 y t
        - (r ^ 6 / 720) • iteratedDeriv 6 y t
        - (r ^ 7 / 5040) • iteratedDeriv 7 y t‖
      ≤ M / 40320 * r ^ 8 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htr_le : t ≤ t + r := by linarith
  have h_dy_bound :
      ∀ s ∈ Set.Icc t (t + r),
        ‖deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
            - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
            - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
            - ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
            - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t
            - ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t‖
          ≤ M / 5040 * (s - t) ^ 7 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have hdy : ContDiff ℝ 7 (deriv y) := hy.deriv'
    have hbnd_d :
        ∀ u ∈ Set.Icc a b, ‖iteratedDeriv 7 (deriv y) u‖ ≤ M := by
      intro u hu
      have hidd_eq : iteratedDeriv 7 (deriv y) = iteratedDeriv 8 y := by
        have : iteratedDeriv 8 y = iteratedDeriv 7 (deriv y) :=
          iteratedDeriv_succ' (n := 7) (f := y)
        exact this.symm
      simpa [hidd_eq] using hbnd u hu
    have hrem :=
      y_seventh_order_taylor_remainder_vec hdy hbnd_d ht
        (by rw [hsplit]; exact hs_ab) hts
    have hderiv2 : deriv (deriv y) t = iteratedDeriv 2 y t := by
      rw [show iteratedDeriv 2 y = deriv (iteratedDeriv 1 y) from
          iteratedDeriv_succ, iteratedDeriv_one]
    have hiter2 : iteratedDeriv 2 (deriv y) t = iteratedDeriv 3 y t := by
      have : iteratedDeriv 3 y = iteratedDeriv 2 (deriv y) :=
        iteratedDeriv_succ' (n := 2) (f := y)
      rw [this]
    have hiter3 : iteratedDeriv 3 (deriv y) t = iteratedDeriv 4 y t := by
      have : iteratedDeriv 4 y = iteratedDeriv 3 (deriv y) :=
        iteratedDeriv_succ' (n := 3) (f := y)
      rw [this]
    have hiter4 : iteratedDeriv 4 (deriv y) t = iteratedDeriv 5 y t := by
      have : iteratedDeriv 5 y = iteratedDeriv 4 (deriv y) :=
        iteratedDeriv_succ' (n := 4) (f := y)
      rw [this]
    have hiter5 : iteratedDeriv 5 (deriv y) t = iteratedDeriv 6 y t := by
      have : iteratedDeriv 6 y = iteratedDeriv 5 (deriv y) :=
        iteratedDeriv_succ' (n := 5) (f := y)
      rw [this]
    have hiter6 : iteratedDeriv 6 (deriv y) t = iteratedDeriv 7 y t := by
      have : iteratedDeriv 7 y = iteratedDeriv 6 (deriv y) :=
        iteratedDeriv_succ' (n := 6) (f := y)
      rw [this]
    rw [hsplit] at hrem
    simpa [hderiv2, hiter2, hiter3, hiter4, hiter5, hiter6] using hrem
  have hdy_cont : Continuous (deriv y) := hy.continuous_deriv (by norm_num)
  have h_dy_int :
      IntervalIntegrable (fun s => deriv y s) MeasureTheory.volume t (t + r) :=
    hdy_cont.intervalIntegrable _ _
  have h_const_int :
      IntervalIntegrable (fun _ : ℝ => deriv y t)
        MeasureTheory.volume t (t + r) := intervalIntegrable_const
  have h_lin_int :
      IntervalIntegrable (fun s : ℝ => (s - t) • iteratedDeriv 2 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_quad_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_cubic_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_quartic_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_quintic_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_sextic_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_ftc_y :
      ∫ s in t..t + r, deriv y s = y (t + r) - y t := by
    have hderiv_at :
        ∀ x ∈ Set.uIcc t (t + r),
          HasDerivAt y (deriv y x) x := by
      intro x _hx
      exact (hy.differentiable (by norm_num) x).hasDerivAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_at h_dy_int
  have h_lin_eval :
      ∫ s in t..t + r, (s - t) • iteratedDeriv 2 y t
        = (r ^ 2 / 2) • iteratedDeriv 2 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_int_smul :
        ∫ s in t..t + r, (s - t) = r ^ 2 / 2 := by
      simp [intervalIntegral.integral_sub, integral_id,
        intervalIntegral.integral_const]
      ring
    rw [h_int_smul]
  have h_quad_eval :
      ∫ s in t..t + r, ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
        = (r ^ 3 / 6) • iteratedDeriv 3 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 2 = r ^ 3 / 3 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 2
            = ∫ s in (t - t)..(t + r - t), s ^ 2 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 2 / 2)
          = fun s : ℝ => (1 / 2 : ℝ) * (s - t) ^ 2 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 2 / 2 = r ^ 3 / 6 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_cubic_eval :
      ∫ s in t..t + r, ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
        = (r ^ 4 / 24) • iteratedDeriv 4 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 3 = r ^ 4 / 4 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 3
            = ∫ s in (t - t)..(t + r - t), s ^ 3 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 3) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 3 / 6)
          = fun s : ℝ => (1 / 6 : ℝ) * (s - t) ^ 3 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 3 / 6 = r ^ 4 / 24 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_quartic_eval :
      ∫ s in t..t + r, ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
        = (r ^ 5 / 120) • iteratedDeriv 5 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 4 = r ^ 5 / 5 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 4
            = ∫ s in (t - t)..(t + r - t), s ^ 4 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 4) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 4 / 24)
          = fun s : ℝ => (1 / 24 : ℝ) * (s - t) ^ 4 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 4 / 24 = r ^ 5 / 120 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_quintic_eval :
      ∫ s in t..t + r, ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t
        = (r ^ 6 / 720) • iteratedDeriv 6 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 5 = r ^ 6 / 6 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 5
            = ∫ s in (t - t)..(t + r - t), s ^ 5 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 5) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 5 / 120)
          = fun s : ℝ => (1 / 120 : ℝ) * (s - t) ^ 5 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 5 / 120 = r ^ 6 / 720 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_sextic_eval :
      ∫ s in t..t + r, ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t
        = (r ^ 7 / 5040) • iteratedDeriv 7 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 6 = r ^ 7 / 7 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 6
            = ∫ s in (t - t)..(t + r - t), s ^ 6 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 6) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 6 / 720)
          = fun s : ℝ => (1 / 720 : ℝ) * (s - t) ^ 6 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 6 / 720 = r ^ 7 / 5040 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_residual_integral :
      y (t + r) - y t - r • deriv y t
          - (r ^ 2 / 2) • iteratedDeriv 2 y t
          - (r ^ 3 / 6) • iteratedDeriv 3 y t
          - (r ^ 4 / 24) • iteratedDeriv 4 y t
          - (r ^ 5 / 120) • iteratedDeriv 5 y t
          - (r ^ 6 / 720) • iteratedDeriv 6 y t
          - (r ^ 7 / 5040) • iteratedDeriv 7 y t
        = ∫ s in t..t + r,
            (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
              - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
              - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
              - ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
              - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t
              - ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t) := by
    rw [intervalIntegral.integral_sub
        ((((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int).sub h_quintic_int) h_sextic_int,
      intervalIntegral.integral_sub
        (((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int) h_quintic_int,
      intervalIntegral.integral_sub
        ((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int) h_quartic_int,
      intervalIntegral.integral_sub
        (((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int) h_cubic_int,
      intervalIntegral.integral_sub
        ((h_dy_int.sub h_const_int).sub h_lin_int) h_quad_int,
      intervalIntegral.integral_sub (h_dy_int.sub h_const_int) h_lin_int,
      intervalIntegral.integral_sub h_dy_int h_const_int,
      h_ftc_y, h_lin_eval, h_quad_eval, h_cubic_eval, h_quartic_eval,
      h_quintic_eval, h_sextic_eval]
    have h_const_eval :
        ∫ _ in t..t + r, deriv y t = r • deriv y t := by
      rw [intervalIntegral.integral_const]
      simp
    rw [h_const_eval]
  have h_bound_integral :
      ‖∫ s in t..t + r,
          (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
            - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
            - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
            - ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
            - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t
            - ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t)‖
        ≤ ∫ s in t..t + r, M / 5040 * (s - t) ^ 7 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dy_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 5040 * (s - t) ^ 7).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 5040 * (s - t) ^ 7 = M / 40320 * r ^ 8 := by
    have h_inner : ∫ s in t..t + r, (s - t) ^ 7 = r ^ 8 / 8 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 7
            = ∫ s in (t - t)..(t + r - t), s ^ 7 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 7) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

theorem derivY_seventh_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 8 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 8 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖deriv y (t + r) - deriv y t - r • iteratedDeriv 2 y t
        - (r ^ 2 / 2) • iteratedDeriv 3 y t
        - (r ^ 3 / 6) • iteratedDeriv 4 y t
        - (r ^ 4 / 24) • iteratedDeriv 5 y t
        - (r ^ 5 / 120) • iteratedDeriv 6 y t
        - (r ^ 6 / 720) • iteratedDeriv 7 y t‖
      ≤ M / 5040 * r ^ 7 := by
  have hdy : ContDiff ℝ 7 (deriv y) := hy.deriv'
  have hbnd_d :
      ∀ s ∈ Set.Icc a b, ‖iteratedDeriv 7 (deriv y) s‖ ≤ M := by
    intro s hs
    have hidd_eq : iteratedDeriv 7 (deriv y) = iteratedDeriv 8 y := by
      have : iteratedDeriv 8 y = iteratedDeriv 7 (deriv y) :=
        iteratedDeriv_succ' (n := 7) (f := y)
      exact this.symm
    simpa [hidd_eq] using hbnd s hs
  have hrem := y_seventh_order_taylor_remainder_vec hdy hbnd_d ht htr hr
  have hderiv2 : deriv (deriv y) t = iteratedDeriv 2 y t := by
    rw [show iteratedDeriv 2 y = deriv (iteratedDeriv 1 y) from
        iteratedDeriv_succ, iteratedDeriv_one]
  have hiter2 : iteratedDeriv 2 (deriv y) t = iteratedDeriv 3 y t := by
    have : iteratedDeriv 3 y = iteratedDeriv 2 (deriv y) :=
      iteratedDeriv_succ' (n := 2) (f := y)
    rw [this]
  have hiter3 : iteratedDeriv 3 (deriv y) t = iteratedDeriv 4 y t := by
    have : iteratedDeriv 4 y = iteratedDeriv 3 (deriv y) :=
      iteratedDeriv_succ' (n := 3) (f := y)
    rw [this]
  have hiter4 : iteratedDeriv 4 (deriv y) t = iteratedDeriv 5 y t := by
    have : iteratedDeriv 5 y = iteratedDeriv 4 (deriv y) :=
      iteratedDeriv_succ' (n := 4) (f := y)
    rw [this]
  have hiter5 : iteratedDeriv 5 (deriv y) t = iteratedDeriv 6 y t := by
    have : iteratedDeriv 6 y = iteratedDeriv 5 (deriv y) :=
      iteratedDeriv_succ' (n := 5) (f := y)
    rw [this]
  have hiter6 : iteratedDeriv 6 (deriv y) t = iteratedDeriv 7 y t := by
    have : iteratedDeriv 7 y = iteratedDeriv 6 (deriv y) :=
      iteratedDeriv_succ' (n := 6) (f := y)
    rw [this]
  simpa [hderiv2, hiter2, hiter3, hiter4, hiter5, hiter6] using hrem

private lemma ab7Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y6 y7 d0 d1 d2 d3 d4 d5 d6 dd ddd dddd ddddd dddddd ddddddd : E)
    (h : ℝ) :
    y7 - y6 - h • ((198721 / 60480 : ℝ) • d6 - (447288 / 60480 : ℝ) • d5
                  + (705549 / 60480 : ℝ) • d4 - (688256 / 60480 : ℝ) • d3
                  + (407139 / 60480 : ℝ) • d2 - (134472 / 60480 : ℝ) • d1
                  + (19087 / 60480 : ℝ) • d0)
      = (y7 - y0 - (7 * h) • d0
            - ((7 * h) ^ 2 / 2) • dd
            - ((7 * h) ^ 3 / 6) • ddd
            - ((7 * h) ^ 4 / 24) • dddd
            - ((7 * h) ^ 5 / 120) • ddddd
            - ((7 * h) ^ 6 / 720) • dddddd
            - ((7 * h) ^ 7 / 5040) • ddddddd)
        - (y6 - y0 - (6 * h) • d0
            - ((6 * h) ^ 2 / 2) • dd
            - ((6 * h) ^ 3 / 6) • ddd
            - ((6 * h) ^ 4 / 24) • dddd
            - ((6 * h) ^ 5 / 120) • ddddd
            - ((6 * h) ^ 6 / 720) • dddddd
            - ((6 * h) ^ 7 / 5040) • ddddddd)
        - (198721 * h / 60480 : ℝ)
            • (d6 - d0 - (6 * h) • dd
                - ((6 * h) ^ 2 / 2) • ddd
                - ((6 * h) ^ 3 / 6) • dddd
                - ((6 * h) ^ 4 / 24) • ddddd
                - ((6 * h) ^ 5 / 120) • dddddd
                - ((6 * h) ^ 6 / 720) • ddddddd)
        + (447288 * h / 60480 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd
                - ((5 * h) ^ 6 / 720) • ddddddd)
        - (705549 * h / 60480 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd
                - ((4 * h) ^ 6 / 720) • ddddddd)
        + (688256 * h / 60480 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd
                - ((3 * h) ^ 6 / 720) • ddddddd)
        - (407139 * h / 60480 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd
                - ((2 * h) ^ 6 / 720) • ddddddd)
        + (134472 * h / 60480 : ℝ)
            • (d1 - d0 - h • dd
                - (h ^ 2 / 2) • ddd
                - (h ^ 3 / 6) • dddd
                - (h ^ 4 / 24) • ddddd
                - (h ^ 5 / 120) • dddddd
                - (h ^ 6 / 720) • ddddddd) := by
  simp only [smul_sub, smul_add, smul_smul]
  module

private lemma ab7Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 40320 * (7 * h) ^ 8 + M / 40320 * (6 * h) ^ 8
      + (198721 * h / 60480) * (M / 5040 * (6 * h) ^ 7)
      + (447288 * h / 60480) * (M / 5040 * (5 * h) ^ 7)
      + (705549 * h / 60480) * (M / 5040 * (4 * h) ^ 7)
      + (688256 * h / 60480) * (M / 5040 * (3 * h) ^ 7)
      + (407139 * h / 60480) * (M / 5040 * (2 * h) ^ 7)
      + (134472 * h / 60480) * (M / 5040 * h ^ 7)
      = (159970508328 / 304819200 : ℝ) * M * h ^ 8 := by
  ring

private lemma ab7Vec_residual_eight_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D G J K R : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (198721 * h / 60480 : ℝ) • C + (447288 * h / 60480 : ℝ) • D
        - (705549 * h / 60480 : ℝ) • G + (688256 * h / 60480 : ℝ) • J
        - (407139 * h / 60480 : ℝ) • K + (134472 * h / 60480 : ℝ) • R‖
      ≤ ‖A‖ + ‖B‖ + (198721 * h / 60480) * ‖C‖
          + (447288 * h / 60480) * ‖D‖ + (705549 * h / 60480) * ‖G‖
          + (688256 * h / 60480) * ‖J‖ + (407139 * h / 60480) * ‖K‖
          + (134472 * h / 60480) * ‖R‖ := by
  have h198721h_nn : 0 ≤ (198721 * h / 60480 : ℝ) := by linarith
  have h447288h_nn : 0 ≤ (447288 * h / 60480 : ℝ) := by linarith
  have h705549h_nn : 0 ≤ (705549 * h / 60480 : ℝ) := by linarith
  have h688256h_nn : 0 ≤ (688256 * h / 60480 : ℝ) := by linarith
  have h407139h_nn : 0 ≤ (407139 * h / 60480 : ℝ) := by linarith
  have h134472h_nn : 0 ≤ (134472 * h / 60480 : ℝ) := by linarith
  have hC_norm :
      ‖(198721 * h / 60480 : ℝ) • C‖ = (198721 * h / 60480) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg h198721h_nn]
  have hD_norm :
      ‖(447288 * h / 60480 : ℝ) • D‖ = (447288 * h / 60480) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg h447288h_nn]
  have hG_norm :
      ‖(705549 * h / 60480 : ℝ) • G‖ = (705549 * h / 60480) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg h705549h_nn]
  have hJ_norm :
      ‖(688256 * h / 60480 : ℝ) • J‖ = (688256 * h / 60480) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg h688256h_nn]
  have hK_norm :
      ‖(407139 * h / 60480 : ℝ) • K‖ = (407139 * h / 60480) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg h407139h_nn]
  have hR_norm :
      ‖(134472 * h / 60480 : ℝ) • R‖ = (134472 * h / 60480) * ‖R‖ := by
    rw [norm_smul, Real.norm_of_nonneg h134472h_nn]
  have h1 : ‖A - B - (198721 * h / 60480 : ℝ) • C
                + (447288 * h / 60480 : ℝ) • D
                - (705549 * h / 60480 : ℝ) • G
                + (688256 * h / 60480 : ℝ) • J
                - (407139 * h / 60480 : ℝ) • K
                + (134472 * h / 60480 : ℝ) • R‖
      ≤ ‖A - B - (198721 * h / 60480 : ℝ) • C
            + (447288 * h / 60480 : ℝ) • D
            - (705549 * h / 60480 : ℝ) • G
            + (688256 * h / 60480 : ℝ) • J
            - (407139 * h / 60480 : ℝ) • K‖
        + ‖(134472 * h / 60480 : ℝ) • R‖ := norm_add_le _ _
  have h2 : ‖A - B - (198721 * h / 60480 : ℝ) • C
                + (447288 * h / 60480 : ℝ) • D
                - (705549 * h / 60480 : ℝ) • G
                + (688256 * h / 60480 : ℝ) • J
                - (407139 * h / 60480 : ℝ) • K‖
      ≤ ‖A - B - (198721 * h / 60480 : ℝ) • C
            + (447288 * h / 60480 : ℝ) • D
            - (705549 * h / 60480 : ℝ) • G
            + (688256 * h / 60480 : ℝ) • J‖
        + ‖(407139 * h / 60480 : ℝ) • K‖ := norm_sub_le _ _
  have h3 : ‖A - B - (198721 * h / 60480 : ℝ) • C
                + (447288 * h / 60480 : ℝ) • D
                - (705549 * h / 60480 : ℝ) • G
                + (688256 * h / 60480 : ℝ) • J‖
      ≤ ‖A - B - (198721 * h / 60480 : ℝ) • C
            + (447288 * h / 60480 : ℝ) • D
            - (705549 * h / 60480 : ℝ) • G‖
        + ‖(688256 * h / 60480 : ℝ) • J‖ := norm_add_le _ _
  have h4 : ‖A - B - (198721 * h / 60480 : ℝ) • C
                + (447288 * h / 60480 : ℝ) • D
                - (705549 * h / 60480 : ℝ) • G‖
      ≤ ‖A - B - (198721 * h / 60480 : ℝ) • C
            + (447288 * h / 60480 : ℝ) • D‖
        + ‖(705549 * h / 60480 : ℝ) • G‖ := norm_sub_le _ _
  have h5 : ‖A - B - (198721 * h / 60480 : ℝ) • C
                + (447288 * h / 60480 : ℝ) • D‖
      ≤ ‖A - B - (198721 * h / 60480 : ℝ) • C‖
        + ‖(447288 * h / 60480 : ℝ) • D‖ := norm_add_le _ _
  have h6 : ‖A - B - (198721 * h / 60480 : ℝ) • C‖
      ≤ ‖A - B‖ + ‖(198721 * h / 60480 : ℝ) • C‖ := norm_sub_le _ _
  have h7 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith [hC_norm.le, hC_norm.ge, hD_norm.le, hD_norm.ge,
    hG_norm.le, hG_norm.ge, hJ_norm.le, hJ_norm.ge, hK_norm.le, hK_norm.ge,
    hR_norm.le, hR_norm.ge]

private theorem ab7Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 8 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 8 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 7 * h) - y (t + 6 * h)
        - h • ((198721 / 60480 : ℝ) • deriv y (t + 6 * h)
              - (447288 / 60480 : ℝ) • deriv y (t + 5 * h)
              + (705549 / 60480 : ℝ) • deriv y (t + 4 * h)
              - (688256 / 60480 : ℝ) • deriv y (t + 3 * h)
              + (407139 / 60480 : ℝ) • deriv y (t + 2 * h)
              - (134472 / 60480 : ℝ) • deriv y (t + h)
              + (19087 / 60480 : ℝ) • deriv y t)‖
      ≤ (525 : ℝ) * M * h ^ 8 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have hRy6 :=
    y_eighth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRy7 :=
    y_eighth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRyp1 :=
    derivY_seventh_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_seventh_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_seventh_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_seventh_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_seventh_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_seventh_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  set y0 : E := y t with hy0_def
  set y6 : E := y (t + 6 * h) with hy6_def
  set y7 : E := y (t + 7 * h) with hy7_def
  set d0 : E := deriv y t with hd0_def
  set d1 : E := deriv y (t + h) with hd1_def
  set d2 : E := deriv y (t + 2 * h) with hd2_def
  set d3 : E := deriv y (t + 3 * h) with hd3_def
  set d4 : E := deriv y (t + 4 * h) with hd4_def
  set d5 : E := deriv y (t + 5 * h) with hd5_def
  set d6 : E := deriv y (t + 6 * h) with hd6_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  set ddddd : E := iteratedDeriv 5 y t with hddddd_def
  set dddddd : E := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd : E := iteratedDeriv 7 y t with hddddddd_def
  clear_value y0 y6 y7 d0 d1 d2 d3 d4 d5 d6 dd ddd dddd ddddd dddddd ddddddd
  have hLTE_eq :
      y7 - y6 - h • ((198721 / 60480 : ℝ) • d6 - (447288 / 60480 : ℝ) • d5
                    + (705549 / 60480 : ℝ) • d4 - (688256 / 60480 : ℝ) • d3
                    + (407139 / 60480 : ℝ) • d2 - (134472 / 60480 : ℝ) • d1
                    + (19087 / 60480 : ℝ) • d0)
        = (y7 - y0 - (7 * h) • d0
              - ((7 * h) ^ 2 / 2) • dd
              - ((7 * h) ^ 3 / 6) • ddd
              - ((7 * h) ^ 4 / 24) • dddd
              - ((7 * h) ^ 5 / 120) • ddddd
              - ((7 * h) ^ 6 / 720) • dddddd
              - ((7 * h) ^ 7 / 5040) • ddddddd)
          - (y6 - y0 - (6 * h) • d0
              - ((6 * h) ^ 2 / 2) • dd
              - ((6 * h) ^ 3 / 6) • ddd
              - ((6 * h) ^ 4 / 24) • dddd
              - ((6 * h) ^ 5 / 120) • ddddd
              - ((6 * h) ^ 6 / 720) • dddddd
              - ((6 * h) ^ 7 / 5040) • ddddddd)
          - (198721 * h / 60480 : ℝ)
              • (d6 - d0 - (6 * h) • dd
                  - ((6 * h) ^ 2 / 2) • ddd
                  - ((6 * h) ^ 3 / 6) • dddd
                  - ((6 * h) ^ 4 / 24) • ddddd
                  - ((6 * h) ^ 5 / 120) • dddddd
                  - ((6 * h) ^ 6 / 720) • ddddddd)
          + (447288 * h / 60480 : ℝ)
              • (d5 - d0 - (5 * h) • dd
                  - ((5 * h) ^ 2 / 2) • ddd
                  - ((5 * h) ^ 3 / 6) • dddd
                  - ((5 * h) ^ 4 / 24) • ddddd
                  - ((5 * h) ^ 5 / 120) • dddddd
                  - ((5 * h) ^ 6 / 720) • ddddddd)
          - (705549 * h / 60480 : ℝ)
              • (d4 - d0 - (4 * h) • dd
                  - ((4 * h) ^ 2 / 2) • ddd
                  - ((4 * h) ^ 3 / 6) • dddd
                  - ((4 * h) ^ 4 / 24) • ddddd
                  - ((4 * h) ^ 5 / 120) • dddddd
                  - ((4 * h) ^ 6 / 720) • ddddddd)
          + (688256 * h / 60480 : ℝ)
              • (d3 - d0 - (3 * h) • dd
                  - ((3 * h) ^ 2 / 2) • ddd
                  - ((3 * h) ^ 3 / 6) • dddd
                  - ((3 * h) ^ 4 / 24) • ddddd
                  - ((3 * h) ^ 5 / 120) • dddddd
                  - ((3 * h) ^ 6 / 720) • ddddddd)
          - (407139 * h / 60480 : ℝ)
              • (d2 - d0 - (2 * h) • dd
                  - ((2 * h) ^ 2 / 2) • ddd
                  - ((2 * h) ^ 3 / 6) • dddd
                  - ((2 * h) ^ 4 / 24) • ddddd
                  - ((2 * h) ^ 5 / 120) • dddddd
                  - ((2 * h) ^ 6 / 720) • ddddddd)
          + (134472 * h / 60480 : ℝ)
              • (d1 - d0 - h • dd
                  - (h ^ 2 / 2) • ddd
                  - (h ^ 3 / 6) • dddd
                  - (h ^ 4 / 24) • ddddd
                  - (h ^ 5 / 120) • dddddd
                  - (h ^ 6 / 720) • ddddddd) :=
    ab7Vec_residual_alg_identity y0 y6 y7 d0 d1 d2 d3 d4 d5 d6
      dd ddd dddd ddddd dddddd ddddddd h
  rw [hLTE_eq]
  set A : E := y7 - y0 - (7 * h) • d0
            - ((7 * h) ^ 2 / 2) • dd
            - ((7 * h) ^ 3 / 6) • ddd
            - ((7 * h) ^ 4 / 24) • dddd
            - ((7 * h) ^ 5 / 120) • ddddd
            - ((7 * h) ^ 6 / 720) • dddddd
            - ((7 * h) ^ 7 / 5040) • ddddddd with hA_def
  set B : E := y6 - y0 - (6 * h) • d0
            - ((6 * h) ^ 2 / 2) • dd
            - ((6 * h) ^ 3 / 6) • ddd
            - ((6 * h) ^ 4 / 24) • dddd
            - ((6 * h) ^ 5 / 120) • ddddd
            - ((6 * h) ^ 6 / 720) • dddddd
            - ((6 * h) ^ 7 / 5040) • ddddddd with hB_def
  set C : E := d6 - d0 - (6 * h) • dd
            - ((6 * h) ^ 2 / 2) • ddd
            - ((6 * h) ^ 3 / 6) • dddd
            - ((6 * h) ^ 4 / 24) • ddddd
            - ((6 * h) ^ 5 / 120) • dddddd
            - ((6 * h) ^ 6 / 720) • ddddddd with hC_def
  set D : E := d5 - d0 - (5 * h) • dd
            - ((5 * h) ^ 2 / 2) • ddd
            - ((5 * h) ^ 3 / 6) • dddd
            - ((5 * h) ^ 4 / 24) • ddddd
            - ((5 * h) ^ 5 / 120) • dddddd
            - ((5 * h) ^ 6 / 720) • ddddddd with hD_def
  set G : E := d4 - d0 - (4 * h) • dd
            - ((4 * h) ^ 2 / 2) • ddd
            - ((4 * h) ^ 3 / 6) • dddd
            - ((4 * h) ^ 4 / 24) • ddddd
            - ((4 * h) ^ 5 / 120) • dddddd
            - ((4 * h) ^ 6 / 720) • ddddddd with hG_def
  set J : E := d3 - d0 - (3 * h) • dd
            - ((3 * h) ^ 2 / 2) • ddd
            - ((3 * h) ^ 3 / 6) • dddd
            - ((3 * h) ^ 4 / 24) • ddddd
            - ((3 * h) ^ 5 / 120) • dddddd
            - ((3 * h) ^ 6 / 720) • ddddddd with hJ_def
  set K : E := d2 - d0 - (2 * h) • dd
            - ((2 * h) ^ 2 / 2) • ddd
            - ((2 * h) ^ 3 / 6) • dddd
            - ((2 * h) ^ 4 / 24) • ddddd
            - ((2 * h) ^ 5 / 120) • dddddd
            - ((2 * h) ^ 6 / 720) • ddddddd with hK_def
  set R : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd
            - (h ^ 4 / 24) • ddddd
            - (h ^ 5 / 120) • dddddd
            - (h ^ 6 / 720) • ddddddd with hR_def
  clear_value A B C D G J K R
  have h198721h_nn : 0 ≤ 198721 * h / 60480 := by linarith
  have h447288h_nn : 0 ≤ 447288 * h / 60480 := by linarith
  have h705549h_nn : 0 ≤ 705549 * h / 60480 := by linarith
  have h688256h_nn : 0 ≤ 688256 * h / 60480 := by linarith
  have h407139h_nn : 0 ≤ 407139 * h / 60480 := by linarith
  have h134472h_nn : 0 ≤ 134472 * h / 60480 := by linarith
  have htri := ab7Vec_residual_eight_term_triangle A B C D G J K R h hh
  have hA_bd : ‖A‖ ≤ M / 40320 * (7 * h) ^ 8 := hRy7
  have hB_bd : ‖B‖ ≤ M / 40320 * (6 * h) ^ 8 := hRy6
  have hC_bd : ‖C‖ ≤ M / 5040 * (6 * h) ^ 7 := hRyp6
  have hD_bd : ‖D‖ ≤ M / 5040 * (5 * h) ^ 7 := hRyp5
  have hG_bd : ‖G‖ ≤ M / 5040 * (4 * h) ^ 7 := hRyp4
  have hJ_bd : ‖J‖ ≤ M / 5040 * (3 * h) ^ 7 := hRyp3
  have hK_bd : ‖K‖ ≤ M / 5040 * (2 * h) ^ 7 := hRyp2
  have hR_bd : ‖R‖ ≤ M / 5040 * h ^ 7 := hRyp1
  have h198721C_bd : (198721 * h / 60480) * ‖C‖
      ≤ (198721 * h / 60480) * (M / 5040 * (6 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hC_bd h198721h_nn
  have h447288D_bd : (447288 * h / 60480) * ‖D‖
      ≤ (447288 * h / 60480) * (M / 5040 * (5 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hD_bd h447288h_nn
  have h705549G_bd : (705549 * h / 60480) * ‖G‖
      ≤ (705549 * h / 60480) * (M / 5040 * (4 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hG_bd h705549h_nn
  have h688256J_bd : (688256 * h / 60480) * ‖J‖
      ≤ (688256 * h / 60480) * (M / 5040 * (3 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hJ_bd h688256h_nn
  have h407139K_bd : (407139 * h / 60480) * ‖K‖
      ≤ (407139 * h / 60480) * (M / 5040 * (2 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hK_bd h407139h_nn
  have h134472R_bd : (134472 * h / 60480) * ‖R‖
      ≤ (134472 * h / 60480) * (M / 5040 * h ^ 7) :=
    mul_le_mul_of_nonneg_left hR_bd h134472h_nn
  have hbound_alg :
      M / 40320 * (7 * h) ^ 8 + M / 40320 * (6 * h) ^ 8
        + (198721 * h / 60480) * (M / 5040 * (6 * h) ^ 7)
        + (447288 * h / 60480) * (M / 5040 * (5 * h) ^ 7)
        + (705549 * h / 60480) * (M / 5040 * (4 * h) ^ 7)
        + (688256 * h / 60480) * (M / 5040 * (3 * h) ^ 7)
        + (407139 * h / 60480) * (M / 5040 * (2 * h) ^ 7)
        + (134472 * h / 60480) * (M / 5040 * h ^ 7)
        = (159970508328 / 304819200 : ℝ) * M * h ^ 8 :=
    ab7Vec_residual_bound_alg_identity M h
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  have hh8_nn : 0 ≤ h ^ 8 := by positivity
  have hMh8_nn : 0 ≤ M * h ^ 8 := mul_nonneg hMnn hh8_nn
  have hslack : (159970508328 / 304819200 : ℝ) * M * h ^ 8 ≤ 525 * M * h ^ 8 := by
    rw [mul_assoc, mul_assoc (525 : ℝ)]
    have hle : (159970508328 / 304819200 : ℝ) ≤ 525 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh8_nn
  calc
    ‖A - B - (198721 * h / 60480 : ℝ) • C
          + (447288 * h / 60480 : ℝ) • D
          - (705549 * h / 60480 : ℝ) • G
          + (688256 * h / 60480 : ℝ) • J
          - (407139 * h / 60480 : ℝ) • K
          + (134472 * h / 60480 : ℝ) • R‖
      ≤ ‖A‖ + ‖B‖ + (198721 * h / 60480) * ‖C‖
          + (447288 * h / 60480) * ‖D‖ + (705549 * h / 60480) * ‖G‖
          + (688256 * h / 60480) * ‖J‖ + (407139 * h / 60480) * ‖K‖
          + (134472 * h / 60480) * ‖R‖ := htri
    _ ≤ M / 40320 * (7 * h) ^ 8 + M / 40320 * (6 * h) ^ 8
          + (198721 * h / 60480) * (M / 5040 * (6 * h) ^ 7)
          + (447288 * h / 60480) * (M / 5040 * (5 * h) ^ 7)
          + (705549 * h / 60480) * (M / 5040 * (4 * h) ^ 7)
          + (688256 * h / 60480) * (M / 5040 * (3 * h) ^ 7)
          + (407139 * h / 60480) * (M / 5040 * (2 * h) ^ 7)
          + (134472 * h / 60480) * (M / 5040 * h ^ 7) := by
        linarith [hA_bd, hB_bd, h198721C_bd, h447288D_bd, h705549G_bd,
          h688256J_bd, h407139K_bd, h134472R_bd]
    _ = (159970508328 / 304819200 : ℝ) * M * h ^ 8 := hbound_alg
    _ ≤ 525 * M * h ^ 8 := hslack

theorem ab7Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 8 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 7) * h ≤ T →
        ‖ab7VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 8 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_eight_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(525 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 7) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h = ((n : ℝ) + 7) * h := by ring
    linarith
  show ‖ab7VecResidual h t y‖ ≤ 525 * M * h ^ 8
  unfold ab7VecResidual
  exact ab7Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem hh.le

lemma ab7IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E) (n : ℕ) :
    ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n
      = abIterVec 7 ab7GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅, y₆] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 0 = _
      rw [ab7IterVec_zero]
      unfold abIterVec
      simp
    | 1 =>
      show ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 1 = _
      rw [ab7IterVec_one]
      unfold abIterVec
      simp
    | 2 =>
      show ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 2 = _
      rw [ab7IterVec_two]
      unfold abIterVec
      simp
    | 3 =>
      show ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 3 = _
      rw [ab7IterVec_three]
      unfold abIterVec
      simp
    | 4 =>
      show ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 4 = _
      rw [ab7IterVec_four]
      unfold abIterVec
      simp
    | 5 =>
      show ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 5 = _
      rw [ab7IterVec_five]
      unfold abIterVec
      simp
    | 6 =>
      show ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 6 = _
      rw [ab7IterVec_six]
      unfold abIterVec
      simp
    | k + 7 =>
      rw [ab7IterVec_succ_seven]
      rw [abIterVec_step (s := 7) (by norm_num)
          ab7GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅, y₆] k]
      rw [show (k + 7 - 1 : ℕ) = k + 6 from by omega]
      rw [Fin.sum_univ_seven]
      have hval3 : ((3 : Fin 7) : ℕ) = 3 := rfl
      have hval4 : ((4 : Fin 7) : ℕ) = 4 := rfl
      have hval5 : ((5 : Fin 7) : ℕ) = 5 := rfl
      have hval6 : ((6 : Fin 7) : ℕ) = 6 := rfl
      simp only [ab7GenericCoeff_zero, ab7GenericCoeff_one, ab7GenericCoeff_two,
        ab7GenericCoeff_three, ab7GenericCoeff_four, ab7GenericCoeff_five,
        ab7GenericCoeff_six,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5, hval6,
        Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega), ← ih (k + 4) (by omega),
        ← ih (k + 5) (by omega), ← ih (k + 6) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring,
        show ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 by push_cast; ring,
        show ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring,
        show ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 by push_cast; ring]
      rw [show (-(134472 : ℝ) / 60480) •
              f (t₀ + ((k : ℝ) + 1) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (k + 1))
            = -((134472 / 60480 : ℝ) •
              f (t₀ + ((k : ℝ) + 1) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (k + 1))) by
        rw [show (-(134472 : ℝ) / 60480) = -(134472 / 60480 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(688256 : ℝ) / 60480) •
              f (t₀ + ((k : ℝ) + 3) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (k + 3))
            = -((688256 / 60480 : ℝ) •
              f (t₀ + ((k : ℝ) + 3) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (k + 3))) by
        rw [show (-(688256 : ℝ) / 60480) = -(688256 / 60480 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(447288 : ℝ) / 60480) •
              f (t₀ + ((k : ℝ) + 5) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (k + 5))
            = -((447288 / 60480 : ℝ) •
              f (t₀ + ((k : ℝ) + 5) * h)
                (ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (k + 5))) by
        rw [show (-(447288 : ℝ) / 60480) = -(447288 / 60480 : ℝ) by ring]
        exact neg_smul _ _]
      abel_nf

lemma ab7VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab7VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 7 ab7GenericCoeff h y t₀ n := by
  unfold ab7VecResidual abResidualVec
  rw [Fin.sum_univ_seven, ab7GenericCoeff_zero, ab7GenericCoeff_one,
    ab7GenericCoeff_two, ab7GenericCoeff_three, ab7GenericCoeff_four,
    ab7GenericCoeff_five, ab7GenericCoeff_six]
  have eA : t₀ + (n : ℝ) * h + 7 * h = t₀ + ((n + 7 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 6 * h = t₀ + ((n + 7 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 7 - 1 : ℕ) = n + 6 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 7) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 7) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 7) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 7) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI]
  rw [show (-(134472 : ℝ) / 60480) • deriv y (t₀ + (n : ℝ) * h + h)
        = -((134472 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h)) by
    rw [show (-(134472 : ℝ) / 60480) = -(134472 / 60480 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(688256 : ℝ) / 60480) • deriv y (t₀ + (n : ℝ) * h + 3 * h)
        = -((688256 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h)) by
    rw [show (-(688256 : ℝ) / 60480) = -(688256 / 60480 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(447288 : ℝ) / 60480) • deriv y (t₀ + (n : ℝ) * h + 5 * h)
        = -((447288 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 5 * h)) by
    rw [show (-(447288 : ℝ) / 60480) = -(447288 / 60480 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (198721 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 6 * h)
        - (447288 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 5 * h)
        + (705549 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 4 * h)
        - (688256 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h)
        + (407139 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
        - (134472 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h)
        + (19087 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h)
        = (19087 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h)
          + -((134472 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h))
          + (407139 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
          + -((688256 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h))
          + (705549 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 4 * h)
          + -((447288 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 5 * h))
          + (198721 / 60480 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 6 * h) by abel_nf]

theorem ab7Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 8 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
      ‖y₀ - y t₀‖ ≤ ε₀ → ‖y₁ - y (t₀ + h)‖ ≤ ε₀ →
      ‖y₂ - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖y₃ - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖y₄ - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖y₅ - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖y₆ - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 6) * h ≤ T →
      ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((40633 / 945) * L * T) * ε₀ + K * h ^ 7 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab7Vec_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((40633 / 945) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd N hNh
  set α : Fin 7 → ℝ := ab7GenericCoeff with hα_def
  set y₀_sept : Fin 7 → E := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆] with hy_sept_def
  have hs : (1 : ℕ) ≤ 7 := by norm_num
  haveI : Nonempty (Fin 7) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIterVec 7 α h f t₀ y₀_sept 0 = y₀ := by
    unfold abIterVec
    simp [hy_sept_def]
  have hiter1 : abIterVec 7 α h f t₀ y₀_sept 1 = y₁ := by
    unfold abIterVec
    simp [hy_sept_def]
  have hiter2 : abIterVec 7 α h f t₀ y₀_sept 2 = y₂ := by
    unfold abIterVec
    simp [hy_sept_def]
  have hiter3 : abIterVec 7 α h f t₀ y₀_sept 3 = y₃ := by
    unfold abIterVec
    simp [hy_sept_def]
  have hiter4 : abIterVec 7 α h f t₀ y₀_sept 4 = y₄ := by
    unfold abIterVec
    simp [hy_sept_def]
  have hiter5 : abIterVec 7 α h f t₀ y₀_sept 5 = y₅ := by
    unfold abIterVec
    simp [hy_sept_def]
  have hiter6 : abIterVec 7 α h f t₀ y₀_sept 6 = y₆ := by
    unfold abIterVec
    simp [hy_sept_def]
  have hstart : abErrWindowVec hs α h f t₀ y₀_sept y 0 ≤ ε₀ := by
    unfold abErrWindowVec
    apply Finset.sup'_le
    intro j _
    show abErrVec 7 α h f t₀ y₀_sept y (0 + (j : ℕ)) ≤ ε₀
    unfold abErrVec
    fin_cases j
    · show ‖abIterVec 7 α h f t₀ y₀_sept 0
          - y (t₀ + ((0 + (((0 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]
      exact he0_bd
    · show ‖abIterVec 7 α h f t₀ y₀_sept 1
          - y (t₀ + ((0 + (((1 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]
      exact he1_bd
    · show ‖abIterVec 7 α h f t₀ y₀_sept 2
          - y (t₀ + ((0 + (((2 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]
      exact he2_bd
    · show ‖abIterVec 7 α h f t₀ y₀_sept 3
          - y (t₀ + ((0 + (((3 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 7) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]
      exact he3_bd
    · show ‖abIterVec 7 α h f t₀ y₀_sept 4
          - y (t₀ + ((0 + (((4 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter4]
      have hval4 : ((4 : Fin 7) : ℕ) = 4 := rfl
      have : ((0 + (((4 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval4]; push_cast; ring
      rw [this]
      exact he4_bd
    · show ‖abIterVec 7 α h f t₀ y₀_sept 5
          - y (t₀ + ((0 + (((5 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter5]
      have hval5 : ((5 : Fin 7) : ℕ) = 5 := rfl
      have : ((0 + (((5 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval5]; push_cast; ring
      rw [this]
      exact he5_bd
    · show ‖abIterVec 7 α h f t₀ y₀_sept 6
          - y (t₀ + ((0 + (((6 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter6]
      have hval6 : ((6 : Fin 7) : ℕ) = 6 := rfl
      have : ((0 + (((6 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 6 := by
        rw [hval6]; push_cast; ring
      rw [this]
      exact he6_bd
  have hres_gen : ∀ n : ℕ, n < N →
      ‖abResidualVec 7 α h y t₀ n‖ ≤ C * h ^ (7 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 7 ≤ (N : ℝ) + 6 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn7_le : ((n : ℝ) + 7) * h ≤ T := by
      have hmul : ((n : ℝ) + 7) * h ≤ ((N : ℝ) + 6) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn7_le
    have hbridge :=
      ab7VecResidual_eq_abResidualVec (E := E) h y t₀ n
    have hpow : C * h ^ (7 + 1) = C * h ^ 8 := by norm_num
    rw [hα_def, ← hbridge]
    linarith [hres, hpow.symm.le, hpow.le]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 6) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 6 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic_vec (p := 7) hs α hh.le hL hC_nn hf t₀
      y₀_sept y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 7 α L = (40633 / 945) * L from by
    rw [hα_def]
    exact abLip_ab7GenericCoeff L] at hgeneric
  have hwindow_ge : abErrVec 7 α h f t₀ y₀_sept y N
      ≤ abErrWindowVec hs α h f t₀ y₀_sept y N := by
    show abErrVec 7 α h f t₀ y₀_sept y (N + ((⟨0, hs⟩ : Fin 7) : ℕ))
        ≤ abErrWindowVec hs α h f t₀ y₀_sept y N
    unfold abErrWindowVec
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 7 => abErrVec 7 α h f t₀ y₀_sept y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIterVec 7 α h f t₀ y₀_sept N
        = ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N := by
    rw [hα_def, hy_sept_def]
    exact (ab7IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N).symm
  have habsErr :
      abErrVec 7 α h f t₀ y₀_sept y N
        = ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N - y (t₀ + (N : ℝ) * h)‖ := by
    show ‖abIterVec 7 α h f t₀ y₀_sept N - y (t₀ + (N : ℝ) * h)‖
        = ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N - y (t₀ + (N : ℝ) * h)‖
    rw [hbridge]
  show ‖ab7IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N - y (t₀ + (N : ℝ) * h)‖
      ≤ Real.exp ((40633 / 945) * L * T) * ε₀
        + T * Real.exp ((40633 / 945) * L * T) * C * h ^ 7
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
