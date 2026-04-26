import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB5Convergence
import OpenMath.LMMAB6ScalarConvergence

/-! ## Adams–Bashforth 6-step Vector Convergence Chain (Iserles §1.2)

Vector-valued AB6 convergence chain, split from the scalar AB6 file to keep
the order-6 development below the project file-size cap. -/

namespace LMM

/-- AB6 vector iteration with six starting samples. -/
noncomputable def ab6IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) : ℕ → E
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | n + 6 =>
      ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
        + h • ((4277 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5))
              - (7923 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4))
              + (9982 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3))
              - (7298 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2))
              + (2877 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1))
              - (475 / 1440 : ℝ) • f (t₀ + (n : ℝ) * h)
                (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n))

@[simp] lemma ab6IterVec_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) :
    ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 0 = y₀ := rfl

@[simp] lemma ab6IterVec_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) :
    ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 1 = y₁ := rfl

@[simp] lemma ab6IterVec_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) :
    ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 2 = y₂ := rfl

@[simp] lemma ab6IterVec_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) :
    ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 3 = y₃ := rfl

@[simp] lemma ab6IterVec_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) :
    ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 4 = y₄ := rfl

@[simp] lemma ab6IterVec_five
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) :
    ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 5 = y₅ := rfl

lemma ab6IterVec_succ_succ_succ_succ_succ_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) (n : ℕ) :
    ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
      = ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
          + h • ((4277 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                  (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5))
                - (7923 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                    (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4))
                + (9982 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                    (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3))
                - (7298 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                    (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2))
                + (2877 / 1440 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                    (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1))
                - (475 / 1440 : ℝ) • f (t₀ + (n : ℝ) * h)
                    (ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n)) := rfl

/-- Vector AB6 local truncation residual. -/
noncomputable def ab6VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 6 * h) - y (t + 5 * h)
    - h • ((4277 / 1440 : ℝ) • deriv y (t + 5 * h)
          - (7923 / 1440 : ℝ) • deriv y (t + 4 * h)
          + (9982 / 1440 : ℝ) • deriv y (t + 3 * h)
          - (7298 / 1440 : ℝ) • deriv y (t + 2 * h)
          + (2877 / 1440 : ℝ) • deriv y (t + h)
          - (475 / 1440 : ℝ) • deriv y t)

theorem ab6Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab6VecResidual h t y
      = y (t + 6 * h) - y (t + 5 * h)
          - h • ((4277 / 1440 : ℝ) • deriv y (t + 5 * h)
                - (7923 / 1440 : ℝ) • deriv y (t + 4 * h)
                + (9982 / 1440 : ℝ) • deriv y (t + 3 * h)
                - (7298 / 1440 : ℝ) • deriv y (t + 2 * h)
                + (2877 / 1440 : ℝ) • deriv y (t + h)
                - (475 / 1440 : ℝ) • deriv y t) := rfl

theorem ab6Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
        - y (t₀ + ((n : ℝ) + 6) * h)‖
      ≤ ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
            - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (4277 / 1440) * h * L
            * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (7923 / 1440) * h * L
            * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (9982 / 1440) * h * L
            * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (7298 / 1440) * h * L
            * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (2877 / 1440) * h * L
            * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (475 / 1440) * h * L
            * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n
                - y (t₀ + (n : ℝ) * h)‖
        + ‖ab6VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n with hyn_def
  set yn1 : E := ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1) with hyn1_def
  set yn2 : E := ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2) with hyn2_def
  set yn3 : E := ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3) with hyn3_def
  set yn4 : E := ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4) with hyn4_def
  set yn5 : E := ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5) with hyn5_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set zn3 : E := y tn3 with hzn3_def
  set zn4 : E := y tn4 with hzn4_def
  set zn5 : E := y tn5 with hzn5_def
  set zn6 : E := y tn6 with hzn6_def
  set τ : E := ab6VecResidual h tn y with hτ_def
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  have htn_6h : tn + 6 * h = tn6 := by simp [htn_def, htn6_def]; ring
  have hτ_eq :
      τ = zn6 - zn5
            - h • ((4277 / 1440 : ℝ) • f tn5 zn5
                  - (7923 / 1440 : ℝ) • f tn4 zn4
                  + (9982 / 1440 : ℝ) • f tn3 zn3
                  - (7298 / 1440 : ℝ) • f tn2 zn2
                  + (2877 / 1440 : ℝ) • f tn1 zn1
                  - (475 / 1440 : ℝ) • f tn zn) := by
    show ab6VecResidual h tn y = _
    unfold ab6VecResidual
    rw [htn1_h, htn_2h, htn_3h, htn_4h, htn_5h, htn_6h,
      hyf tn5, hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  have hstep : ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
      = yn5 + h • ((4277 / 1440 : ℝ) • f tn5 yn5
                    - (7923 / 1440 : ℝ) • f tn4 yn4
                    + (9982 / 1440 : ℝ) • f tn3 yn3
                    - (7298 / 1440 : ℝ) • f tn2 yn2
                    + (2877 / 1440 : ℝ) • f tn1 yn1
                    - (475 / 1440 : ℝ) • f tn yn) := by
    show ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) = _
    rw [ab6IterVec_succ_succ_succ_succ_succ_succ]
  have halg : ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) - zn6
      = (yn5 - zn5)
        + h • ((4277 / 1440 : ℝ) • (f tn5 yn5 - f tn5 zn5))
        - h • ((7923 / 1440 : ℝ) • (f tn4 yn4 - f tn4 zn4))
        + h • ((9982 / 1440 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        - h • ((7298 / 1440 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        + h • ((2877 / 1440 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        - h • ((475 / 1440 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    rw [hstep, hτ_eq]
    simp only [smul_sub, smul_add]
    abel
  have hLip5 : ‖f tn5 yn5 - f tn5 zn5‖ ≤ L * ‖yn5 - zn5‖ := hf tn5 yn5 zn5
  have hLip4 : ‖f tn4 yn4 - f tn4 zn4‖ ≤ L * ‖yn4 - zn4‖ := hf tn4 yn4 zn4
  have hLip3 : ‖f tn3 yn3 - f tn3 zn3‖ ≤ L * ‖yn3 - zn3‖ := hf tn3 yn3 zn3
  have hLip2 : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ := hf tn2 yn2 zn2
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ := hf tn1 yn1 zn1
  have hLip0 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ := hf tn yn zn
  have h4277_nn : (0 : ℝ) ≤ 4277 / 1440 := by norm_num
  have h7923_nn : (0 : ℝ) ≤ 7923 / 1440 := by norm_num
  have h9982_nn : (0 : ℝ) ≤ 9982 / 1440 := by norm_num
  have h7298_nn : (0 : ℝ) ≤ 7298 / 1440 := by norm_num
  have h2877_nn : (0 : ℝ) ≤ 2877 / 1440 := by norm_num
  have h475_nn : (0 : ℝ) ≤ 475 / 1440 := by norm_num
  have h4277_norm :
      ‖h • ((4277 / 1440 : ℝ) • (f tn5 yn5 - f tn5 zn5))‖
        ≤ (4277 / 1440) * h * L * ‖yn5 - zn5‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h4277_nn]
    have : h * ((4277 / 1440 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((4277 / 1440 : ℝ) * (L * ‖yn5 - zn5‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip5 h4277_nn
    calc
      h * ((4277 / 1440 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
          ≤ h * ((4277 / 1440 : ℝ) * (L * ‖yn5 - zn5‖)) := this
      _ = (4277 / 1440) * h * L * ‖yn5 - zn5‖ := by ring
  have h7923_norm :
      ‖h • ((7923 / 1440 : ℝ) • (f tn4 yn4 - f tn4 zn4))‖
        ≤ (7923 / 1440) * h * L * ‖yn4 - zn4‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h7923_nn]
    have : h * ((7923 / 1440 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((7923 / 1440 : ℝ) * (L * ‖yn4 - zn4‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip4 h7923_nn
    calc
      h * ((7923 / 1440 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
          ≤ h * ((7923 / 1440 : ℝ) * (L * ‖yn4 - zn4‖)) := this
      _ = (7923 / 1440) * h * L * ‖yn4 - zn4‖ := by ring
  have h9982_norm :
      ‖h • ((9982 / 1440 : ℝ) • (f tn3 yn3 - f tn3 zn3))‖
        ≤ (9982 / 1440) * h * L * ‖yn3 - zn3‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h9982_nn]
    have : h * ((9982 / 1440 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((9982 / 1440 : ℝ) * (L * ‖yn3 - zn3‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip3 h9982_nn
    calc
      h * ((9982 / 1440 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
          ≤ h * ((9982 / 1440 : ℝ) * (L * ‖yn3 - zn3‖)) := this
      _ = (9982 / 1440) * h * L * ‖yn3 - zn3‖ := by ring
  have h7298_norm :
      ‖h • ((7298 / 1440 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
        ≤ (7298 / 1440) * h * L * ‖yn2 - zn2‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h7298_nn]
    have : h * ((7298 / 1440 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((7298 / 1440 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 h7298_nn
    calc
      h * ((7298 / 1440 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
          ≤ h * ((7298 / 1440 : ℝ) * (L * ‖yn2 - zn2‖)) := this
      _ = (7298 / 1440) * h * L * ‖yn2 - zn2‖ := by ring
  have h2877_norm :
      ‖h • ((2877 / 1440 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
        ≤ (2877 / 1440) * h * L * ‖yn1 - zn1‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h2877_nn]
    have : h * ((2877 / 1440 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((2877 / 1440 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 h2877_nn
    calc
      h * ((2877 / 1440 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
          ≤ h * ((2877 / 1440 : ℝ) * (L * ‖yn1 - zn1‖)) := this
      _ = (2877 / 1440) * h * L * ‖yn1 - zn1‖ := by ring
  have h475_norm :
      ‖h • ((475 / 1440 : ℝ) • (f tn yn - f tn zn))‖
        ≤ (475 / 1440) * h * L * ‖yn - zn‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h475_nn]
    have : h * ((475 / 1440 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((475 / 1440 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 h475_nn
    calc
      h * ((475 / 1440 : ℝ) * ‖f tn yn - f tn zn‖)
          ≤ h * ((475 / 1440 : ℝ) * (L * ‖yn - zn‖)) := this
      _ = (475 / 1440) * h * L * ‖yn - zn‖ := by ring
  set A : E := yn5 - zn5 with hA_def
  set B : E := h • ((4277 / 1440 : ℝ) • (f tn5 yn5 - f tn5 zn5)) with hB_def
  set C : E := h • ((7923 / 1440 : ℝ) • (f tn4 yn4 - f tn4 zn4)) with hC_def
  set D : E := h • ((9982 / 1440 : ℝ) • (f tn3 yn3 - f tn3 zn3)) with hD_def
  set G : E := h • ((7298 / 1440 : ℝ) • (f tn2 yn2 - f tn2 zn2)) with hG_def
  set J : E := h • ((2877 / 1440 : ℝ) • (f tn1 yn1 - f tn1 zn1)) with hJ_def
  set K : E := h • ((475 / 1440 : ℝ) • (f tn yn - f tn zn)) with hK_def
  have htri : ‖A + B - C + D - G + J - K - τ‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖G‖ + ‖J‖ + ‖K‖ + ‖τ‖ := by
    have h1 : ‖A + B - C + D - G + J - K - τ‖
        ≤ ‖A + B - C + D - G + J - K‖ + ‖τ‖ := norm_sub_le _ _
    have h2 : ‖A + B - C + D - G + J - K‖
        ≤ ‖A + B - C + D - G + J‖ + ‖K‖ := norm_sub_le _ _
    have h3 : ‖A + B - C + D - G + J‖
        ≤ ‖A + B - C + D - G‖ + ‖J‖ := norm_add_le _ _
    have h4 : ‖A + B - C + D - G‖
        ≤ ‖A + B - C + D‖ + ‖G‖ := norm_sub_le _ _
    have h5 : ‖A + B - C + D‖
        ≤ ‖A + B - C‖ + ‖D‖ := norm_add_le _ _
    have h6 : ‖A + B - C‖ ≤ ‖A + B‖ + ‖C‖ := norm_sub_le _ _
    have h7 : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    linarith
  have hB_bd : ‖B‖ ≤ (4277 / 1440) * h * L * ‖yn5 - zn5‖ := by
    simpa [hB_def] using h4277_norm
  have hC_bd : ‖C‖ ≤ (7923 / 1440) * h * L * ‖yn4 - zn4‖ := by
    simpa [hC_def] using h7923_norm
  have hD_bd : ‖D‖ ≤ (9982 / 1440) * h * L * ‖yn3 - zn3‖ := by
    simpa [hD_def] using h9982_norm
  have hG_bd : ‖G‖ ≤ (7298 / 1440) * h * L * ‖yn2 - zn2‖ := by
    simpa [hG_def] using h7298_norm
  have hJ_bd : ‖J‖ ≤ (2877 / 1440) * h * L * ‖yn1 - zn1‖ := by
    simpa [hJ_def] using h2877_norm
  have hK_bd : ‖K‖ ≤ (475 / 1440) * h * L * ‖yn - zn‖ := by
    simpa [hK_def] using h475_norm
  have hcalc :
      ‖A + B - C + D - G + J - K - τ‖
        ≤ ‖yn5 - zn5‖
          + (4277 / 1440) * h * L * ‖yn5 - zn5‖
          + (7923 / 1440) * h * L * ‖yn4 - zn4‖
          + (9982 / 1440) * h * L * ‖yn3 - zn3‖
          + (7298 / 1440) * h * L * ‖yn2 - zn2‖
          + (2877 / 1440) * h * L * ‖yn1 - zn1‖
          + (475 / 1440) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    have hA_norm : ‖A‖ = ‖yn5 - zn5‖ := by rw [hA_def]
    linarith [htri, hA_norm, hB_bd, hC_bd, hD_bd, hG_bd, hJ_bd, hK_bd]
  calc
    ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) - zn6‖
        = ‖A + B - C + D - G + J - K - τ‖ := by
          rw [halg, hA_def, hB_def, hC_def, hD_def, hG_def, hJ_def, hK_def]
    _ ≤ ‖yn5 - zn5‖
          + (4277 / 1440) * h * L * ‖yn5 - zn5‖
          + (7923 / 1440) * h * L * ‖yn4 - zn4‖
          + (9982 / 1440) * h * L * ‖yn3 - zn3‖
          + (7298 / 1440) * h * L * ‖yn2 - zn2‖
          + (2877 / 1440) * h * L * ‖yn1 - zn1‖
          + (475 / 1440) * h * L * ‖yn - zn‖
          + ‖τ‖ := hcalc

theorem ab6Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max
          ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
              - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
              - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
              - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
              - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
              - y (t₀ + ((n : ℝ) + 5) * h)‖)
        ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
            - y (t₀ + ((n : ℝ) + 6) * h)‖
      ≤ (1 + h * ((114 / 5) * L))
            * max (max (max (max (max
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n
                      - y (t₀ + (n : ℝ) * h)‖
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)‖)
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)‖)
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)‖)
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)‖)
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
                      - y (t₀ + ((n : ℝ) + 5) * h)‖
        + ‖ab6VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ :=
    ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n - y (t₀ + (n : ℝ) * h)‖
    with hen_def
  set en1 : ℝ :=
    ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
        - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
        - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set en3 : ℝ :=
    ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
        - y (t₀ + ((n : ℝ) + 3) * h)‖ with hen3_def
  set en4 : ℝ :=
    ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
        - y (t₀ + ((n : ℝ) + 4) * h)‖ with hen4_def
  set en5 : ℝ :=
    ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
        - y (t₀ + ((n : ℝ) + 5) * h)‖ with hen5_def
  set en6 : ℝ :=
    ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
        - y (t₀ + ((n : ℝ) + 6) * h)‖ with hen6_def
  set τabs : ℝ := ‖ab6VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hen4_nn : 0 ≤ en4 := norm_nonneg _
  have hen5_nn : 0 ≤ en5 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hstep :
      en6 ≤ en5 + (4277 / 1440) * h * L * en5
                + (7923 / 1440) * h * L * en4
                + (9982 / 1440) * h * L * en3
                + (7298 / 1440) * h * L * en2
                + (2877 / 1440) * h * L * en1
                + (475 / 1440) * h * L * en + τabs := by
    have := ab6Vec_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y hyf n
    show ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
          - y (t₀ + ((n : ℝ) + 6) * h)‖
        ≤ ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
              - y (t₀ + ((n : ℝ) + 5) * h)‖
          + (4277 / 1440) * h * L
              * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
                  - y (t₀ + ((n : ℝ) + 5) * h)‖
          + (7923 / 1440) * h * L
              * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)‖
          + (9982 / 1440) * h * L
              * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)‖
          + (7298 / 1440) * h * L
              * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)‖
          + (2877 / 1440) * h * L
              * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)‖
          + (475 / 1440) * h * L
              * ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n
                  - y (t₀ + (n : ℝ) * h)‖
          + ‖ab6VecResidual h (t₀ + (n : ℝ) * h) y‖
    exact this
  set EN_n : ℝ := max (max (max (max (max en en1) en2) en3) en4) en5 with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen5_le_EN : en5 ≤ EN_n := le_max_right _ _
  have h4277_nn : 0 ≤ (4277 / 1440) * h * L := by positivity
  have h7923_nn : 0 ≤ (7923 / 1440) * h * L := by positivity
  have h9982_nn : 0 ≤ (9982 / 1440) * h * L := by positivity
  have h7298_nn : 0 ≤ (7298 / 1440) * h * L := by positivity
  have h2877_nn : 0 ≤ (2877 / 1440) * h * L := by positivity
  have h475_nn : 0 ≤ (475 / 1440) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((114 / 5) * L) := by positivity
  have hen6_bd : en6 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    have h1 : (4277 / 1440) * h * L * en5 ≤ (4277 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen5_le_EN h4277_nn
    have h2 : (7923 / 1440) * h * L * en4 ≤ (7923 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN h7923_nn
    have h3 : (9982 / 1440) * h * L * en3 ≤ (9982 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN h9982_nn
    have h4 : (7298 / 1440) * h * L * en2 ≤ (7298 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h7298_nn
    have h5 : (2877 / 1440) * h * L * en1 ≤ (2877 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h2877_nn
    have h6 : (475 / 1440) * h * L * en ≤ (475 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h475_nn
    have h_alg :
        EN_n + (4277 / 1440) * h * L * EN_n
              + (7923 / 1440) * h * L * EN_n
              + (9982 / 1440) * h * L * EN_n
              + (7298 / 1440) * h * L * EN_n
              + (2877 / 1440) * h * L * EN_n
              + (475 / 1440) * h * L * EN_n + τabs
          = (1 + h * ((114 / 5) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen5_le_EN, h1, h2, h3, h4, h5, h6, h_alg.le]
  have hEN_le_grow : EN_n ≤ (1 + h * ((114 / 5) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((114 / 5) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  have hen5_bd : en5 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen5_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd)
    hen4_bd) hen5_bd) hen6_bd

private theorem iteratedDeriv_seven_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 7 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 7 y t‖ ≤ M := by
  have h_cont : Continuous (iteratedDeriv 7 y) :=
    hy.continuous_iteratedDeriv 7 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

private theorem y_seventh_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 7 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 7 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖y (t + r) - y t - r • deriv y t
        - (r ^ 2 / 2) • iteratedDeriv 2 y t
        - (r ^ 3 / 6) • iteratedDeriv 3 y t
        - (r ^ 4 / 24) • iteratedDeriv 4 y t
        - (r ^ 5 / 120) • iteratedDeriv 5 y t
        - (r ^ 6 / 720) • iteratedDeriv 6 y t‖
      ≤ M / 5040 * r ^ 7 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htr_le : t ≤ t + r := by linarith
  have h_dy_bound :
      ∀ s ∈ Set.Icc t (t + r),
        ‖deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
            - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
            - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
            - ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
            - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t‖
          ≤ M / 720 * (s - t) ^ 6 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have hdy : ContDiff ℝ 6 (deriv y) := hy.deriv'
    have hbnd_d :
        ∀ u ∈ Set.Icc a b, ‖iteratedDeriv 6 (deriv y) u‖ ≤ M := by
      intro u hu
      have hidd_eq : iteratedDeriv 6 (deriv y) = iteratedDeriv 7 y := by
        have : iteratedDeriv 7 y = iteratedDeriv 6 (deriv y) :=
          iteratedDeriv_succ' (n := 6) (f := y)
        exact this.symm
      simpa [hidd_eq] using hbnd u hu
    have hrem :=
      y_sixth_order_taylor_remainder_vec hdy hbnd_d ht
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
    rw [hsplit] at hrem
    simpa [hderiv2, hiter2, hiter3, hiter4, hiter5] using hrem
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
  have h_residual_integral :
      y (t + r) - y t - r • deriv y t
          - (r ^ 2 / 2) • iteratedDeriv 2 y t
          - (r ^ 3 / 6) • iteratedDeriv 3 y t
          - (r ^ 4 / 24) • iteratedDeriv 4 y t
          - (r ^ 5 / 120) • iteratedDeriv 5 y t
          - (r ^ 6 / 720) • iteratedDeriv 6 y t
        = ∫ s in t..t + r,
            (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
              - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
              - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
              - ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
              - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t) := by
    rw [intervalIntegral.integral_sub
        (((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub h_cubic_int).sub
          h_quartic_int) h_quintic_int,
      intervalIntegral.integral_sub
        ((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub h_cubic_int)
          h_quartic_int,
      intervalIntegral.integral_sub
        (((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int) h_cubic_int,
      intervalIntegral.integral_sub
        ((h_dy_int.sub h_const_int).sub h_lin_int) h_quad_int,
      intervalIntegral.integral_sub (h_dy_int.sub h_const_int) h_lin_int,
      intervalIntegral.integral_sub h_dy_int h_const_int,
      h_ftc_y, h_lin_eval, h_quad_eval, h_cubic_eval, h_quartic_eval,
      h_quintic_eval]
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
            - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t)‖
        ≤ ∫ s in t..t + r, M / 720 * (s - t) ^ 6 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dy_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 720 * (s - t) ^ 6).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 720 * (s - t) ^ 6 = M / 5040 * r ^ 7 := by
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
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

private theorem derivY_sixth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 7 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 7 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖deriv y (t + r) - deriv y t - r • iteratedDeriv 2 y t
        - (r ^ 2 / 2) • iteratedDeriv 3 y t
        - (r ^ 3 / 6) • iteratedDeriv 4 y t
        - (r ^ 4 / 24) • iteratedDeriv 5 y t
        - (r ^ 5 / 120) • iteratedDeriv 6 y t‖
      ≤ M / 720 * r ^ 6 := by
  have hdy : ContDiff ℝ 6 (deriv y) := hy.deriv'
  have hbnd_d :
      ∀ s ∈ Set.Icc a b, ‖iteratedDeriv 6 (deriv y) s‖ ≤ M := by
    intro s hs
    have hidd_eq : iteratedDeriv 6 (deriv y) = iteratedDeriv 7 y := by
      have : iteratedDeriv 7 y = iteratedDeriv 6 (deriv y) :=
        iteratedDeriv_succ' (n := 6) (f := y)
      exact this.symm
    simpa [hidd_eq] using hbnd s hs
  have hrem := y_sixth_order_taylor_remainder_vec hdy hbnd_d ht htr hr
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
  simpa [hderiv2, hiter2, hiter3, hiter4, hiter5] using hrem

private lemma ab6Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y5 y6 d0 d1 d2 d3 d4 d5 dd ddd dddd ddddd dddddd : E) (h : ℝ) :
    y6 - y5 - h • ((4277 / 1440 : ℝ) • d5 - (7923 / 1440 : ℝ) • d4
                  + (9982 / 1440 : ℝ) • d3 - (7298 / 1440 : ℝ) • d2
                  + (2877 / 1440 : ℝ) • d1 - (475 / 1440 : ℝ) • d0)
      = (y6 - y0 - (6 * h) • d0
            - ((6 * h) ^ 2 / 2) • dd
            - ((6 * h) ^ 3 / 6) • ddd
            - ((6 * h) ^ 4 / 24) • dddd
            - ((6 * h) ^ 5 / 120) • ddddd
            - ((6 * h) ^ 6 / 720) • dddddd)
        - (y5 - y0 - (5 * h) • d0
            - ((5 * h) ^ 2 / 2) • dd
            - ((5 * h) ^ 3 / 6) • ddd
            - ((5 * h) ^ 4 / 24) • dddd
            - ((5 * h) ^ 5 / 120) • ddddd
            - ((5 * h) ^ 6 / 720) • dddddd)
        - (4277 * h / 1440 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd)
        + (7923 * h / 1440 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd)
        - (9982 * h / 1440 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd)
        + (7298 * h / 1440 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd)
        - (2877 * h / 1440 : ℝ)
            • (d1 - d0 - h • dd
                - (h ^ 2 / 2) • ddd
                - (h ^ 3 / 6) • dddd
                - (h ^ 4 / 24) • ddddd
                - (h ^ 5 / 120) • dddddd) := by
  simp only [smul_sub, smul_add, smul_smul]
  module

private lemma ab6Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 5040 * (6 * h) ^ 7 + M / 5040 * (5 * h) ^ 7
      + (4277 * h / 1440) * (M / 720 * (5 * h) ^ 6)
      + (7923 * h / 1440) * (M / 720 * (4 * h) ^ 6)
      + (9982 * h / 1440) * (M / 720 * (3 * h) ^ 6)
      + (7298 * h / 1440) * (M / 720 * (2 * h) ^ 6)
      + (2877 * h / 1440) * (M / 720 * h ^ 6)
      = (1264800760 / 7257600 : ℝ) * M * h ^ 7 := by
  ring

private lemma ab6Vec_residual_seven_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D G J K : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (4277 * h / 1440 : ℝ) • C + (7923 * h / 1440 : ℝ) • D
        - (9982 * h / 1440 : ℝ) • G + (7298 * h / 1440 : ℝ) • J
        - (2877 * h / 1440 : ℝ) • K‖
      ≤ ‖A‖ + ‖B‖ + (4277 * h / 1440) * ‖C‖ + (7923 * h / 1440) * ‖D‖
          + (9982 * h / 1440) * ‖G‖ + (7298 * h / 1440) * ‖J‖
          + (2877 * h / 1440) * ‖K‖ := by
  have h4277h_nn : 0 ≤ (4277 * h / 1440 : ℝ) := by linarith
  have h7923h_nn : 0 ≤ (7923 * h / 1440 : ℝ) := by linarith
  have h9982h_nn : 0 ≤ (9982 * h / 1440 : ℝ) := by linarith
  have h7298h_nn : 0 ≤ (7298 * h / 1440 : ℝ) := by linarith
  have h2877h_nn : 0 ≤ (2877 * h / 1440 : ℝ) := by linarith
  have hC_norm :
      ‖(4277 * h / 1440 : ℝ) • C‖ = (4277 * h / 1440) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg h4277h_nn]
  have hD_norm :
      ‖(7923 * h / 1440 : ℝ) • D‖ = (7923 * h / 1440) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg h7923h_nn]
  have hG_norm :
      ‖(9982 * h / 1440 : ℝ) • G‖ = (9982 * h / 1440) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg h9982h_nn]
  have hJ_norm :
      ‖(7298 * h / 1440 : ℝ) • J‖ = (7298 * h / 1440) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg h7298h_nn]
  have hK_norm :
      ‖(2877 * h / 1440 : ℝ) • K‖ = (2877 * h / 1440) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg h2877h_nn]
  have h1 : ‖A - B - (4277 * h / 1440 : ℝ) • C + (7923 * h / 1440 : ℝ) • D
                - (9982 * h / 1440 : ℝ) • G + (7298 * h / 1440 : ℝ) • J
                - (2877 * h / 1440 : ℝ) • K‖
      ≤ ‖A - B - (4277 * h / 1440 : ℝ) • C + (7923 * h / 1440 : ℝ) • D
            - (9982 * h / 1440 : ℝ) • G + (7298 * h / 1440 : ℝ) • J‖
        + ‖(2877 * h / 1440 : ℝ) • K‖ := norm_sub_le _ _
  have h2 : ‖A - B - (4277 * h / 1440 : ℝ) • C + (7923 * h / 1440 : ℝ) • D
                - (9982 * h / 1440 : ℝ) • G + (7298 * h / 1440 : ℝ) • J‖
      ≤ ‖A - B - (4277 * h / 1440 : ℝ) • C + (7923 * h / 1440 : ℝ) • D
            - (9982 * h / 1440 : ℝ) • G‖
        + ‖(7298 * h / 1440 : ℝ) • J‖ := norm_add_le _ _
  have h3 : ‖A - B - (4277 * h / 1440 : ℝ) • C + (7923 * h / 1440 : ℝ) • D
                - (9982 * h / 1440 : ℝ) • G‖
      ≤ ‖A - B - (4277 * h / 1440 : ℝ) • C + (7923 * h / 1440 : ℝ) • D‖
        + ‖(9982 * h / 1440 : ℝ) • G‖ := norm_sub_le _ _
  have h4 : ‖A - B - (4277 * h / 1440 : ℝ) • C + (7923 * h / 1440 : ℝ) • D‖
      ≤ ‖A - B - (4277 * h / 1440 : ℝ) • C‖
        + ‖(7923 * h / 1440 : ℝ) • D‖ := norm_add_le _ _
  have h5 : ‖A - B - (4277 * h / 1440 : ℝ) • C‖
      ≤ ‖A - B‖ + ‖(4277 * h / 1440 : ℝ) • C‖ := norm_sub_le _ _
  have h6 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith [hC_norm.le, hC_norm.ge, hD_norm.le, hD_norm.ge,
    hG_norm.le, hG_norm.ge, hJ_norm.le, hJ_norm.ge,
    hK_norm.le, hK_norm.ge]

private theorem ab6Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 7 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 7 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 6 * h) - y (t + 5 * h)
        - h • ((4277 / 1440 : ℝ) • deriv y (t + 5 * h)
              - (7923 / 1440 : ℝ) • deriv y (t + 4 * h)
              + (9982 / 1440 : ℝ) • deriv y (t + 3 * h)
              - (7298 / 1440 : ℝ) • deriv y (t + 2 * h)
              + (2877 / 1440 : ℝ) • deriv y (t + h)
              - (475 / 1440 : ℝ) • deriv y t)‖
      ≤ (175 : ℝ) * M * h ^ 7 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have hRy5 :=
    y_seventh_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRy6 :=
    y_seventh_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp1 :=
    derivY_sixth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_sixth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_sixth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_sixth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_sixth_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  set y0 : E := y t with hy0_def
  set y5 : E := y (t + 5 * h) with hy5_def
  set y6 : E := y (t + 6 * h) with hy6_def
  set d0 : E := deriv y t with hd0_def
  set d1 : E := deriv y (t + h) with hd1_def
  set d2 : E := deriv y (t + 2 * h) with hd2_def
  set d3 : E := deriv y (t + 3 * h) with hd3_def
  set d4 : E := deriv y (t + 4 * h) with hd4_def
  set d5 : E := deriv y (t + 5 * h) with hd5_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  set ddddd : E := iteratedDeriv 5 y t with hddddd_def
  set dddddd : E := iteratedDeriv 6 y t with hdddddd_def
  have hLTE_eq :
      y6 - y5 - h • ((4277 / 1440 : ℝ) • d5 - (7923 / 1440 : ℝ) • d4
                    + (9982 / 1440 : ℝ) • d3 - (7298 / 1440 : ℝ) • d2
                    + (2877 / 1440 : ℝ) • d1 - (475 / 1440 : ℝ) • d0)
        = (y6 - y0 - (6 * h) • d0
              - ((6 * h) ^ 2 / 2) • dd
              - ((6 * h) ^ 3 / 6) • ddd
              - ((6 * h) ^ 4 / 24) • dddd
              - ((6 * h) ^ 5 / 120) • ddddd
              - ((6 * h) ^ 6 / 720) • dddddd)
          - (y5 - y0 - (5 * h) • d0
              - ((5 * h) ^ 2 / 2) • dd
              - ((5 * h) ^ 3 / 6) • ddd
              - ((5 * h) ^ 4 / 24) • dddd
              - ((5 * h) ^ 5 / 120) • ddddd
              - ((5 * h) ^ 6 / 720) • dddddd)
          - (4277 * h / 1440 : ℝ)
              • (d5 - d0 - (5 * h) • dd
                  - ((5 * h) ^ 2 / 2) • ddd
                  - ((5 * h) ^ 3 / 6) • dddd
                  - ((5 * h) ^ 4 / 24) • ddddd
                  - ((5 * h) ^ 5 / 120) • dddddd)
          + (7923 * h / 1440 : ℝ)
              • (d4 - d0 - (4 * h) • dd
                  - ((4 * h) ^ 2 / 2) • ddd
                  - ((4 * h) ^ 3 / 6) • dddd
                  - ((4 * h) ^ 4 / 24) • ddddd
                  - ((4 * h) ^ 5 / 120) • dddddd)
          - (9982 * h / 1440 : ℝ)
              • (d3 - d0 - (3 * h) • dd
                  - ((3 * h) ^ 2 / 2) • ddd
                  - ((3 * h) ^ 3 / 6) • dddd
                  - ((3 * h) ^ 4 / 24) • ddddd
                  - ((3 * h) ^ 5 / 120) • dddddd)
          + (7298 * h / 1440 : ℝ)
              • (d2 - d0 - (2 * h) • dd
                  - ((2 * h) ^ 2 / 2) • ddd
                  - ((2 * h) ^ 3 / 6) • dddd
                  - ((2 * h) ^ 4 / 24) • ddddd
                  - ((2 * h) ^ 5 / 120) • dddddd)
          - (2877 * h / 1440 : ℝ)
              • (d1 - d0 - h • dd
                  - (h ^ 2 / 2) • ddd
                  - (h ^ 3 / 6) • dddd
                  - (h ^ 4 / 24) • ddddd
                  - (h ^ 5 / 120) • dddddd) :=
    ab6Vec_residual_alg_identity y0 y5 y6 d0 d1 d2 d3 d4 d5 dd ddd dddd ddddd
      dddddd h
  rw [hLTE_eq]
  set A : E := y6 - y0 - (6 * h) • d0
            - ((6 * h) ^ 2 / 2) • dd
            - ((6 * h) ^ 3 / 6) • ddd
            - ((6 * h) ^ 4 / 24) • dddd
            - ((6 * h) ^ 5 / 120) • ddddd
            - ((6 * h) ^ 6 / 720) • dddddd with hA_def
  set B : E := y5 - y0 - (5 * h) • d0
            - ((5 * h) ^ 2 / 2) • dd
            - ((5 * h) ^ 3 / 6) • ddd
            - ((5 * h) ^ 4 / 24) • dddd
            - ((5 * h) ^ 5 / 120) • ddddd
            - ((5 * h) ^ 6 / 720) • dddddd with hB_def
  set C : E := d5 - d0 - (5 * h) • dd
            - ((5 * h) ^ 2 / 2) • ddd
            - ((5 * h) ^ 3 / 6) • dddd
            - ((5 * h) ^ 4 / 24) • ddddd
            - ((5 * h) ^ 5 / 120) • dddddd with hC_def
  set D : E := d4 - d0 - (4 * h) • dd
            - ((4 * h) ^ 2 / 2) • ddd
            - ((4 * h) ^ 3 / 6) • dddd
            - ((4 * h) ^ 4 / 24) • ddddd
            - ((4 * h) ^ 5 / 120) • dddddd with hD_def
  set G : E := d3 - d0 - (3 * h) • dd
            - ((3 * h) ^ 2 / 2) • ddd
            - ((3 * h) ^ 3 / 6) • dddd
            - ((3 * h) ^ 4 / 24) • ddddd
            - ((3 * h) ^ 5 / 120) • dddddd with hG_def
  set J : E := d2 - d0 - (2 * h) • dd
            - ((2 * h) ^ 2 / 2) • ddd
            - ((2 * h) ^ 3 / 6) • dddd
            - ((2 * h) ^ 4 / 24) • ddddd
            - ((2 * h) ^ 5 / 120) • dddddd with hJ_def
  set K : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd
            - (h ^ 4 / 24) • ddddd
            - (h ^ 5 / 120) • dddddd with hK_def
  have h4277h_nn : 0 ≤ (4277 * h / 1440 : ℝ) := by linarith
  have h7923h_nn : 0 ≤ (7923 * h / 1440 : ℝ) := by linarith
  have h9982h_nn : 0 ≤ (9982 * h / 1440 : ℝ) := by linarith
  have h7298h_nn : 0 ≤ (7298 * h / 1440 : ℝ) := by linarith
  have h2877h_nn : 0 ≤ (2877 * h / 1440 : ℝ) := by linarith
  have htri := ab6Vec_residual_seven_term_triangle A B C D G J K h hh
  have hA_bd : ‖A‖ ≤ M / 5040 * (6 * h) ^ 7 := hRy6
  have hB_bd : ‖B‖ ≤ M / 5040 * (5 * h) ^ 7 := hRy5
  have hC_bd : ‖C‖ ≤ M / 720 * (5 * h) ^ 6 := hRyp5
  have hD_bd : ‖D‖ ≤ M / 720 * (4 * h) ^ 6 := hRyp4
  have hG_bd : ‖G‖ ≤ M / 720 * (3 * h) ^ 6 := hRyp3
  have hJ_bd : ‖J‖ ≤ M / 720 * (2 * h) ^ 6 := hRyp2
  have hK_bd : ‖K‖ ≤ M / 720 * h ^ 6 := hRyp1
  have h4277C_bd : (4277 * h / 1440) * ‖C‖
      ≤ (4277 * h / 1440) * (M / 720 * (5 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hC_bd h4277h_nn
  have h7923D_bd : (7923 * h / 1440) * ‖D‖
      ≤ (7923 * h / 1440) * (M / 720 * (4 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hD_bd h7923h_nn
  have h9982G_bd : (9982 * h / 1440) * ‖G‖
      ≤ (9982 * h / 1440) * (M / 720 * (3 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hG_bd h9982h_nn
  have h7298J_bd : (7298 * h / 1440) * ‖J‖
      ≤ (7298 * h / 1440) * (M / 720 * (2 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hJ_bd h7298h_nn
  have h2877K_bd : (2877 * h / 1440) * ‖K‖
      ≤ (2877 * h / 1440) * (M / 720 * h ^ 6) :=
    mul_le_mul_of_nonneg_left hK_bd h2877h_nn
  have hbound_alg :
      M / 5040 * (6 * h) ^ 7 + M / 5040 * (5 * h) ^ 7
        + (4277 * h / 1440) * (M / 720 * (5 * h) ^ 6)
        + (7923 * h / 1440) * (M / 720 * (4 * h) ^ 6)
        + (9982 * h / 1440) * (M / 720 * (3 * h) ^ 6)
        + (7298 * h / 1440) * (M / 720 * (2 * h) ^ 6)
        + (2877 * h / 1440) * (M / 720 * h ^ 6)
        = (1264800760 / 7257600 : ℝ) * M * h ^ 7 :=
    ab6Vec_residual_bound_alg_identity M h
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  have hh7_nn : 0 ≤ h ^ 7 := by positivity
  have hMh7_nn : 0 ≤ M * h ^ 7 := mul_nonneg hMnn hh7_nn
  have hslack : (1264800760 / 7257600 : ℝ) * M * h ^ 7 ≤ 175 * M * h ^ 7 := by
    have hle : (1264800760 / 7257600 : ℝ) ≤ 175 := by norm_num
    calc
      (1264800760 / 7257600 : ℝ) * M * h ^ 7
          = (1264800760 / 7257600 : ℝ) * (M * h ^ 7) := by ring
      _ ≤ 175 * (M * h ^ 7) := mul_le_mul_of_nonneg_right hle hMh7_nn
      _ = 175 * M * h ^ 7 := by ring
  calc
    ‖A - B - (4277 * h / 1440 : ℝ) • C + (7923 * h / 1440 : ℝ) • D
          - (9982 * h / 1440 : ℝ) • G + (7298 * h / 1440 : ℝ) • J
          - (2877 * h / 1440 : ℝ) • K‖
      ≤ ‖A‖ + ‖B‖ + (4277 * h / 1440) * ‖C‖ + (7923 * h / 1440) * ‖D‖
          + (9982 * h / 1440) * ‖G‖ + (7298 * h / 1440) * ‖J‖
          + (2877 * h / 1440) * ‖K‖ := htri
    _ ≤ M / 5040 * (6 * h) ^ 7 + M / 5040 * (5 * h) ^ 7
          + (4277 * h / 1440) * (M / 720 * (5 * h) ^ 6)
          + (7923 * h / 1440) * (M / 720 * (4 * h) ^ 6)
          + (9982 * h / 1440) * (M / 720 * (3 * h) ^ 6)
          + (7298 * h / 1440) * (M / 720 * (2 * h) ^ 6)
          + (2877 * h / 1440) * (M / 720 * h ^ 6) := by
        linarith [hA_bd, hB_bd, h4277C_bd, h7923D_bd, h9982G_bd, h7298J_bd,
          h2877K_bd]
    _ = (1264800760 / 7257600 : ℝ) * M * h ^ 7 := hbound_alg
    _ ≤ 175 * M * h ^ 7 := hslack

theorem ab6Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 7 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 6) * h ≤ T →
        ‖ab6VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 7 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_seven_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(175 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 6) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h = ((n : ℝ) + 6) * h := by ring
    linarith
  show ‖ab6VecResidual h t y‖ ≤ 175 * M * h ^ 7
  unfold ab6VecResidual
  exact ab6Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem hh.le

theorem ab6Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 7 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
      ‖y₀ - y t₀‖ ≤ ε₀ → ‖y₁ - y (t₀ + h)‖ ≤ ε₀ →
      ‖y₂ - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖y₃ - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖y₄ - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖y₅ - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 5) * h ≤ T →
      ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((114 / 5) * L * T) * ε₀ + K * h ^ 6 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab6Vec_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((114 / 5) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ k
      - y (t₀ + (k : ℝ) * h)‖
    with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (max (eN k) (eN (k + 1))) (eN (k + 2)))
                  (eN (k + 3))) (eN (k + 4))) (eN (k + 5))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => norm_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (le_max_of_le_left (heN_nn k)))))
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (max (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4)) (eN 5)
        ≤ ε₀
    refine max_le (max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_) ?_
    · show ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 0
          - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀
      simpa using he0_bd
    · show ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 1
          - y (t₀ + ((1 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]
      simpa using he1_bd
    · show ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 2
          - y (t₀ + ((2 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]
      simpa using he2_bd
    · show ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 3
          - y (t₀ + ((3 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]
      simpa using he3_bd
    · show ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 4
          - y (t₀ + ((4 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]
      simpa using he4_bd
    · show ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 5
          - y (t₀ + ((5 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((5 : ℕ) : ℝ) * h = 5 * h := by push_cast; ring
      rw [hcast]
      simpa using he5_bd
  have hLeff_nn : (0 : ℝ) ≤ (114 / 5) * L := by positivity
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 6) * h ≤ T →
      EN (n + 1) ≤ (1 + h * ((114 / 5) * L)) * EN n + C * h ^ 7 := by
    intro n hnh_le
    have honestep := ab6Vec_one_step_error_bound (h := h) (L := L)
        hh.le hL hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hcast4 : ((n + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 4 := by
      push_cast; ring
    have hcast5 : ((n + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 5 := by
      push_cast; ring
    have hcast6 : ((n + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 6 := by
      push_cast; ring
    have heq_eN_n1 : eN (n + 1)
        = ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
            - y (t₀ + ((n : ℝ) + 1) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast1]
    have heq_eN_n2 : eN (n + 1 + 1)
        = ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
            - y (t₀ + ((n : ℝ) + 2) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast2]
    have heq_eN_n3 : eN (n + 1 + 1 + 1)
        = ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
            - y (t₀ + ((n : ℝ) + 3) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast3]
    have heq_eN_n4 : eN (n + 1 + 1 + 1 + 1)
        = ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
            - y (t₀ + ((n : ℝ) + 4) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast4]
    have heq_eN_n5 : eN (n + 1 + 1 + 1 + 1 + 1)
        = ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
            - y (t₀ + ((n : ℝ) + 5) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast5]
    have heq_eN_n6 : eN (n + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
            - y (t₀ + ((n : ℝ) + 6) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast6]
    show max (max (max (max (max (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * ((114 / 5) * L))
            * max (max (max (max (max (eN n) (eN (n + 1))) (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1))
          + C * h ^ 7
    rw [heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5, heq_eN_n6]
    show max (max (max (max (max
              ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)‖
              ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)‖)
              ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)‖)
              ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)‖)
              ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)‖)
              ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
                - y (t₀ + ((n : ℝ) + 6) * h)‖
        ≤ (1 + h * ((114 / 5) * L))
            * max (max (max (max (max (eN n)
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
                    - y (t₀ + ((n : ℝ) + 1) * h)‖)
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
                    - y (t₀ + ((n : ℝ) + 2) * h)‖)
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
                    - y (t₀ + ((n : ℝ) + 3) * h)‖)
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
                    - y (t₀ + ((n : ℝ) + 4) * h)‖)
                  ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
                    - y (t₀ + ((n : ℝ) + 5) * h)‖
          + C * h ^ 7
    linarith [honestep, hres]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((114 / 5) * L * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((114 / 5) * L * T) * C :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  have hh6_nn : 0 ≤ h ^ 6 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((114 / 5) * L * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((114 / 5) * L * T) * ε₀
            + T * Real.exp ((114 / 5) * L * T) * C * h ^ 6 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((114 / 5) * L * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((114 / 5) * L * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh6_nn : 0 ≤ T * Real.exp ((114 / 5) * L * T) * C * h ^ 6 :=
      mul_nonneg hKnn hh6_nn
    linarith
  match N, hNh with
  | 0, _ =>
    have hbase : ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 0
          - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      simpa using he0_bd
    exact hbase_to_headline _ hbase
  | 1, _ =>
    have hbase : ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 1
          - y (t₀ + ((1 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]
      simpa using he1_bd
    exact hbase_to_headline _ hbase
  | 2, _ =>
    have hbase : ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 2
          - y (t₀ + ((2 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]
      simpa using he2_bd
    exact hbase_to_headline _ hbase
  | 3, _ =>
    have hbase : ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 3
          - y (t₀ + ((3 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]
      simpa using he3_bd
    exact hbase_to_headline _ hbase
  | 4, _ =>
    have hbase : ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 4
          - y (t₀ + ((4 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]
      simpa using he4_bd
    exact hbase_to_headline _ hbase
  | 5, _ =>
    have hbase : ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 5
          - y (t₀ + ((5 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((5 : ℕ) : ℝ) * h = 5 * h := by push_cast; ring
      rw [hcast]
      simpa using he5_bd
    exact hbase_to_headline _ hbase
  | N' + 6, hNh =>
    have hcast : (((N' + 6 : ℕ) : ℝ)) = (N' : ℝ) + 6 := by push_cast; ring
    have hN_hyp : ((N' : ℝ) + 6) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * ((114 / 5) * L)) * EN n + C * h ^ (6 + 1) := by
      intro n hn_lt
      have hpow : C * h ^ (6 + 1) = C * h ^ 7 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn1_le_N' : (n : ℝ) + 1 ≤ (N' : ℝ) + 1 := by
        have : (n : ℝ) ≤ (N' : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hn_lt
        linarith
      have h_le_chain : (n : ℝ) + 6 ≤ (N' : ℝ) + 6 := by linarith
      have h_mul : ((n : ℝ) + 6) * h ≤ ((N' : ℝ) + 6) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have : (N' : ℝ) + 1 ≤ (N' : ℝ) + 6 := by linarith
      have := mul_le_mul_of_nonneg_right this hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := (114 / 5) * L) (C := C) (T := T) (p := 6)
        (e := EN) (N := N' + 1)
        hh.le hLeff_nn hC_nn (hEN_nn 0) hgronwall_step (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 6) ≤ EN (N' + 1) := by
      show eN (N' + 6) ≤ max (max (max (max (max (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4)))
              (eN (N' + 1 + 5))
      have heq : N' + 6 = N' + 1 + 5 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((114 / 5) * L * T) * EN 0
          ≤ Real.exp ((114 / 5) * L * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (N' + 6)
          - y (t₀ + ((N' + 6 : ℕ) : ℝ) * h)‖
        ≤ Real.exp ((114 / 5) * L * T) * ε₀
          + T * Real.exp ((114 / 5) * L * T) * C * h ^ 6
    have heN_eq :
        eN (N' + 6)
          = ‖ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (N' + 6)
              - y (t₀ + ((N' + 6 : ℕ) : ℝ) * h)‖ := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
