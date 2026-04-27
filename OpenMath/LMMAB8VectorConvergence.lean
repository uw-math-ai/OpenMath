import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB8Convergence
import OpenMath.LMMAM7Convergence
import OpenMath.LMMAM7VectorConvergence

/-! ## Adams-Bashforth 8-step Vector Quantitative Convergence Chain (Iserles §1.2)

Finite-dimensional vector-valued analogue of the scalar AB8 quantitative
convergence chain in `OpenMath.LMMAB8Convergence`.
-/

namespace LMM

private theorem abIterVec_lipschitz_pointwise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {s : ℕ} (hs : 1 ≤ s) (α : Fin s → ℝ)
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ : Fin s → E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖abIterVec s α h f t₀ y₀ (n + s)
        - y (t₀ + ((n + s : ℕ) : ℝ) * h)‖
      ≤ ‖abIterVec s α h f t₀ y₀ (n + s - 1)
            - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)‖
        + h * (∑ j : Fin s,
            |α j| * L
              * ‖abIterVec s α h f t₀ y₀ (n + (j : ℕ))
                  - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)‖)
        + ‖abResidualVec s α h y t₀ n‖ := by
  haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  set yiter : ℕ → E := abIterVec s α h f t₀ y₀ with hyiter_def
  set τ : E := abResidualVec s α h y t₀ n with hτ_def
  have hstep := abIterVec_step s hs α h f t₀ y₀ n
  have hτ_alt : τ
      = y (t₀ + ((n + s : ℕ) : ℝ) * h)
          - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)
          - h • ∑ j : Fin s, (α j) •
              f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)) := by
    show abResidualVec s α h y t₀ n = _
    unfold abResidualVec
    have hcong :
        (fun j : Fin s => (α j) • deriv y
            (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))
          = (fun j : Fin s => (α j) •
              f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))) := by
      funext j
      rw [hyf]
    rw [hcong]
  set Sa : E := ∑ j : Fin s, (α j) •
      f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
        (yiter (n + (j : ℕ))) with hSa_def
  set Sy : E := ∑ j : Fin s, (α j) •
      f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
        (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)) with hSy_def
  have halg :
      yiter (n + s) - y (t₀ + ((n + s : ℕ) : ℝ) * h)
        = (yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h))
          + h • (Sa - Sy) - τ := by
    rw [hτ_alt]
    have hstep' : yiter (n + s) = yiter (n + s - 1) + h • Sa := by
      rw [hyiter_def, hSa_def]
      exact hstep
    rw [hstep']
    simp only [smul_sub]
    abel
  have hSa_sub_Sy :
      Sa - Sy = ∑ j : Fin s, (α j) •
        (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
          - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
              (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))) := by
    rw [hSa_def, hSy_def, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_sub]
  have h_diff_bound : ∀ j : Fin s,
      ‖(α j) •
          (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
            - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)))‖
        ≤ |α j| * L
            * ‖yiter (n + (j : ℕ))
                - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)‖ := by
    intro j
    have hLip := hf (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
      (yiter (n + (j : ℕ)))
      (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))
    have hαj_nn : 0 ≤ |α j| := abs_nonneg _
    calc
      ‖(α j) •
          (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
            - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)))‖
          = |α j| *
              ‖f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
                - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                    (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |α j| *
            (L * ‖yiter (n + (j : ℕ))
              - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)‖) :=
          mul_le_mul_of_nonneg_left hLip hαj_nn
      _ = |α j| * L
            * ‖yiter (n + (j : ℕ))
                - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)‖ := by ring
  have hSd_norm :
      ‖Sa - Sy‖ ≤ ∑ j : Fin s, |α j| * L
          * ‖yiter (n + (j : ℕ))
              - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)‖ := by
    rw [hSa_sub_Sy]
    calc
      ‖∑ j : Fin s, (α j) •
          (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
            - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)))‖
          ≤ ∑ j : Fin s,
              ‖(α j) •
                (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
                  - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                    (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)))‖ := by
            simpa using norm_sum_le (Finset.univ)
              (fun j : Fin s => (α j) •
                (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
                  - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                    (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))))
      _ ≤ ∑ j : Fin s, |α j| * L
            * ‖yiter (n + (j : ℕ))
                - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)‖ :=
          Finset.sum_le_sum (fun j _ => h_diff_bound j)
  have htri :
      ‖yiter (n + s) - y (t₀ + ((n + s : ℕ) : ℝ) * h)‖
        ≤ ‖yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)‖
          + ‖h • (Sa - Sy)‖ + ‖τ‖ := by
    rw [halg]
    have h1 :
        ‖(yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h))
            + h • (Sa - Sy) - τ‖
          ≤ ‖(yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h))
              + h • (Sa - Sy)‖ + ‖τ‖ := norm_sub_le _ _
    have h2 :
        ‖(yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h))
            + h • (Sa - Sy)‖
          ≤ ‖yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)‖
            + ‖h • (Sa - Sy)‖ := norm_add_le _ _
    linarith
  have h_h_Sd :
      ‖h • (Sa - Sy)‖ ≤ h * (∑ j : Fin s, |α j| * L
          * ‖yiter (n + (j : ℕ))
              - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)‖) := by
    rw [norm_smul, Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hSd_norm hh
  have hfinal :
      ‖yiter (n + s) - y (t₀ + ((n + s : ℕ) : ℝ) * h)‖
        ≤ ‖yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)‖
          + h * (∑ j : Fin s, |α j| * L
              * ‖yiter (n + (j : ℕ))
                  - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)‖)
          + ‖τ‖ := by
    linarith [htri, h_h_Sd]
  simpa [hyiter_def, hτ_def, Nat.cast_add] using hfinal

/-- AB8 vector iteration with eight starting samples. -/
noncomputable def ab8IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) : ℕ → E
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | 6 => y₆
  | 7 => y₇
  | n + 8 =>
      ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
        + h • ((434241 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7))
              - (1152169 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6))
              + (2183877 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5))
              - (2664477 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4))
              + (2102243 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3))
              - (1041723 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2))
              + (295767 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1))
              - (36799 / 120960 : ℝ) • f (t₀ + (n : ℝ) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n))

@[simp] lemma ab8IterVec_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 0 = y₀ := rfl

@[simp] lemma ab8IterVec_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 1 = y₁ := rfl

@[simp] lemma ab8IterVec_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 2 = y₂ := rfl

@[simp] lemma ab8IterVec_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 3 = y₃ := rfl

@[simp] lemma ab8IterVec_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 4 = y₄ := rfl

@[simp] lemma ab8IterVec_five
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 5 = y₅ := rfl

@[simp] lemma ab8IterVec_six
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 6 = y₆ := rfl

@[simp] lemma ab8IterVec_seven
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 7 = y₇ := rfl

lemma ab8IterVec_succ_eight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) (n : ℕ) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8)
      = ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
          + h • ((434241 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h)
                  (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7))
                - (1152169 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                    (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6))
                + (2183877 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                    (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5))
                - (2664477 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                    (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4))
                + (2102243 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                    (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3))
                - (1041723 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                    (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2))
                + (295767 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                    (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1))
                - (36799 / 120960 : ℝ) • f (t₀ + (n : ℝ) * h)
                    (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n)) := rfl

/-- Vector AB8 local truncation residual. -/
noncomputable def ab8VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 8 * h) - y (t + 7 * h)
    - h • ((434241 / 120960 : ℝ) • deriv y (t + 7 * h)
          - (1152169 / 120960 : ℝ) • deriv y (t + 6 * h)
          + (2183877 / 120960 : ℝ) • deriv y (t + 5 * h)
          - (2664477 / 120960 : ℝ) • deriv y (t + 4 * h)
          + (2102243 / 120960 : ℝ) • deriv y (t + 3 * h)
          - (1041723 / 120960 : ℝ) • deriv y (t + 2 * h)
          + (295767 / 120960 : ℝ) • deriv y (t + h)
          - (36799 / 120960 : ℝ) • deriv y t)

theorem ab8Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab8VecResidual h t y
      = y (t + 8 * h) - y (t + 7 * h)
          - h • ((434241 / 120960 : ℝ) • deriv y (t + 7 * h)
                - (1152169 / 120960 : ℝ) • deriv y (t + 6 * h)
                + (2183877 / 120960 : ℝ) • deriv y (t + 5 * h)
                - (2664477 / 120960 : ℝ) • deriv y (t + 4 * h)
                + (2102243 / 120960 : ℝ) • deriv y (t + 3 * h)
                - (1041723 / 120960 : ℝ) • deriv y (t + 2 * h)
                + (295767 / 120960 : ℝ) • deriv y (t + h)
                - (36799 / 120960 : ℝ) • deriv y t) := rfl

private lemma ab8IterVec_eq_abIterVec_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) (n : ℕ) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n
      = abIterVec 8 ab8GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 0 = _
      rw [ab8IterVec_zero]
      unfold abIterVec
      simp
    | 1 =>
      show ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 1 = _
      rw [ab8IterVec_one]
      unfold abIterVec
      simp
    | 2 =>
      show ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 2 = _
      rw [ab8IterVec_two]
      unfold abIterVec
      simp
    | 3 =>
      show ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 3 = _
      rw [ab8IterVec_three]
      unfold abIterVec
      simp
    | 4 =>
      show ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 4 = _
      rw [ab8IterVec_four]
      unfold abIterVec
      simp
    | 5 =>
      show ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 5 = _
      rw [ab8IterVec_five]
      unfold abIterVec
      simp
    | 6 =>
      show ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 6 = _
      rw [ab8IterVec_six]
      unfold abIterVec
      simp
    | 7 =>
      show ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 7 = _
      rw [ab8IterVec_seven]
      unfold abIterVec
      simp
    | k + 8 =>
      rw [ab8IterVec_succ_eight]
      rw [abIterVec_step (s := 8) (by norm_num)
          ab8GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇] k]
      rw [show (k + 8 - 1 : ℕ) = k + 7 from by omega]
      rw [Fin.sum_univ_eight]
      have hval3 : ((3 : Fin 8) : ℕ) = 3 := rfl
      have hval4 : ((4 : Fin 8) : ℕ) = 4 := rfl
      have hval5 : ((5 : Fin 8) : ℕ) = 5 := rfl
      have hval6 : ((6 : Fin 8) : ℕ) = 6 := rfl
      have hval7 : ((7 : Fin 8) : ℕ) = 7 := rfl
      simp only [ab8GenericCoeff_zero, ab8GenericCoeff_one, ab8GenericCoeff_two,
        ab8GenericCoeff_three, ab8GenericCoeff_four, ab8GenericCoeff_five,
        ab8GenericCoeff_six, ab8GenericCoeff_seven,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5, hval6,
        hval7, Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega), ← ih (k + 4) (by omega),
        ← ih (k + 5) (by omega), ← ih (k + 6) (by omega),
        ← ih (k + 7) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring,
        show ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 by push_cast; ring,
        show ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring,
        show ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 by push_cast; ring,
        show ((k + 7 : ℕ) : ℝ) = (k : ℝ) + 7 by push_cast; ring]
      rw [show (-(36799 : ℝ) / 120960) •
              f (t₀ + (k : ℝ) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ k)
            = -((36799 / 120960 : ℝ) •
              f (t₀ + (k : ℝ) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ k)) by
        rw [show (-(36799 : ℝ) / 120960) = -(36799 / 120960 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(1041723 : ℝ) / 120960) •
              f (t₀ + ((k : ℝ) + 2) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (k + 2))
            = -((1041723 / 120960 : ℝ) •
              f (t₀ + ((k : ℝ) + 2) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (k + 2))) by
        rw [show (-(1041723 : ℝ) / 120960) = -(1041723 / 120960 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(2664477 : ℝ) / 120960) •
              f (t₀ + ((k : ℝ) + 4) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (k + 4))
            = -((2664477 / 120960 : ℝ) •
              f (t₀ + ((k : ℝ) + 4) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (k + 4))) by
        rw [show (-(2664477 : ℝ) / 120960) = -(2664477 / 120960 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(1152169 : ℝ) / 120960) •
              f (t₀ + ((k : ℝ) + 6) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (k + 6))
            = -((1152169 / 120960 : ℝ) •
              f (t₀ + ((k : ℝ) + 6) * h)
                (ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (k + 6))) by
        rw [show (-(1152169 : ℝ) / 120960) = -(1152169 / 120960 : ℝ) by ring]
        exact neg_smul _ _]
      abel_nf

private lemma ab8VecResidual_eq_abResidualVec_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab8VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 8 ab8GenericCoeff h y t₀ n := by
  unfold ab8VecResidual abResidualVec
  rw [Fin.sum_univ_eight, ab8GenericCoeff_zero, ab8GenericCoeff_one,
    ab8GenericCoeff_two, ab8GenericCoeff_three, ab8GenericCoeff_four,
    ab8GenericCoeff_five, ab8GenericCoeff_six, ab8GenericCoeff_seven]
  have eA : t₀ + (n : ℝ) * h + 8 * h = t₀ + ((n + 8 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 7 * h = t₀ + ((n + 8 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 8 - 1 : ℕ) = n + 7 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 8) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 8) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 8) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 8) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  have eJ : t₀ + (n : ℝ) * h + 7 * h
      = t₀ + ((n + ((7 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((7 : Fin 8) : ℕ) = 7 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI, ← eJ]
  rw [show (-(36799 : ℝ) / 120960) • deriv y (t₀ + (n : ℝ) * h)
        = -((36799 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h)) by
    rw [show (-(36799 : ℝ) / 120960) = -(36799 / 120960 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(1041723 : ℝ) / 120960) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
        = -((1041723 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)) by
    rw [show (-(1041723 : ℝ) / 120960) = -(1041723 / 120960 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(2664477 : ℝ) / 120960) • deriv y (t₀ + (n : ℝ) * h + 4 * h)
        = -((2664477 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 4 * h)) by
    rw [show (-(2664477 : ℝ) / 120960) = -(2664477 / 120960 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(1152169 : ℝ) / 120960) • deriv y (t₀ + (n : ℝ) * h + 6 * h)
        = -((1152169 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 6 * h)) by
    rw [show (-(1152169 : ℝ) / 120960) = -(1152169 / 120960 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (434241 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 7 * h)
        - (1152169 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 6 * h)
        + (2183877 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 5 * h)
        - (2664477 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 4 * h)
        + (2102243 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h)
        - (1041723 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
        + (295767 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h)
        - (36799 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h)
        = -((36799 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h))
          + (295767 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h)
          + -((1041723 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h))
          + (2102243 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h)
          + -((2664477 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 4 * h))
          + (2183877 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 5 * h)
          + -((1152169 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 6 * h))
          + (434241 / 120960 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 7 * h) by abel_nf]

theorem ab8Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8)
        - y (t₀ + ((n : ℝ) + 8) * h)‖
      ≤ ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
            - y (t₀ + ((n : ℝ) + 7) * h)‖
        + (434241 / 120960) * h * L
            * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
                - y (t₀ + ((n : ℝ) + 7) * h)‖
        + (1152169 / 120960) * h * L
            * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6)
                - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (2183877 / 120960) * h * L
            * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (2664477 / 120960) * h * L
            * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (2102243 / 120960) * h * L
            * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (1041723 / 120960) * h * L
            * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (295767 / 120960) * h * L
            * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (36799 / 120960) * h * L
            * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n
                - y (t₀ + (n : ℝ) * h)‖
        + ‖ab8VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set y₀_oct : Fin 8 → E := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇] with hy_oct_def
  have hs : (1 : ℕ) ≤ 8 := by norm_num
  have hpoint :=
    abIterVec_lipschitz_pointwise (s := 8) hs ab8GenericCoeff (h := h) (L := L)
      hh hf t₀ y₀_oct y hyf n
  have hval3 : ((3 : Fin 8) : ℕ) = 3 := rfl
  have hval4 : ((4 : Fin 8) : ℕ) = 4 := rfl
  have hval5 : ((5 : Fin 8) : ℕ) = 5 := rfl
  have hval6 : ((6 : Fin 8) : ℕ) = 6 := rfl
  have hval7 : ((7 : Fin 8) : ℕ) = 7 := rfl
  rw [Fin.sum_univ_eight, ab8GenericCoeff_zero, ab8GenericCoeff_one,
    ab8GenericCoeff_two, ab8GenericCoeff_three, ab8GenericCoeff_four,
    ab8GenericCoeff_five, ab8GenericCoeff_six, ab8GenericCoeff_seven] at hpoint
  rw [show |(-(36799 : ℝ) / 120960)| = (36799 : ℝ) / 120960 by norm_num,
      show |((295767 : ℝ) / 120960)| = (295767 : ℝ) / 120960 by norm_num,
      show |(-(1041723 : ℝ) / 120960)| = (1041723 : ℝ) / 120960 by norm_num,
      show |((2102243 : ℝ) / 120960)| = (2102243 : ℝ) / 120960 by norm_num,
      show |(-(2664477 : ℝ) / 120960)| = (2664477 : ℝ) / 120960 by norm_num,
      show |((2183877 : ℝ) / 120960)| = (2183877 : ℝ) / 120960 by norm_num,
      show |(-(1152169 : ℝ) / 120960)| = (1152169 : ℝ) / 120960 by norm_num,
      show |((434241 : ℝ) / 120960)| = (434241 : ℝ) / 120960 by norm_num] at hpoint
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5,
    hval6, hval7, Nat.add_zero] at hpoint
  rw [show (n + 8 - 1 : ℕ) = n + 7 from by omega] at hpoint
  rw [← ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8),
    ← ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7),
    ← ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n,
    ← ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1),
    ← ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2),
    ← ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3),
    ← ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4),
    ← ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5),
    ← ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6),
    ← ab8VecResidual_eq_abResidualVec_aux (E := E) h y t₀ n] at hpoint
  rw [show ((n + 8 : ℕ) : ℝ) = (n : ℝ) + 8 by push_cast; ring,
    show ((n + 7 : ℕ) : ℝ) = (n : ℝ) + 7 by push_cast; ring,
    show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
    show ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 by push_cast; ring,
    show ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 by push_cast; ring,
    show ((n + 4 : ℕ) : ℝ) = (n : ℝ) + 4 by push_cast; ring,
    show ((n + 5 : ℕ) : ℝ) = (n : ℝ) + 5 by push_cast; ring,
    show ((n + 6 : ℕ) : ℝ) = (n : ℝ) + 6 by push_cast; ring] at hpoint
  convert hpoint using 1
  ring

theorem ab8Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max
          ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1)
              - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2)
              - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3)
              - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4)
              - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5)
              - y (t₀ + ((n : ℝ) + 5) * h)‖)
          ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6)
              - y (t₀ + ((n : ℝ) + 6) * h)‖)
          ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
              - y (t₀ + ((n : ℝ) + 7) * h)‖)
        ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8)
            - y (t₀ + ((n : ℝ) + 8) * h)‖
      ≤ (1 + h * ((77432 / 945) * L))
            * max (max (max (max (max (max (max
                  ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n
                      - y (t₀ + (n : ℝ) * h)‖
                  ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)‖)
                  ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)‖)
                  ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)‖)
                  ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)‖)
                  ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5)
                      - y (t₀ + ((n : ℝ) + 5) * h)‖)
                  ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6)
                      - y (t₀ + ((n : ℝ) + 6) * h)‖)
                  ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
                      - y (t₀ + ((n : ℝ) + 7) * h)‖
        + ‖ab8VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n
      - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1)
      - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2)
      - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set en3 : ℝ :=
    ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3)
      - y (t₀ + ((n : ℝ) + 3) * h)‖ with hen3_def
  set en4 : ℝ :=
    ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4)
      - y (t₀ + ((n : ℝ) + 4) * h)‖ with hen4_def
  set en5 : ℝ :=
    ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5)
      - y (t₀ + ((n : ℝ) + 5) * h)‖ with hen5_def
  set en6 : ℝ :=
    ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6)
      - y (t₀ + ((n : ℝ) + 6) * h)‖ with hen6_def
  set en7 : ℝ :=
    ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
      - y (t₀ + ((n : ℝ) + 7) * h)‖ with hen7_def
  set en8 : ℝ :=
    ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8)
      - y (t₀ + ((n : ℝ) + 8) * h)‖ with hen8_def
  set τabs : ℝ := ‖ab8VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hen4_nn : 0 ≤ en4 := norm_nonneg _
  have hen5_nn : 0 ≤ en5 := norm_nonneg _
  have hen6_nn : 0 ≤ en6 := norm_nonneg _
  have hen7_nn : 0 ≤ en7 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hstep :
      en8 ≤ en7 + (434241 / 120960) * h * L * en7
                + (1152169 / 120960) * h * L * en6
                + (2183877 / 120960) * h * L * en5
                + (2664477 / 120960) * h * L * en4
                + (2102243 / 120960) * h * L * en3
                + (1041723 / 120960) * h * L * en2
                + (295767 / 120960) * h * L * en1
                + (36799 / 120960) * h * L * en + τabs := by
    have := ab8Vec_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y hyf n
    show ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8)
          - y (t₀ + ((n : ℝ) + 8) * h)‖
        ≤ ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
            - y (t₀ + ((n : ℝ) + 7) * h)‖
          + (434241 / 120960) * h * L
              * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
                  - y (t₀ + ((n : ℝ) + 7) * h)‖
          + (1152169 / 120960) * h * L
              * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6)
                  - y (t₀ + ((n : ℝ) + 6) * h)‖
          + (2183877 / 120960) * h * L
              * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5)
                  - y (t₀ + ((n : ℝ) + 5) * h)‖
          + (2664477 / 120960) * h * L
              * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)‖
          + (2102243 / 120960) * h * L
              * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)‖
          + (1041723 / 120960) * h * L
              * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)‖
          + (295767 / 120960) * h * L
              * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)‖
          + (36799 / 120960) * h * L
              * ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n
                  - y (t₀ + (n : ℝ) * h)‖
          + ‖ab8VecResidual h (t₀ + (n : ℝ) * h) y‖
    exact this
  set EN_n : ℝ := max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7
    with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen5_le_EN : en5 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen6_le_EN : en6 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen7_le_EN : en7 ≤ EN_n := le_max_right _ _
  have h434241_nn : 0 ≤ (434241 / 120960) * h * L := by positivity
  have h1152169_nn : 0 ≤ (1152169 / 120960) * h * L := by positivity
  have h2183877_nn : 0 ≤ (2183877 / 120960) * h * L := by positivity
  have h2664477_nn : 0 ≤ (2664477 / 120960) * h * L := by positivity
  have h2102243_nn : 0 ≤ (2102243 / 120960) * h * L := by positivity
  have h1041723_nn : 0 ≤ (1041723 / 120960) * h * L := by positivity
  have h295767_nn : 0 ≤ (295767 / 120960) * h * L := by positivity
  have h36799_nn : 0 ≤ (36799 / 120960) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((77432 / 945) * L) := by positivity
  have hen8_bd : en8 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    have h1 : (434241 / 120960) * h * L * en7 ≤ (434241 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen7_le_EN h434241_nn
    have h2 : (1152169 / 120960) * h * L * en6 ≤ (1152169 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen6_le_EN h1152169_nn
    have h3 : (2183877 / 120960) * h * L * en5 ≤ (2183877 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen5_le_EN h2183877_nn
    have h4 : (2664477 / 120960) * h * L * en4 ≤ (2664477 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN h2664477_nn
    have h5 : (2102243 / 120960) * h * L * en3 ≤ (2102243 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN h2102243_nn
    have h6 : (1041723 / 120960) * h * L * en2 ≤ (1041723 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h1041723_nn
    have h7 : (295767 / 120960) * h * L * en1 ≤ (295767 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h295767_nn
    have h8 : (36799 / 120960) * h * L * en ≤ (36799 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h36799_nn
    have h_alg :
        EN_n + (434241 / 120960) * h * L * EN_n
              + (1152169 / 120960) * h * L * EN_n
              + (2183877 / 120960) * h * L * EN_n
              + (2664477 / 120960) * h * L * EN_n
              + (2102243 / 120960) * h * L * EN_n
              + (1041723 / 120960) * h * L * EN_n
              + (295767 / 120960) * h * L * EN_n
              + (36799 / 120960) * h * L * EN_n + τabs
          = (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen7_le_EN, h1, h2, h3, h4, h5, h6, h7, h8, h_alg.le]
  have hEN_le_grow : EN_n ≤ (1 + h * ((77432 / 945) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((77432 / 945) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  have hen5_bd : en5 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen5_le_EN, hEN_le_grow]
  have hen6_bd : en6 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen6_le_EN, hEN_le_grow]
  have hen7_bd : en7 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen7_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd)
    hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd

private lemma ab8Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7 dd ddd dddd ddddd dddddd ddddddd
      dddddddd : E) (h : ℝ) :
    y8 - y7 - h • ((434241 / 120960 : ℝ) • d7 - (1152169 / 120960 : ℝ) • d6
                  + (2183877 / 120960 : ℝ) • d5 - (2664477 / 120960 : ℝ) • d4
                  + (2102243 / 120960 : ℝ) • d3 - (1041723 / 120960 : ℝ) • d2
                  + (295767 / 120960 : ℝ) • d1 - (36799 / 120960 : ℝ) • d0)
      = (y8 - y0 - (8 * h) • d0
            - ((8 * h) ^ 2 / 2) • dd
            - ((8 * h) ^ 3 / 6) • ddd
            - ((8 * h) ^ 4 / 24) • dddd
            - ((8 * h) ^ 5 / 120) • ddddd
            - ((8 * h) ^ 6 / 720) • dddddd
            - ((8 * h) ^ 7 / 5040) • ddddddd
            - ((8 * h) ^ 8 / 40320) • dddddddd)
        - (y7 - y0 - (7 * h) • d0
            - ((7 * h) ^ 2 / 2) • dd
            - ((7 * h) ^ 3 / 6) • ddd
            - ((7 * h) ^ 4 / 24) • dddd
            - ((7 * h) ^ 5 / 120) • ddddd
            - ((7 * h) ^ 6 / 720) • dddddd
            - ((7 * h) ^ 7 / 5040) • ddddddd
            - ((7 * h) ^ 8 / 40320) • dddddddd)
        - (434241 * h / 120960 : ℝ)
            • (d7 - d0 - (7 * h) • dd
                - ((7 * h) ^ 2 / 2) • ddd
                - ((7 * h) ^ 3 / 6) • dddd
                - ((7 * h) ^ 4 / 24) • ddddd
                - ((7 * h) ^ 5 / 120) • dddddd
                - ((7 * h) ^ 6 / 720) • ddddddd
                - ((7 * h) ^ 7 / 5040) • dddddddd)
        + (1152169 * h / 120960 : ℝ)
            • (d6 - d0 - (6 * h) • dd
                - ((6 * h) ^ 2 / 2) • ddd
                - ((6 * h) ^ 3 / 6) • dddd
                - ((6 * h) ^ 4 / 24) • ddddd
                - ((6 * h) ^ 5 / 120) • dddddd
                - ((6 * h) ^ 6 / 720) • ddddddd
                - ((6 * h) ^ 7 / 5040) • dddddddd)
        - (2183877 * h / 120960 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd
                - ((5 * h) ^ 6 / 720) • ddddddd
                - ((5 * h) ^ 7 / 5040) • dddddddd)
        + (2664477 * h / 120960 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd
                - ((4 * h) ^ 6 / 720) • ddddddd
                - ((4 * h) ^ 7 / 5040) • dddddddd)
        - (2102243 * h / 120960 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd
                - ((3 * h) ^ 6 / 720) • ddddddd
                - ((3 * h) ^ 7 / 5040) • dddddddd)
        + (1041723 * h / 120960 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd
                - ((2 * h) ^ 6 / 720) • ddddddd
                - ((2 * h) ^ 7 / 5040) • dddddddd)
        - (295767 * h / 120960 : ℝ)
            • (d1 - d0 - h • dd
                - (h ^ 2 / 2) • ddd
                - (h ^ 3 / 6) • dddd
                - (h ^ 4 / 24) • ddddd
                - (h ^ 5 / 120) • dddddd
                - (h ^ 6 / 720) • ddddddd
                - (h ^ 7 / 5040) • dddddddd) := by
  simp only [smul_sub, smul_add, smul_smul]
  module

private lemma ab8Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 362880 * (8 * h) ^ 9 + M / 362880 * (7 * h) ^ 9
      + (434241 * h / 120960) * (M / 40320 * (7 * h) ^ 8)
      + (1152169 * h / 120960) * (M / 40320 * (6 * h) ^ 8)
      + (2183877 * h / 120960) * (M / 40320 * (5 * h) ^ 8)
      + (2664477 * h / 120960) * (M / 40320 * (4 * h) ^ 8)
      + (2102243 * h / 120960) * (M / 40320 * (3 * h) ^ 8)
      + (1041723 * h / 120960) * (M / 40320 * (2 * h) ^ 8)
      + (295767 * h / 120960) * (M / 40320 * h ^ 8)
      = (388219697 / 241920 : ℝ) * M * h ^ 9 := by
  ring

private lemma ab8Vec_residual_nine_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D G J K R S : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (434241 * h / 120960 : ℝ) • C + (1152169 * h / 120960 : ℝ) • D
        - (2183877 * h / 120960 : ℝ) • G + (2664477 * h / 120960 : ℝ) • J
        - (2102243 * h / 120960 : ℝ) • K + (1041723 * h / 120960 : ℝ) • R
        - (295767 * h / 120960 : ℝ) • S‖
      ≤ ‖A‖ + ‖B‖ + (434241 * h / 120960) * ‖C‖
          + (1152169 * h / 120960) * ‖D‖ + (2183877 * h / 120960) * ‖G‖
          + (2664477 * h / 120960) * ‖J‖ + (2102243 * h / 120960) * ‖K‖
          + (1041723 * h / 120960) * ‖R‖
          + (295767 * h / 120960) * ‖S‖ := by
  have h434241h_nn : 0 ≤ (434241 * h / 120960 : ℝ) := by linarith
  have h1152169h_nn : 0 ≤ (1152169 * h / 120960 : ℝ) := by linarith
  have h2183877h_nn : 0 ≤ (2183877 * h / 120960 : ℝ) := by linarith
  have h2664477h_nn : 0 ≤ (2664477 * h / 120960 : ℝ) := by linarith
  have h2102243h_nn : 0 ≤ (2102243 * h / 120960 : ℝ) := by linarith
  have h1041723h_nn : 0 ≤ (1041723 * h / 120960 : ℝ) := by linarith
  have h295767h_nn : 0 ≤ (295767 * h / 120960 : ℝ) := by linarith
  have hC_norm :
      ‖(434241 * h / 120960 : ℝ) • C‖ = (434241 * h / 120960) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg h434241h_nn]
  have hD_norm :
      ‖(1152169 * h / 120960 : ℝ) • D‖ = (1152169 * h / 120960) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg h1152169h_nn]
  have hG_norm :
      ‖(2183877 * h / 120960 : ℝ) • G‖ = (2183877 * h / 120960) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg h2183877h_nn]
  have hJ_norm :
      ‖(2664477 * h / 120960 : ℝ) • J‖ = (2664477 * h / 120960) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg h2664477h_nn]
  have hK_norm :
      ‖(2102243 * h / 120960 : ℝ) • K‖ = (2102243 * h / 120960) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg h2102243h_nn]
  have hR_norm :
      ‖(1041723 * h / 120960 : ℝ) • R‖ = (1041723 * h / 120960) * ‖R‖ := by
    rw [norm_smul, Real.norm_of_nonneg h1041723h_nn]
  have hS_norm :
      ‖(295767 * h / 120960 : ℝ) • S‖ = (295767 * h / 120960) * ‖S‖ := by
    rw [norm_smul, Real.norm_of_nonneg h295767h_nn]
  have h1 : ‖A - B - (434241 * h / 120960 : ℝ) • C
                + (1152169 * h / 120960 : ℝ) • D
                - (2183877 * h / 120960 : ℝ) • G
                + (2664477 * h / 120960 : ℝ) • J
                - (2102243 * h / 120960 : ℝ) • K
                + (1041723 * h / 120960 : ℝ) • R
                - (295767 * h / 120960 : ℝ) • S‖
      ≤ ‖A - B - (434241 * h / 120960 : ℝ) • C
            + (1152169 * h / 120960 : ℝ) • D
            - (2183877 * h / 120960 : ℝ) • G
            + (2664477 * h / 120960 : ℝ) • J
            - (2102243 * h / 120960 : ℝ) • K
            + (1041723 * h / 120960 : ℝ) • R‖
        + ‖(295767 * h / 120960 : ℝ) • S‖ := norm_sub_le _ _
  have h2 : ‖A - B - (434241 * h / 120960 : ℝ) • C
                + (1152169 * h / 120960 : ℝ) • D
                - (2183877 * h / 120960 : ℝ) • G
                + (2664477 * h / 120960 : ℝ) • J
                - (2102243 * h / 120960 : ℝ) • K
                + (1041723 * h / 120960 : ℝ) • R‖
      ≤ ‖A - B - (434241 * h / 120960 : ℝ) • C
            + (1152169 * h / 120960 : ℝ) • D
            - (2183877 * h / 120960 : ℝ) • G
            + (2664477 * h / 120960 : ℝ) • J
            - (2102243 * h / 120960 : ℝ) • K‖
        + ‖(1041723 * h / 120960 : ℝ) • R‖ := norm_add_le _ _
  have h3 : ‖A - B - (434241 * h / 120960 : ℝ) • C
                + (1152169 * h / 120960 : ℝ) • D
                - (2183877 * h / 120960 : ℝ) • G
                + (2664477 * h / 120960 : ℝ) • J
                - (2102243 * h / 120960 : ℝ) • K‖
      ≤ ‖A - B - (434241 * h / 120960 : ℝ) • C
            + (1152169 * h / 120960 : ℝ) • D
            - (2183877 * h / 120960 : ℝ) • G
            + (2664477 * h / 120960 : ℝ) • J‖
        + ‖(2102243 * h / 120960 : ℝ) • K‖ := norm_sub_le _ _
  have h4 : ‖A - B - (434241 * h / 120960 : ℝ) • C
                + (1152169 * h / 120960 : ℝ) • D
                - (2183877 * h / 120960 : ℝ) • G
                + (2664477 * h / 120960 : ℝ) • J‖
      ≤ ‖A - B - (434241 * h / 120960 : ℝ) • C
            + (1152169 * h / 120960 : ℝ) • D
            - (2183877 * h / 120960 : ℝ) • G‖
        + ‖(2664477 * h / 120960 : ℝ) • J‖ := norm_add_le _ _
  have h5 : ‖A - B - (434241 * h / 120960 : ℝ) • C
                + (1152169 * h / 120960 : ℝ) • D
                - (2183877 * h / 120960 : ℝ) • G‖
      ≤ ‖A - B - (434241 * h / 120960 : ℝ) • C
            + (1152169 * h / 120960 : ℝ) • D‖
        + ‖(2183877 * h / 120960 : ℝ) • G‖ := norm_sub_le _ _
  have h6 : ‖A - B - (434241 * h / 120960 : ℝ) • C
                + (1152169 * h / 120960 : ℝ) • D‖
      ≤ ‖A - B - (434241 * h / 120960 : ℝ) • C‖
        + ‖(1152169 * h / 120960 : ℝ) • D‖ := norm_add_le _ _
  have h7 : ‖A - B - (434241 * h / 120960 : ℝ) • C‖
      ≤ ‖A - B‖ + ‖(434241 * h / 120960 : ℝ) • C‖ := norm_sub_le _ _
  have h8 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith [hC_norm.le, hC_norm.ge, hD_norm.le, hD_norm.ge,
    hG_norm.le, hG_norm.ge, hJ_norm.le, hJ_norm.ge, hK_norm.le, hK_norm.ge,
    hR_norm.le, hR_norm.ge, hS_norm.le, hS_norm.ge]

private theorem ab8Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 9 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 9 y t‖ ≤ M)
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
        - h • ((434241 / 120960 : ℝ) • deriv y (t + 7 * h)
              - (1152169 / 120960 : ℝ) • deriv y (t + 6 * h)
              + (2183877 / 120960 : ℝ) • deriv y (t + 5 * h)
              - (2664477 / 120960 : ℝ) • deriv y (t + 4 * h)
              + (2102243 / 120960 : ℝ) • deriv y (t + 3 * h)
              - (1041723 / 120960 : ℝ) • deriv y (t + 2 * h)
              + (295767 / 120960 : ℝ) • deriv y (t + h)
              - (36799 / 120960 : ℝ) • deriv y t)‖
      ≤ (1605 : ℝ) * M * h ^ 9 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have hRy7 :=
    y_ninth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRy8 :=
    y_ninth_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRyp1 :=
    derivY_eighth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_eighth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_eighth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_eighth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_eighth_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_eighth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_eighth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
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
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  set ddddd : E := iteratedDeriv 5 y t with hddddd_def
  set dddddd : E := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd : E := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd : E := iteratedDeriv 8 y t with hdddddddd_def
  clear_value y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7
    dd ddd dddd ddddd dddddd ddddddd dddddddd
  have hLTE_eq :=
    ab8Vec_residual_alg_identity y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7
      dd ddd dddd ddddd dddddd ddddddd dddddddd h
  rw [hLTE_eq]
  set A : E := y8 - y0 - (8 * h) • d0
            - ((8 * h) ^ 2 / 2) • dd
            - ((8 * h) ^ 3 / 6) • ddd
            - ((8 * h) ^ 4 / 24) • dddd
            - ((8 * h) ^ 5 / 120) • ddddd
            - ((8 * h) ^ 6 / 720) • dddddd
            - ((8 * h) ^ 7 / 5040) • ddddddd
            - ((8 * h) ^ 8 / 40320) • dddddddd with hA_def
  set B : E := y7 - y0 - (7 * h) • d0
            - ((7 * h) ^ 2 / 2) • dd
            - ((7 * h) ^ 3 / 6) • ddd
            - ((7 * h) ^ 4 / 24) • dddd
            - ((7 * h) ^ 5 / 120) • ddddd
            - ((7 * h) ^ 6 / 720) • dddddd
            - ((7 * h) ^ 7 / 5040) • ddddddd
            - ((7 * h) ^ 8 / 40320) • dddddddd with hB_def
  set C : E := d7 - d0 - (7 * h) • dd
            - ((7 * h) ^ 2 / 2) • ddd
            - ((7 * h) ^ 3 / 6) • dddd
            - ((7 * h) ^ 4 / 24) • ddddd
            - ((7 * h) ^ 5 / 120) • dddddd
            - ((7 * h) ^ 6 / 720) • ddddddd
            - ((7 * h) ^ 7 / 5040) • dddddddd with hC_def
  set D : E := d6 - d0 - (6 * h) • dd
            - ((6 * h) ^ 2 / 2) • ddd
            - ((6 * h) ^ 3 / 6) • dddd
            - ((6 * h) ^ 4 / 24) • ddddd
            - ((6 * h) ^ 5 / 120) • dddddd
            - ((6 * h) ^ 6 / 720) • ddddddd
            - ((6 * h) ^ 7 / 5040) • dddddddd with hD_def
  set G : E := d5 - d0 - (5 * h) • dd
            - ((5 * h) ^ 2 / 2) • ddd
            - ((5 * h) ^ 3 / 6) • dddd
            - ((5 * h) ^ 4 / 24) • ddddd
            - ((5 * h) ^ 5 / 120) • dddddd
            - ((5 * h) ^ 6 / 720) • ddddddd
            - ((5 * h) ^ 7 / 5040) • dddddddd with hG_def
  set J : E := d4 - d0 - (4 * h) • dd
            - ((4 * h) ^ 2 / 2) • ddd
            - ((4 * h) ^ 3 / 6) • dddd
            - ((4 * h) ^ 4 / 24) • ddddd
            - ((4 * h) ^ 5 / 120) • dddddd
            - ((4 * h) ^ 6 / 720) • ddddddd
            - ((4 * h) ^ 7 / 5040) • dddddddd with hJ_def
  set K : E := d3 - d0 - (3 * h) • dd
            - ((3 * h) ^ 2 / 2) • ddd
            - ((3 * h) ^ 3 / 6) • dddd
            - ((3 * h) ^ 4 / 24) • ddddd
            - ((3 * h) ^ 5 / 120) • dddddd
            - ((3 * h) ^ 6 / 720) • ddddddd
            - ((3 * h) ^ 7 / 5040) • dddddddd with hK_def
  set R : E := d2 - d0 - (2 * h) • dd
            - ((2 * h) ^ 2 / 2) • ddd
            - ((2 * h) ^ 3 / 6) • dddd
            - ((2 * h) ^ 4 / 24) • ddddd
            - ((2 * h) ^ 5 / 120) • dddddd
            - ((2 * h) ^ 6 / 720) • ddddddd
            - ((2 * h) ^ 7 / 5040) • dddddddd with hR_def
  set S : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd
            - (h ^ 4 / 24) • ddddd
            - (h ^ 5 / 120) • dddddd
            - (h ^ 6 / 720) • ddddddd
            - (h ^ 7 / 5040) • dddddddd with hS_def
  clear_value A B C D G J K R S
  have h434241h_nn : 0 ≤ 434241 * h / 120960 := by linarith
  have h1152169h_nn : 0 ≤ 1152169 * h / 120960 := by linarith
  have h2183877h_nn : 0 ≤ 2183877 * h / 120960 := by linarith
  have h2664477h_nn : 0 ≤ 2664477 * h / 120960 := by linarith
  have h2102243h_nn : 0 ≤ 2102243 * h / 120960 := by linarith
  have h1041723h_nn : 0 ≤ 1041723 * h / 120960 := by linarith
  have h295767h_nn : 0 ≤ 295767 * h / 120960 := by linarith
  have htri := ab8Vec_residual_nine_term_triangle A B C D G J K R S h hh
  have hA_bd : ‖A‖ ≤ M / 362880 * (8 * h) ^ 9 := hRy8
  have hB_bd : ‖B‖ ≤ M / 362880 * (7 * h) ^ 9 := hRy7
  have hC_bd : ‖C‖ ≤ M / 40320 * (7 * h) ^ 8 := hRyp7
  have hD_bd : ‖D‖ ≤ M / 40320 * (6 * h) ^ 8 := hRyp6
  have hG_bd : ‖G‖ ≤ M / 40320 * (5 * h) ^ 8 := hRyp5
  have hJ_bd : ‖J‖ ≤ M / 40320 * (4 * h) ^ 8 := hRyp4
  have hK_bd : ‖K‖ ≤ M / 40320 * (3 * h) ^ 8 := hRyp3
  have hR_bd : ‖R‖ ≤ M / 40320 * (2 * h) ^ 8 := hRyp2
  have hS_bd : ‖S‖ ≤ M / 40320 * h ^ 8 := hRyp1
  have h434241C_bd : (434241 * h / 120960) * ‖C‖
      ≤ (434241 * h / 120960) * (M / 40320 * (7 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hC_bd h434241h_nn
  have h1152169D_bd : (1152169 * h / 120960) * ‖D‖
      ≤ (1152169 * h / 120960) * (M / 40320 * (6 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hD_bd h1152169h_nn
  have h2183877G_bd : (2183877 * h / 120960) * ‖G‖
      ≤ (2183877 * h / 120960) * (M / 40320 * (5 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hG_bd h2183877h_nn
  have h2664477J_bd : (2664477 * h / 120960) * ‖J‖
      ≤ (2664477 * h / 120960) * (M / 40320 * (4 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hJ_bd h2664477h_nn
  have h2102243K_bd : (2102243 * h / 120960) * ‖K‖
      ≤ (2102243 * h / 120960) * (M / 40320 * (3 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hK_bd h2102243h_nn
  have h1041723R_bd : (1041723 * h / 120960) * ‖R‖
      ≤ (1041723 * h / 120960) * (M / 40320 * (2 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hR_bd h1041723h_nn
  have h295767S_bd : (295767 * h / 120960) * ‖S‖
      ≤ (295767 * h / 120960) * (M / 40320 * h ^ 8) :=
    mul_le_mul_of_nonneg_left hS_bd h295767h_nn
  have hbound_alg := ab8Vec_residual_bound_alg_identity M h
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  have hh9_nn : 0 ≤ h ^ 9 := by positivity
  have hMh9_nn : 0 ≤ M * h ^ 9 := mul_nonneg hMnn hh9_nn
  have hslack : (388219697 / 241920 : ℝ) * M * h ^ 9 ≤ 1605 * M * h ^ 9 := by
    rw [mul_assoc, mul_assoc (1605 : ℝ)]
    have hle : (388219697 / 241920 : ℝ) ≤ 1605 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh9_nn
  calc
    ‖A - B - (434241 * h / 120960 : ℝ) • C
          + (1152169 * h / 120960 : ℝ) • D
          - (2183877 * h / 120960 : ℝ) • G
          + (2664477 * h / 120960 : ℝ) • J
          - (2102243 * h / 120960 : ℝ) • K
          + (1041723 * h / 120960 : ℝ) • R
          - (295767 * h / 120960 : ℝ) • S‖
      ≤ ‖A‖ + ‖B‖ + (434241 * h / 120960) * ‖C‖
          + (1152169 * h / 120960) * ‖D‖
          + (2183877 * h / 120960) * ‖G‖
          + (2664477 * h / 120960) * ‖J‖
          + (2102243 * h / 120960) * ‖K‖
          + (1041723 * h / 120960) * ‖R‖
          + (295767 * h / 120960) * ‖S‖ := htri
    _ ≤ M / 362880 * (8 * h) ^ 9 + M / 362880 * (7 * h) ^ 9
          + (434241 * h / 120960) * (M / 40320 * (7 * h) ^ 8)
          + (1152169 * h / 120960) * (M / 40320 * (6 * h) ^ 8)
          + (2183877 * h / 120960) * (M / 40320 * (5 * h) ^ 8)
          + (2664477 * h / 120960) * (M / 40320 * (4 * h) ^ 8)
          + (2102243 * h / 120960) * (M / 40320 * (3 * h) ^ 8)
          + (1041723 * h / 120960) * (M / 40320 * (2 * h) ^ 8)
          + (295767 * h / 120960) * (M / 40320 * h ^ 8) := by
        linarith [hA_bd, hB_bd, h434241C_bd, h1152169D_bd, h2183877G_bd,
          h2664477J_bd, h2102243K_bd, h1041723R_bd, h295767S_bd]
    _ = (388219697 / 241920 : ℝ) * M * h ^ 9 := hbound_alg
    _ ≤ 1605 * M * h ^ 9 := hslack

theorem ab8Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 9 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 8) * h ≤ T →
        ‖ab8VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 9 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_nine_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(1605 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
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
  show ‖ab8VecResidual h t y‖ ≤ 1605 * M * h ^ 9
  unfold ab8VecResidual
  exact ab8Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem hh.le

lemma ab8IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E) (n : ℕ) :
    ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n
      = abIterVec 8 ab8GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇] n := by
  exact ab8IterVec_eq_abIterVec_aux h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n

lemma ab8VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab8VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 8 ab8GenericCoeff h y t₀ n := by
  exact ab8VecResidual_eq_abResidualVec_aux h y t₀ n

theorem ab8Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 9 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
      ‖y₀ - y t₀‖ ≤ ε₀ → ‖y₁ - y (t₀ + h)‖ ≤ ε₀ →
      ‖y₂ - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖y₃ - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖y₄ - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖y₅ - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖y₆ - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ‖y₇ - y (t₀ + 7 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 7) * h ≤ T →
      ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((77432 / 945) * L * T) * ε₀ + K * h ^ 8 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab8Vec_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((77432 / 945) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd N hNh
  set α : Fin 8 → ℝ := ab8GenericCoeff with hα_def
  set y₀_oct : Fin 8 → E := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇] with hy_oct_def
  have hs : (1 : ℕ) ≤ 8 := by norm_num
  haveI : Nonempty (Fin 8) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIterVec 8 α h f t₀ y₀_oct 0 = y₀ := by
    unfold abIterVec
    simp [hy_oct_def]
  have hiter1 : abIterVec 8 α h f t₀ y₀_oct 1 = y₁ := by
    unfold abIterVec
    simp [hy_oct_def]
  have hiter2 : abIterVec 8 α h f t₀ y₀_oct 2 = y₂ := by
    unfold abIterVec
    simp [hy_oct_def]
  have hiter3 : abIterVec 8 α h f t₀ y₀_oct 3 = y₃ := by
    unfold abIterVec
    simp [hy_oct_def]
  have hiter4 : abIterVec 8 α h f t₀ y₀_oct 4 = y₄ := by
    unfold abIterVec
    simp [hy_oct_def]
  have hiter5 : abIterVec 8 α h f t₀ y₀_oct 5 = y₅ := by
    unfold abIterVec
    simp [hy_oct_def]
  have hiter6 : abIterVec 8 α h f t₀ y₀_oct 6 = y₆ := by
    unfold abIterVec
    simp [hy_oct_def]
  have hiter7 : abIterVec 8 α h f t₀ y₀_oct 7 = y₇ := by
    unfold abIterVec
    simp [hy_oct_def]
  have hstart : abErrWindowVec hs α h f t₀ y₀_oct y 0 ≤ ε₀ := by
    unfold abErrWindowVec
    apply Finset.sup'_le
    intro j _
    show abErrVec 8 α h f t₀ y₀_oct y (0 + (j : ℕ)) ≤ ε₀
    unfold abErrVec
    fin_cases j
    · show ‖abIterVec 8 α h f t₀ y₀_oct 0
          - y (t₀ + ((0 + (((0 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]
      exact he0_bd
    · show ‖abIterVec 8 α h f t₀ y₀_oct 1
          - y (t₀ + ((0 + (((1 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]
      exact he1_bd
    · show ‖abIterVec 8 α h f t₀ y₀_oct 2
          - y (t₀ + ((0 + (((2 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]
      exact he2_bd
    · show ‖abIterVec 8 α h f t₀ y₀_oct 3
          - y (t₀ + ((0 + (((3 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 8) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]
      exact he3_bd
    · show ‖abIterVec 8 α h f t₀ y₀_oct 4
          - y (t₀ + ((0 + (((4 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter4]
      have hval4 : ((4 : Fin 8) : ℕ) = 4 := rfl
      have : ((0 + (((4 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval4]; push_cast; ring
      rw [this]
      exact he4_bd
    · show ‖abIterVec 8 α h f t₀ y₀_oct 5
          - y (t₀ + ((0 + (((5 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter5]
      have hval5 : ((5 : Fin 8) : ℕ) = 5 := rfl
      have : ((0 + (((5 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval5]; push_cast; ring
      rw [this]
      exact he5_bd
    · show ‖abIterVec 8 α h f t₀ y₀_oct 6
          - y (t₀ + ((0 + (((6 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter6]
      have hval6 : ((6 : Fin 8) : ℕ) = 6 := rfl
      have : ((0 + (((6 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 6 := by
        rw [hval6]; push_cast; ring
      rw [this]
      exact he6_bd
    · show ‖abIterVec 8 α h f t₀ y₀_oct 7
          - y (t₀ + ((0 + (((7 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter7]
      have hval7 : ((7 : Fin 8) : ℕ) = 7 := rfl
      have : ((0 + (((7 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 7 := by
        rw [hval7]; push_cast; ring
      rw [this]
      exact he7_bd
  have hres_gen : ∀ n : ℕ, n < N →
      ‖abResidualVec 8 α h y t₀ n‖ ≤ C * h ^ (8 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 8 ≤ (N : ℝ) + 7 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn8_le : ((n : ℝ) + 8) * h ≤ T := by
      have hmul : ((n : ℝ) + 8) * h ≤ ((N : ℝ) + 7) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn8_le
    have hbridge :=
      ab8VecResidual_eq_abResidualVec (E := E) h y t₀ n
    have hpow : C * h ^ (8 + 1) = C * h ^ 9 := by norm_num
    rw [hα_def, ← hbridge]
    linarith [hres, hpow.symm.le, hpow.le]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 7) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 7 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic_vec (p := 8) hs α hh.le hL hC_nn hf t₀
      y₀_oct y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 8 α L = (77432 / 945) * L from by
    rw [hα_def]
    exact abLip_ab8GenericCoeff L] at hgeneric
  have hwindow_ge : abErrVec 8 α h f t₀ y₀_oct y N
      ≤ abErrWindowVec hs α h f t₀ y₀_oct y N := by
    show abErrVec 8 α h f t₀ y₀_oct y (N + ((⟨0, hs⟩ : Fin 8) : ℕ))
        ≤ abErrWindowVec hs α h f t₀ y₀_oct y N
    unfold abErrWindowVec
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 8 => abErrVec 8 α h f t₀ y₀_oct y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIterVec 8 α h f t₀ y₀_oct N
        = ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N := by
    rw [hα_def, hy_oct_def]
    exact (ab8IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N).symm
  have habsErr :
      abErrVec 8 α h f t₀ y₀_oct y N
        = ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N
            - y (t₀ + (N : ℝ) * h)‖ := by
    show ‖abIterVec 8 α h f t₀ y₀_oct N - y (t₀ + (N : ℝ) * h)‖
        = ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N
            - y (t₀ + (N : ℝ) * h)‖
    rw [hbridge]
  show ‖ab8IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N
          - y (t₀ + (N : ℝ) * h)‖
      ≤ Real.exp ((77432 / 945) * L * T) * ε₀
        + T * Real.exp ((77432 / 945) * L * T) * C * h ^ 8
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
