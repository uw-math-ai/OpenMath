import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB9Convergence
import OpenMath.LMMAM8VectorConvergence

/-! ## Adams-Bashforth 9-step Vector Quantitative Convergence Chain (Iserles §1.2)

Finite-dimensional vector-valued analogue of the scalar AB9 quantitative
convergence chain in `OpenMath.LMMAB9Convergence`.
-/

namespace LMM

/-- Helper: expand `∑ i : Fin 9, f i` as nine summands. -/
private lemma sum_univ_nine_aux {α : Type*} [AddCommMonoid α] (f : Fin 9 → α) :
    ∑ i : Fin 9, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

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

/-- AB9 vector iteration with nine starting samples. -/
noncomputable def ab9IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) : ℕ → E
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | 6 => y₆
  | 7 => y₇
  | 8 => y₈
  | n + 9 =>
      ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
        + h • ((14097247 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8))
              - (43125206 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7))
              + (95476786 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6))
              - (139855262 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5))
              + (137968480 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4))
              - (91172642 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3))
              + (38833486 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2))
              - (9664106 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1))
              + (1070017 / 3628800 : ℝ) • f (t₀ + (n : ℝ) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n))

@[simp] lemma ab9IterVec_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 0 = y₀ := rfl

@[simp] lemma ab9IterVec_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 1 = y₁ := rfl

@[simp] lemma ab9IterVec_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 2 = y₂ := rfl

@[simp] lemma ab9IterVec_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 3 = y₃ := rfl

@[simp] lemma ab9IterVec_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 4 = y₄ := rfl

@[simp] lemma ab9IterVec_five
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 5 = y₅ := rfl

@[simp] lemma ab9IterVec_six
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 6 = y₆ := rfl

@[simp] lemma ab9IterVec_seven
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 7 = y₇ := rfl

@[simp] lemma ab9IterVec_eight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 8 = y₈ := rfl

lemma ab9IterVec_succ_nine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) (n : ℕ) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9)
      = ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
        + h • ((14097247 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8))
              - (43125206 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7))
              + (95476786 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6))
              - (139855262 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5))
              + (137968480 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4))
              - (91172642 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3))
              + (38833486 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2))
              - (9664106 / 3628800 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1))
              + (1070017 / 3628800 : ℝ) • f (t₀ + (n : ℝ) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n)) := rfl

/-- Vector AB9 local truncation residual. -/
noncomputable def ab9VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 9 * h) - y (t + 8 * h)
    - h • ((14097247 / 3628800 : ℝ) • deriv y (t + 8 * h)
          - (43125206 / 3628800 : ℝ) • deriv y (t + 7 * h)
          + (95476786 / 3628800 : ℝ) • deriv y (t + 6 * h)
          - (139855262 / 3628800 : ℝ) • deriv y (t + 5 * h)
          + (137968480 / 3628800 : ℝ) • deriv y (t + 4 * h)
          - (91172642 / 3628800 : ℝ) • deriv y (t + 3 * h)
          + (38833486 / 3628800 : ℝ) • deriv y (t + 2 * h)
          - (9664106 / 3628800 : ℝ) • deriv y (t + h)
          + (1070017 / 3628800 : ℝ) • deriv y t)

theorem ab9Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab9VecResidual h t y
      = y (t + 9 * h) - y (t + 8 * h)
          - h • ((14097247 / 3628800 : ℝ) • deriv y (t + 8 * h)
                - (43125206 / 3628800 : ℝ) • deriv y (t + 7 * h)
                + (95476786 / 3628800 : ℝ) • deriv y (t + 6 * h)
                - (139855262 / 3628800 : ℝ) • deriv y (t + 5 * h)
                + (137968480 / 3628800 : ℝ) • deriv y (t + 4 * h)
                - (91172642 / 3628800 : ℝ) • deriv y (t + 3 * h)
                + (38833486 / 3628800 : ℝ) • deriv y (t + 2 * h)
                - (9664106 / 3628800 : ℝ) • deriv y (t + h)
                + (1070017 / 3628800 : ℝ) • deriv y t) := rfl

lemma ab9IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) (n : ℕ) :
    ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n
      = abIterVec 9 ab9GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 0 = _
      rw [ab9IterVec_zero]
      unfold abIterVec
      simp
    | 1 =>
      show ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 1 = _
      rw [ab9IterVec_one]
      unfold abIterVec
      simp
    | 2 =>
      show ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 2 = _
      rw [ab9IterVec_two]
      unfold abIterVec
      simp
    | 3 =>
      show ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 3 = _
      rw [ab9IterVec_three]
      unfold abIterVec
      simp
    | 4 =>
      show ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 4 = _
      rw [ab9IterVec_four]
      unfold abIterVec
      simp
    | 5 =>
      show ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 5 = _
      rw [ab9IterVec_five]
      unfold abIterVec
      simp
    | 6 =>
      show ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 6 = _
      rw [ab9IterVec_six]
      unfold abIterVec
      simp
    | 7 =>
      show ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 7 = _
      rw [ab9IterVec_seven]
      unfold abIterVec
      simp
    | 8 =>
      show ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 8 = _
      rw [ab9IterVec_eight]
      unfold abIterVec
      simp
    | k + 9 =>
      rw [ab9IterVec_succ_nine]
      rw [abIterVec_step (s := 9) (by norm_num)
          ab9GenericCoeff h f t₀
            ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈] k]
      rw [show (k + 9 - 1 : ℕ) = k + 8 from by omega]
      rw [sum_univ_nine_aux]
      have hval3 : ((3 : Fin 9) : ℕ) = 3 := rfl
      have hval4 : ((4 : Fin 9) : ℕ) = 4 := rfl
      have hval5 : ((5 : Fin 9) : ℕ) = 5 := rfl
      have hval6 : ((6 : Fin 9) : ℕ) = 6 := rfl
      have hval7 : ((7 : Fin 9) : ℕ) = 7 := rfl
      have hval8 : ((8 : Fin 9) : ℕ) = 8 := rfl
      simp only [ab9GenericCoeff_zero, ab9GenericCoeff_one, ab9GenericCoeff_two,
        ab9GenericCoeff_three, ab9GenericCoeff_four, ab9GenericCoeff_five,
        ab9GenericCoeff_six, ab9GenericCoeff_seven, ab9GenericCoeff_eight,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5, hval6,
        hval7, hval8, Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega), ← ih (k + 4) (by omega),
        ← ih (k + 5) (by omega), ← ih (k + 6) (by omega),
        ← ih (k + 7) (by omega), ← ih (k + 8) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring,
        show ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 by push_cast; ring,
        show ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring,
        show ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 by push_cast; ring,
        show ((k + 7 : ℕ) : ℝ) = (k : ℝ) + 7 by push_cast; ring,
        show ((k + 8 : ℕ) : ℝ) = (k : ℝ) + 8 by push_cast; ring]
      rw [show (-(9664106 : ℝ) / 3628800) •
              f (t₀ + ((k : ℝ) + 1) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (k + 1))
            = -((9664106 / 3628800 : ℝ) •
              f (t₀ + ((k : ℝ) + 1) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (k + 1))) by
        rw [show (-(9664106 : ℝ) / 3628800) = -(9664106 / 3628800 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(91172642 : ℝ) / 3628800) •
              f (t₀ + ((k : ℝ) + 3) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (k + 3))
            = -((91172642 / 3628800 : ℝ) •
              f (t₀ + ((k : ℝ) + 3) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (k + 3))) by
        rw [show (-(91172642 : ℝ) / 3628800) = -(91172642 / 3628800 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(139855262 : ℝ) / 3628800) •
              f (t₀ + ((k : ℝ) + 5) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (k + 5))
            = -((139855262 / 3628800 : ℝ) •
              f (t₀ + ((k : ℝ) + 5) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (k + 5))) by
        rw [show (-(139855262 : ℝ) / 3628800) = -(139855262 / 3628800 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(43125206 : ℝ) / 3628800) •
              f (t₀ + ((k : ℝ) + 7) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (k + 7))
            = -((43125206 / 3628800 : ℝ) •
              f (t₀ + ((k : ℝ) + 7) * h)
                (ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (k + 7))) by
        rw [show (-(43125206 : ℝ) / 3628800) = -(43125206 / 3628800 : ℝ) by ring]
        exact neg_smul _ _]
      abel_nf

lemma ab9VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab9VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 9 ab9GenericCoeff h y t₀ n := by
  unfold ab9VecResidual abResidualVec
  rw [sum_univ_nine_aux, ab9GenericCoeff_zero, ab9GenericCoeff_one,
    ab9GenericCoeff_two, ab9GenericCoeff_three, ab9GenericCoeff_four,
    ab9GenericCoeff_five, ab9GenericCoeff_six, ab9GenericCoeff_seven,
    ab9GenericCoeff_eight]
  have eA : t₀ + (n : ℝ) * h + 9 * h = t₀ + ((n + 9 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 8 * h = t₀ + ((n + 9 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 9 - 1 : ℕ) = n + 8 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 9) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 9) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 9) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 9) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  have eJ : t₀ + (n : ℝ) * h + 7 * h
      = t₀ + ((n + ((7 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((7 : Fin 9) : ℕ) = 7 := rfl
    rw [this]; push_cast; ring
  have eK : t₀ + (n : ℝ) * h + 8 * h
      = t₀ + ((n + ((8 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((8 : Fin 9) : ℕ) = 8 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI, ← eJ, ← eK]
  rw [show (-(9664106 : ℝ) / 3628800) • deriv y (t₀ + (n : ℝ) * h + h)
        = -((9664106 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h)) by
    rw [show (-(9664106 : ℝ) / 3628800) = -(9664106 / 3628800 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(91172642 : ℝ) / 3628800) • deriv y (t₀ + (n : ℝ) * h + 3 * h)
        = -((91172642 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h)) by
    rw [show (-(91172642 : ℝ) / 3628800) = -(91172642 / 3628800 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(139855262 : ℝ) / 3628800) • deriv y (t₀ + (n : ℝ) * h + 5 * h)
        = -((139855262 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 5 * h)) by
    rw [show (-(139855262 : ℝ) / 3628800) = -(139855262 / 3628800 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(43125206 : ℝ) / 3628800) • deriv y (t₀ + (n : ℝ) * h + 7 * h)
        = -((43125206 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 7 * h)) by
    rw [show (-(43125206 : ℝ) / 3628800) = -(43125206 / 3628800 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (14097247 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 8 * h)
        - (43125206 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 7 * h)
        + (95476786 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 6 * h)
        - (139855262 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 5 * h)
        + (137968480 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 4 * h)
        - (91172642 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h)
        + (38833486 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
        - (9664106 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h)
        + (1070017 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h)
        = (1070017 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h)
          + -((9664106 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h))
          + (38833486 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
          + -((91172642 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h))
          + (137968480 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 4 * h)
          + -((139855262 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 5 * h))
          + (95476786 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 6 * h)
          + -((43125206 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 7 * h))
          + (14097247 / 3628800 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 8 * h) by
    abel_nf]

theorem ab9Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9)
        - y (t₀ + ((n : ℝ) + 9) * h)‖
      ≤ ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
            - y (t₀ + ((n : ℝ) + 8) * h)‖
        + (14097247 / 3628800) * h * L
            * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
                - y (t₀ + ((n : ℝ) + 8) * h)‖
        + (43125206 / 3628800) * h * L
            * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7)
                - y (t₀ + ((n : ℝ) + 7) * h)‖
        + (95476786 / 3628800) * h * L
            * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6)
                - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (139855262 / 3628800) * h * L
            * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (137968480 / 3628800) * h * L
            * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (91172642 / 3628800) * h * L
            * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (38833486 / 3628800) * h * L
            * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (9664106 / 3628800) * h * L
            * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (1070017 / 3628800) * h * L
            * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n
                - y (t₀ + (n : ℝ) * h)‖
        + ‖ab9VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set y₀_non : Fin 9 → E := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈]
    with hy_non_def
  have hs : (1 : ℕ) ≤ 9 := by norm_num
  have hpoint :=
    abIterVec_lipschitz_pointwise (s := 9) hs ab9GenericCoeff (h := h) (L := L)
      hh hf t₀ y₀_non y hyf n
  have hval3 : ((3 : Fin 9) : ℕ) = 3 := rfl
  have hval4 : ((4 : Fin 9) : ℕ) = 4 := rfl
  have hval5 : ((5 : Fin 9) : ℕ) = 5 := rfl
  have hval6 : ((6 : Fin 9) : ℕ) = 6 := rfl
  have hval7 : ((7 : Fin 9) : ℕ) = 7 := rfl
  have hval8 : ((8 : Fin 9) : ℕ) = 8 := rfl
  rw [sum_univ_nine_aux, ab9GenericCoeff_zero, ab9GenericCoeff_one,
    ab9GenericCoeff_two, ab9GenericCoeff_three, ab9GenericCoeff_four,
    ab9GenericCoeff_five, ab9GenericCoeff_six, ab9GenericCoeff_seven,
    ab9GenericCoeff_eight] at hpoint
  rw [show |((1070017 : ℝ) / 3628800)| = (1070017 : ℝ) / 3628800 by norm_num,
      show |(-(9664106 : ℝ) / 3628800)| = (9664106 : ℝ) / 3628800 by norm_num,
      show |((38833486 : ℝ) / 3628800)| = (38833486 : ℝ) / 3628800 by norm_num,
      show |(-(91172642 : ℝ) / 3628800)| = (91172642 : ℝ) / 3628800 by norm_num,
      show |((137968480 : ℝ) / 3628800)| = (137968480 : ℝ) / 3628800 by norm_num,
      show |(-(139855262 : ℝ) / 3628800)| = (139855262 : ℝ) / 3628800 by norm_num,
      show |((95476786 : ℝ) / 3628800)| = (95476786 : ℝ) / 3628800 by norm_num,
      show |(-(43125206 : ℝ) / 3628800)| = (43125206 : ℝ) / 3628800 by norm_num,
      show |((14097247 : ℝ) / 3628800)| = (14097247 : ℝ) / 3628800 by norm_num] at hpoint
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5,
    hval6, hval7, hval8, Nat.add_zero] at hpoint
  rw [show (n + 9 - 1 : ℕ) = n + 8 from by omega] at hpoint
  rw [← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9),
    ← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8),
    ← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n,
    ← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1),
    ← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2),
    ← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3),
    ← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4),
    ← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5),
    ← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6),
    ← ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7),
    ← ab9VecResidual_eq_abResidualVec (E := E) h y t₀ n] at hpoint
  rw [show ((n + 9 : ℕ) : ℝ) = (n : ℝ) + 9 by push_cast; ring,
    show ((n + 8 : ℕ) : ℝ) = (n : ℝ) + 8 by push_cast; ring,
    show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
    show ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 by push_cast; ring,
    show ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 by push_cast; ring,
    show ((n + 4 : ℕ) : ℝ) = (n : ℝ) + 4 by push_cast; ring,
    show ((n + 5 : ℕ) : ℝ) = (n : ℝ) + 5 by push_cast; ring,
    show ((n + 6 : ℕ) : ℝ) = (n : ℝ) + 6 by push_cast; ring,
    show ((n + 7 : ℕ) : ℝ) = (n : ℝ) + 7 by push_cast; ring] at hpoint
  convert hpoint using 1
  ring

theorem ab9Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max (max
          ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1)
              - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2)
              - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3)
              - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4)
              - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5)
              - y (t₀ + ((n : ℝ) + 5) * h)‖)
          ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6)
              - y (t₀ + ((n : ℝ) + 6) * h)‖)
          ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7)
              - y (t₀ + ((n : ℝ) + 7) * h)‖)
          ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
              - y (t₀ + ((n : ℝ) + 8) * h)‖)
        ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9)
            - y (t₀ + ((n : ℝ) + 9) * h)‖
      ≤ (1 + h * ((2231497 / 14175) * L))
            * max (max (max (max (max (max (max (max
                  ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n
                      - y (t₀ + (n : ℝ) * h)‖
                  ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)‖)
                  ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)‖)
                  ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)‖)
                  ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)‖)
                  ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5)
                      - y (t₀ + ((n : ℝ) + 5) * h)‖)
                  ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6)
                      - y (t₀ + ((n : ℝ) + 6) * h)‖)
                  ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7)
                      - y (t₀ + ((n : ℝ) + 7) * h)‖)
                  ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
                      - y (t₀ + ((n : ℝ) + 8) * h)‖
        + ‖ab9VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n - y (t₀ + (n : ℝ) * h)‖
    with hen_def
  set en1 : ℝ :=
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
    with hen1_def
  set en2 : ℝ :=
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
    with hen2_def
  set en3 : ℝ :=
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
    with hen3_def
  set en4 : ℝ :=
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖
    with hen4_def
  set en5 : ℝ :=
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
    with hen5_def
  set en6 : ℝ :=
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
    with hen6_def
  set en7 : ℝ :=
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
    with hen7_def
  set en8 : ℝ :=
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
    with hen8_def
  set en9 : ℝ :=
    ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
    with hen9_def
  set τabs : ℝ :=
    ‖ab9VecResidual h (t₀ + (n : ℝ) * h) y‖
    with hτabs_def
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
  -- One-step Lipschitz bound (from `ab9Vec_one_step_lipschitz`).
  have hstep :
      en9 ≤ en8 + (14097247 / 3628800) * h * L * en8
                + (43125206 / 3628800) * h * L * en7
                + (95476786 / 3628800) * h * L * en6
                + (139855262 / 3628800) * h * L * en5
                + (137968480 / 3628800) * h * L * en4
                + (91172642 / 3628800) * h * L * en3
                + (38833486 / 3628800) * h * L * en2
                + (9664106 / 3628800) * h * L * en1
                + (1070017 / 3628800) * h * L * en + τabs := by
    have := ab9Vec_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y hyf n
    show ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
        ≤ ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
          + (14097247 / 3628800) * h * L
              * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
                  - y (t₀ + ((n : ℝ) + 8) * h)‖
          + (43125206 / 3628800) * h * L
              * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7)
                  - y (t₀ + ((n : ℝ) + 7) * h)‖
          + (95476786 / 3628800) * h * L
              * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6)
                  - y (t₀ + ((n : ℝ) + 6) * h)‖
          + (139855262 / 3628800) * h * L
              * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5)
                  - y (t₀ + ((n : ℝ) + 5) * h)‖
          + (137968480 / 3628800) * h * L
              * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)‖
          + (91172642 / 3628800) * h * L
              * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)‖
          + (38833486 / 3628800) * h * L
              * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)‖
          + (9664106 / 3628800) * h * L
              * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)‖
          + (1070017 / 3628800) * h * L
              * ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n - y (t₀ + (n : ℝ) * h)‖
          + ‖ab9VecResidual h (t₀ + (n : ℝ) * h) y‖
    exact this
  set EN_n : ℝ :=
    max (max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7) en8
    with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)
  have hen5_le_EN : en5 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen6_le_EN : en6 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen7_le_EN : en7 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen8_le_EN : en8 ≤ EN_n := le_max_right _ _
  have hc8_nn : 0 ≤ (14097247 / 3628800) * h * L := by positivity
  have hc7_nn : 0 ≤ (43125206 / 3628800) * h * L := by positivity
  have hc6_nn : 0 ≤ (95476786 / 3628800) * h * L := by positivity
  have hc5_nn : 0 ≤ (139855262 / 3628800) * h * L := by positivity
  have hc4_nn : 0 ≤ (137968480 / 3628800) * h * L := by positivity
  have hc3_nn : 0 ≤ (91172642 / 3628800) * h * L := by positivity
  have hc2_nn : 0 ≤ (38833486 / 3628800) * h * L := by positivity
  have hc1_nn : 0 ≤ (9664106 / 3628800) * h * L := by positivity
  have hc0_nn : 0 ≤ (1070017 / 3628800) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((2231497 / 14175) * L) := by positivity
  have hen9_bd : en9 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    have h1 : (14097247 / 3628800) * h * L * en8 ≤ (14097247 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen8_le_EN hc8_nn
    have h2 : (43125206 / 3628800) * h * L * en7 ≤ (43125206 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen7_le_EN hc7_nn
    have h3 : (95476786 / 3628800) * h * L * en6 ≤ (95476786 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen6_le_EN hc6_nn
    have h4 : (139855262 / 3628800) * h * L * en5 ≤ (139855262 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen5_le_EN hc5_nn
    have h5 : (137968480 / 3628800) * h * L * en4 ≤ (137968480 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN hc4_nn
    have h6 : (91172642 / 3628800) * h * L * en3 ≤ (91172642 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN hc3_nn
    have h7 : (38833486 / 3628800) * h * L * en2 ≤ (38833486 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN hc2_nn
    have h8 : (9664106 / 3628800) * h * L * en1 ≤ (9664106 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN hc1_nn
    have h9 : (1070017 / 3628800) * h * L * en ≤ (1070017 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN hc0_nn
    have h_alg :
        EN_n + (14097247 / 3628800) * h * L * EN_n
              + (43125206 / 3628800) * h * L * EN_n
              + (95476786 / 3628800) * h * L * EN_n
              + (139855262 / 3628800) * h * L * EN_n
              + (137968480 / 3628800) * h * L * EN_n
              + (91172642 / 3628800) * h * L * EN_n
              + (38833486 / 3628800) * h * L * EN_n
              + (9664106 / 3628800) * h * L * EN_n
              + (1070017 / 3628800) * h * L * EN_n + τabs
          = (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen8_le_EN, h1, h2, h3, h4, h5, h6, h7, h8, h9, h_alg.le]
  have hEN_le_grow : EN_n ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  have hen5_bd : en5 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen5_le_EN, hEN_le_grow]
  have hen6_bd : en6 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen6_le_EN, hEN_le_grow]
  have hen7_bd : en7 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen7_le_EN, hEN_le_grow]
  have hen8_bd : en8 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen8_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd)
    hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd) hen9_bd


private lemma ab9Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y8 y9 d0 d1 d2 d3 d4 d5 d6 d7 d8 dd ddd dddd ddddd dddddd ddddddd
      dddddddd ddddddddd : E) (h : ℝ) :
    y9 - y8 - h • ((14097247 / 3628800 : ℝ) • d8 - (43125206 / 3628800 : ℝ) • d7
                  + (95476786 / 3628800 : ℝ) • d6 - (139855262 / 3628800 : ℝ) • d5
                  + (137968480 / 3628800 : ℝ) • d4 - (91172642 / 3628800 : ℝ) • d3
                  + (38833486 / 3628800 : ℝ) • d2 - (9664106 / 3628800 : ℝ) • d1
                  + (1070017 / 3628800 : ℝ) • d0)
      = (y9 - y0 - (9 * h) • d0
            - ((9 * h) ^ 2 / 2) • dd
            - ((9 * h) ^ 3 / 6) • ddd
            - ((9 * h) ^ 4 / 24) • dddd
            - ((9 * h) ^ 5 / 120) • ddddd
            - ((9 * h) ^ 6 / 720) • dddddd
            - ((9 * h) ^ 7 / 5040) • ddddddd
            - ((9 * h) ^ 8 / 40320) • dddddddd
            - ((9 * h) ^ 9 / 362880) • ddddddddd)
        - (y8 - y0 - (8 * h) • d0
            - ((8 * h) ^ 2 / 2) • dd
            - ((8 * h) ^ 3 / 6) • ddd
            - ((8 * h) ^ 4 / 24) • dddd
            - ((8 * h) ^ 5 / 120) • ddddd
            - ((8 * h) ^ 6 / 720) • dddddd
            - ((8 * h) ^ 7 / 5040) • ddddddd
            - ((8 * h) ^ 8 / 40320) • dddddddd
            - ((8 * h) ^ 9 / 362880) • ddddddddd)
        - (14097247 * h / 3628800 : ℝ)
            • (d8 - d0 - (8 * h) • dd
                - ((8 * h) ^ 2 / 2) • ddd
                - ((8 * h) ^ 3 / 6) • dddd
                - ((8 * h) ^ 4 / 24) • ddddd
                - ((8 * h) ^ 5 / 120) • dddddd
                - ((8 * h) ^ 6 / 720) • ddddddd
                - ((8 * h) ^ 7 / 5040) • dddddddd
                - ((8 * h) ^ 8 / 40320) • ddddddddd)
        + (43125206 * h / 3628800 : ℝ)
            • (d7 - d0 - (7 * h) • dd
                - ((7 * h) ^ 2 / 2) • ddd
                - ((7 * h) ^ 3 / 6) • dddd
                - ((7 * h) ^ 4 / 24) • ddddd
                - ((7 * h) ^ 5 / 120) • dddddd
                - ((7 * h) ^ 6 / 720) • ddddddd
                - ((7 * h) ^ 7 / 5040) • dddddddd
                - ((7 * h) ^ 8 / 40320) • ddddddddd)
        - (95476786 * h / 3628800 : ℝ)
            • (d6 - d0 - (6 * h) • dd
                - ((6 * h) ^ 2 / 2) • ddd
                - ((6 * h) ^ 3 / 6) • dddd
                - ((6 * h) ^ 4 / 24) • ddddd
                - ((6 * h) ^ 5 / 120) • dddddd
                - ((6 * h) ^ 6 / 720) • ddddddd
                - ((6 * h) ^ 7 / 5040) • dddddddd
                - ((6 * h) ^ 8 / 40320) • ddddddddd)
        + (139855262 * h / 3628800 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd
                - ((5 * h) ^ 6 / 720) • ddddddd
                - ((5 * h) ^ 7 / 5040) • dddddddd
                - ((5 * h) ^ 8 / 40320) • ddddddddd)
        - (137968480 * h / 3628800 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd
                - ((4 * h) ^ 6 / 720) • ddddddd
                - ((4 * h) ^ 7 / 5040) • dddddddd
                - ((4 * h) ^ 8 / 40320) • ddddddddd)
        + (91172642 * h / 3628800 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd
                - ((3 * h) ^ 6 / 720) • ddddddd
                - ((3 * h) ^ 7 / 5040) • dddddddd
                - ((3 * h) ^ 8 / 40320) • ddddddddd)
        - (38833486 * h / 3628800 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd
                - ((2 * h) ^ 6 / 720) • ddddddd
                - ((2 * h) ^ 7 / 5040) • dddddddd
                - ((2 * h) ^ 8 / 40320) • ddddddddd)
        + (9664106 * h / 3628800 : ℝ)
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

private lemma ab9Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 3628800 * (9 * h) ^ 10 + M / 3628800 * (8 * h) ^ 10
      + (14097247 * h / 3628800) * (M / 362880 * (8 * h) ^ 9)
      + (43125206 * h / 3628800) * (M / 362880 * (7 * h) ^ 9)
      + (95476786 * h / 3628800) * (M / 362880 * (6 * h) ^ 9)
      + (139855262 * h / 3628800) * (M / 362880 * (5 * h) ^ 9)
      + (137968480 * h / 3628800) * (M / 362880 * (4 * h) ^ 9)
      + (91172642 * h / 3628800) * (M / 362880 * (3 * h) ^ 9)
      + (38833486 * h / 3628800) * (M / 362880 * (2 * h) ^ 9)
      + (9664106 * h / 3628800) * (M / 362880 * h ^ 9)
      = (102509448755347 / 20575296000 : ℝ) * M * h ^ 10 := by
  ring

private lemma ab9Vec_triangle_aux
    {E : Type*} [NormedAddCommGroup E]
    (A B C D G J K R S U : E) :
    ‖A - B - C + D - G + J - K + R - S + U‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖G‖ + ‖J‖ + ‖K‖ + ‖R‖ + ‖S‖ + ‖U‖ := by
  have h1 : ‖A - B - C + D - G + J - K + R - S + U‖
      ≤ ‖A - B - C + D - G + J - K + R - S‖ + ‖U‖ := norm_add_le _ _
  have h2 : ‖A - B - C + D - G + J - K + R - S‖
      ≤ ‖A - B - C + D - G + J - K + R‖ + ‖S‖ := norm_sub_le _ _
  have h3 : ‖A - B - C + D - G + J - K + R‖
      ≤ ‖A - B - C + D - G + J - K‖ + ‖R‖ := norm_add_le _ _
  have h4 : ‖A - B - C + D - G + J - K‖
      ≤ ‖A - B - C + D - G + J‖ + ‖K‖ := norm_sub_le _ _
  have h5 : ‖A - B - C + D - G + J‖
      ≤ ‖A - B - C + D - G‖ + ‖J‖ := norm_add_le _ _
  have h6 : ‖A - B - C + D - G‖
      ≤ ‖A - B - C + D‖ + ‖G‖ := norm_sub_le _ _
  have h7 : ‖A - B - C + D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_add_le _ _
  have h8 : ‖A - B - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le _ _
  have h9 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith

private lemma ab9Vec_residual_ten_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D G J K R S U : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (14097247 * h / 3628800 : ℝ) • C
        + (43125206 * h / 3628800 : ℝ) • D
        - (95476786 * h / 3628800 : ℝ) • G
        + (139855262 * h / 3628800 : ℝ) • J
        - (137968480 * h / 3628800 : ℝ) • K
        + (91172642 * h / 3628800 : ℝ) • R
        - (38833486 * h / 3628800 : ℝ) • S
        + (9664106 * h / 3628800 : ℝ) • U‖
      ≤ ‖A‖ + ‖B‖ + (14097247 * h / 3628800) * ‖C‖
          + (43125206 * h / 3628800) * ‖D‖
          + (95476786 * h / 3628800) * ‖G‖
          + (139855262 * h / 3628800) * ‖J‖
          + (137968480 * h / 3628800) * ‖K‖
          + (91172642 * h / 3628800) * ‖R‖
          + (38833486 * h / 3628800) * ‖S‖
          + (9664106 * h / 3628800) * ‖U‖ := by
  have hc8_nn : 0 ≤ (14097247 * h / 3628800 : ℝ) := by linarith
  have hc7_nn : 0 ≤ (43125206 * h / 3628800 : ℝ) := by linarith
  have hc6_nn : 0 ≤ (95476786 * h / 3628800 : ℝ) := by linarith
  have hc5_nn : 0 ≤ (139855262 * h / 3628800 : ℝ) := by linarith
  have hc4_nn : 0 ≤ (137968480 * h / 3628800 : ℝ) := by linarith
  have hc3_nn : 0 ≤ (91172642 * h / 3628800 : ℝ) := by linarith
  have hc2_nn : 0 ≤ (38833486 * h / 3628800 : ℝ) := by linarith
  have hc1_nn : 0 ≤ (9664106 * h / 3628800 : ℝ) := by linarith
  have hC_norm :
      ‖(14097247 * h / 3628800 : ℝ) • C‖ = (14097247 * h / 3628800) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc8_nn]
  have hD_norm :
      ‖(43125206 * h / 3628800 : ℝ) • D‖ = (43125206 * h / 3628800) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc7_nn]
  have hG_norm :
      ‖(95476786 * h / 3628800 : ℝ) • G‖ = (95476786 * h / 3628800) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc6_nn]
  have hJ_norm :
      ‖(139855262 * h / 3628800 : ℝ) • J‖ = (139855262 * h / 3628800) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc5_nn]
  have hK_norm :
      ‖(137968480 * h / 3628800 : ℝ) • K‖ = (137968480 * h / 3628800) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc4_nn]
  have hR_norm :
      ‖(91172642 * h / 3628800 : ℝ) • R‖ = (91172642 * h / 3628800) * ‖R‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc3_nn]
  have hS_norm :
      ‖(38833486 * h / 3628800 : ℝ) • S‖ = (38833486 * h / 3628800) * ‖S‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc2_nn]
  have hU_norm :
      ‖(9664106 * h / 3628800 : ℝ) • U‖ = (9664106 * h / 3628800) * ‖U‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc1_nn]
  have htri := ab9Vec_triangle_aux A B
    ((14097247 * h / 3628800 : ℝ) • C) ((43125206 * h / 3628800 : ℝ) • D)
    ((95476786 * h / 3628800 : ℝ) • G) ((139855262 * h / 3628800 : ℝ) • J)
    ((137968480 * h / 3628800 : ℝ) • K) ((91172642 * h / 3628800 : ℝ) • R)
    ((38833486 * h / 3628800 : ℝ) • S) ((9664106 * h / 3628800 : ℝ) • U)
  rw [hC_norm, hD_norm, hG_norm, hJ_norm, hK_norm, hR_norm, hS_norm, hU_norm] at htri
  exact htri

private lemma ab9Vec_residual_combine_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D G J K R S U : E) (M h : ℝ) (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (hA_bd : ‖A‖ ≤ M / 3628800 * (9 * h) ^ 10)
    (hB_bd : ‖B‖ ≤ M / 3628800 * (8 * h) ^ 10)
    (hC_bd : ‖C‖ ≤ M / 362880 * (8 * h) ^ 9)
    (hD_bd : ‖D‖ ≤ M / 362880 * (7 * h) ^ 9)
    (hG_bd : ‖G‖ ≤ M / 362880 * (6 * h) ^ 9)
    (hJ_bd : ‖J‖ ≤ M / 362880 * (5 * h) ^ 9)
    (hK_bd : ‖K‖ ≤ M / 362880 * (4 * h) ^ 9)
    (hR_bd : ‖R‖ ≤ M / 362880 * (3 * h) ^ 9)
    (hS_bd : ‖S‖ ≤ M / 362880 * (2 * h) ^ 9)
    (hU_bd : ‖U‖ ≤ M / 362880 * h ^ 9) :
    ‖A - B - (14097247 * h / 3628800 : ℝ) • C
        + (43125206 * h / 3628800 : ℝ) • D
        - (95476786 * h / 3628800 : ℝ) • G
        + (139855262 * h / 3628800 : ℝ) • J
        - (137968480 * h / 3628800 : ℝ) • K
        + (91172642 * h / 3628800 : ℝ) • R
        - (38833486 * h / 3628800 : ℝ) • S
        + (9664106 * h / 3628800 : ℝ) • U‖
      ≤ 4983 * M * h ^ 10 := by
  have htri := ab9Vec_residual_ten_term_triangle A B C D G J K R S U h hh
  have hc8_nn : 0 ≤ 14097247 * h / 3628800 := by linarith
  have hc7_nn : 0 ≤ 43125206 * h / 3628800 := by linarith
  have hc6_nn : 0 ≤ 95476786 * h / 3628800 := by linarith
  have hc5_nn : 0 ≤ 139855262 * h / 3628800 := by linarith
  have hc4_nn : 0 ≤ 137968480 * h / 3628800 := by linarith
  have hc3_nn : 0 ≤ 91172642 * h / 3628800 := by linarith
  have hc2_nn : 0 ≤ 38833486 * h / 3628800 := by linarith
  have hc1_nn : 0 ≤ 9664106 * h / 3628800 := by linarith
  have hCbd_s : (14097247 * h / 3628800) * ‖C‖
      ≤ (14097247 * h / 3628800) * (M / 362880 * (8 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hC_bd hc8_nn
  have hDbd_s : (43125206 * h / 3628800) * ‖D‖
      ≤ (43125206 * h / 3628800) * (M / 362880 * (7 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hD_bd hc7_nn
  have hGbd_s : (95476786 * h / 3628800) * ‖G‖
      ≤ (95476786 * h / 3628800) * (M / 362880 * (6 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hG_bd hc6_nn
  have hJbd_s : (139855262 * h / 3628800) * ‖J‖
      ≤ (139855262 * h / 3628800) * (M / 362880 * (5 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hJ_bd hc5_nn
  have hKbd_s : (137968480 * h / 3628800) * ‖K‖
      ≤ (137968480 * h / 3628800) * (M / 362880 * (4 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hK_bd hc4_nn
  have hRbd_s : (91172642 * h / 3628800) * ‖R‖
      ≤ (91172642 * h / 3628800) * (M / 362880 * (3 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hR_bd hc3_nn
  have hSbd_s : (38833486 * h / 3628800) * ‖S‖
      ≤ (38833486 * h / 3628800) * (M / 362880 * (2 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hS_bd hc2_nn
  have hUbd_s : (9664106 * h / 3628800) * ‖U‖
      ≤ (9664106 * h / 3628800) * (M / 362880 * h ^ 9) :=
    mul_le_mul_of_nonneg_left hU_bd hc1_nn
  have hbound_alg := ab9Vec_residual_bound_alg_identity M h
  have hh10_nn : 0 ≤ h ^ 10 := by positivity
  have hMh10_nn : 0 ≤ M * h ^ 10 := mul_nonneg hMnn hh10_nn
  have hslack : (102509448755347 / 20575296000 : ℝ) * M * h ^ 10
      ≤ 4983 * M * h ^ 10 := by
    rw [mul_assoc, mul_assoc (4983 : ℝ)]
    have hle : (102509448755347 / 20575296000 : ℝ) ≤ 4983 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh10_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hGbd_s,
    hJbd_s, hKbd_s, hRbd_s, hSbd_s, hUbd_s]

private theorem ab9Vec_pointwise_residual_bound
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
    (ht9h : t + 9 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 9 * h) - y (t + 8 * h)
        - h • ((14097247 / 3628800 : ℝ) • deriv y (t + 8 * h)
              - (43125206 / 3628800 : ℝ) • deriv y (t + 7 * h)
              + (95476786 / 3628800 : ℝ) • deriv y (t + 6 * h)
              - (139855262 / 3628800 : ℝ) • deriv y (t + 5 * h)
              + (137968480 / 3628800 : ℝ) • deriv y (t + 4 * h)
              - (91172642 / 3628800 : ℝ) • deriv y (t + 3 * h)
              + (38833486 / 3628800 : ℝ) • deriv y (t + 2 * h)
              - (9664106 / 3628800 : ℝ) • deriv y (t + h)
              + (1070017 / 3628800 : ℝ) • deriv y t)‖
      ≤ (4983 : ℝ) * M * h ^ 10 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have h9h : 0 ≤ 9 * h := by linarith
  have hRy8 :=
    y_tenth_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRy9 :=
    y_tenth_order_taylor_remainder_vec hy hbnd ht ht9h h9h
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
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  set ddddd : E := iteratedDeriv 5 y t with hddddd_def
  set dddddd : E := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd : E := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd : E := iteratedDeriv 8 y t with hdddddddd_def
  set ddddddddd : E := iteratedDeriv 9 y t with hddddddddd_def
  clear_value y0 y8 y9 d0 d1 d2 d3 d4 d5 d6 d7 d8
    dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd
  have hLTE_eq :=
    ab9Vec_residual_alg_identity y0 y8 y9 d0 d1 d2 d3 d4 d5 d6 d7 d8
      dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd h
  rw [hLTE_eq]
  set A : E := y9 - y0 - (9 * h) • d0
            - ((9 * h) ^ 2 / 2) • dd
            - ((9 * h) ^ 3 / 6) • ddd
            - ((9 * h) ^ 4 / 24) • dddd
            - ((9 * h) ^ 5 / 120) • ddddd
            - ((9 * h) ^ 6 / 720) • dddddd
            - ((9 * h) ^ 7 / 5040) • ddddddd
            - ((9 * h) ^ 8 / 40320) • dddddddd
            - ((9 * h) ^ 9 / 362880) • ddddddddd with hA_def
  set B : E := y8 - y0 - (8 * h) • d0
            - ((8 * h) ^ 2 / 2) • dd
            - ((8 * h) ^ 3 / 6) • ddd
            - ((8 * h) ^ 4 / 24) • dddd
            - ((8 * h) ^ 5 / 120) • ddddd
            - ((8 * h) ^ 6 / 720) • dddddd
            - ((8 * h) ^ 7 / 5040) • ddddddd
            - ((8 * h) ^ 8 / 40320) • dddddddd
            - ((8 * h) ^ 9 / 362880) • ddddddddd with hB_def
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
  set G : E := d6 - d0 - (6 * h) • dd
            - ((6 * h) ^ 2 / 2) • ddd
            - ((6 * h) ^ 3 / 6) • dddd
            - ((6 * h) ^ 4 / 24) • ddddd
            - ((6 * h) ^ 5 / 120) • dddddd
            - ((6 * h) ^ 6 / 720) • ddddddd
            - ((6 * h) ^ 7 / 5040) • dddddddd
            - ((6 * h) ^ 8 / 40320) • ddddddddd with hG_def
  set J : E := d5 - d0 - (5 * h) • dd
            - ((5 * h) ^ 2 / 2) • ddd
            - ((5 * h) ^ 3 / 6) • dddd
            - ((5 * h) ^ 4 / 24) • ddddd
            - ((5 * h) ^ 5 / 120) • dddddd
            - ((5 * h) ^ 6 / 720) • ddddddd
            - ((5 * h) ^ 7 / 5040) • dddddddd
            - ((5 * h) ^ 8 / 40320) • ddddddddd with hJ_def
  set K : E := d4 - d0 - (4 * h) • dd
            - ((4 * h) ^ 2 / 2) • ddd
            - ((4 * h) ^ 3 / 6) • dddd
            - ((4 * h) ^ 4 / 24) • ddddd
            - ((4 * h) ^ 5 / 120) • dddddd
            - ((4 * h) ^ 6 / 720) • ddddddd
            - ((4 * h) ^ 7 / 5040) • dddddddd
            - ((4 * h) ^ 8 / 40320) • ddddddddd with hK_def
  set R : E := d3 - d0 - (3 * h) • dd
            - ((3 * h) ^ 2 / 2) • ddd
            - ((3 * h) ^ 3 / 6) • dddd
            - ((3 * h) ^ 4 / 24) • ddddd
            - ((3 * h) ^ 5 / 120) • dddddd
            - ((3 * h) ^ 6 / 720) • ddddddd
            - ((3 * h) ^ 7 / 5040) • dddddddd
            - ((3 * h) ^ 8 / 40320) • ddddddddd with hR_def
  set S : E := d2 - d0 - (2 * h) • dd
            - ((2 * h) ^ 2 / 2) • ddd
            - ((2 * h) ^ 3 / 6) • dddd
            - ((2 * h) ^ 4 / 24) • ddddd
            - ((2 * h) ^ 5 / 120) • dddddd
            - ((2 * h) ^ 6 / 720) • ddddddd
            - ((2 * h) ^ 7 / 5040) • dddddddd
            - ((2 * h) ^ 8 / 40320) • ddddddddd with hS_def
  set U : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd
            - (h ^ 4 / 24) • ddddd
            - (h ^ 5 / 120) • dddddd
            - (h ^ 6 / 720) • ddddddd
            - (h ^ 7 / 5040) • dddddddd
            - (h ^ 8 / 40320) • ddddddddd with hU_def
  clear_value A B C D G J K R S U
  have hA_bd : ‖A‖ ≤ M / 3628800 * (9 * h) ^ 10 := hRy9
  have hB_bd : ‖B‖ ≤ M / 3628800 * (8 * h) ^ 10 := hRy8
  have hC_bd : ‖C‖ ≤ M / 362880 * (8 * h) ^ 9 := hRyp8
  have hD_bd : ‖D‖ ≤ M / 362880 * (7 * h) ^ 9 := hRyp7
  have hG_bd : ‖G‖ ≤ M / 362880 * (6 * h) ^ 9 := hRyp6
  have hJ_bd : ‖J‖ ≤ M / 362880 * (5 * h) ^ 9 := hRyp5
  have hK_bd : ‖K‖ ≤ M / 362880 * (4 * h) ^ 9 := hRyp4
  have hR_bd : ‖R‖ ≤ M / 362880 * (3 * h) ^ 9 := hRyp3
  have hS_bd : ‖S‖ ≤ M / 362880 * (2 * h) ^ 9 := hRyp2
  have hU_bd : ‖U‖ ≤ M / 362880 * h ^ 9 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  exact ab9Vec_residual_combine_aux A B C D G J K R S U M h hh hMnn
    hA_bd hB_bd hC_bd hD_bd hG_bd hJ_bd hK_bd hR_bd hS_bd hU_bd

theorem ab9Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 10 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 9) * h ≤ T →
        ‖ab9VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 10 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_ten_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(4983 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
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
  show ‖ab9VecResidual h t y‖ ≤ 4983 * M * h ^ 10
  unfold ab9VecResidual
  exact ab9Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem hh.le

theorem ab9Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 10 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
      ‖y₀ - y t₀‖ ≤ ε₀ → ‖y₁ - y (t₀ + h)‖ ≤ ε₀ →
      ‖y₂ - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖y₃ - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖y₄ - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖y₅ - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖y₆ - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ‖y₇ - y (t₀ + 7 * h)‖ ≤ ε₀ →
      ‖y₈ - y (t₀ + 8 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 8) * h ≤ T →
      ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((2231497 / 14175) * L * T) * ε₀ + K * h ^ 9 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab9Vec_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((2231497 / 14175) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd he8_bd N hNh
  set α : Fin 9 → ℝ := ab9GenericCoeff with hα_def
  set y₀_non : Fin 9 → E := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈]
    with hy_non_def
  have hs : (1 : ℕ) ≤ 9 := by norm_num
  haveI : Nonempty (Fin 9) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIterVec 9 α h f t₀ y₀_non 0 = y₀ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter1 : abIterVec 9 α h f t₀ y₀_non 1 = y₁ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter2 : abIterVec 9 α h f t₀ y₀_non 2 = y₂ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter3 : abIterVec 9 α h f t₀ y₀_non 3 = y₃ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter4 : abIterVec 9 α h f t₀ y₀_non 4 = y₄ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter5 : abIterVec 9 α h f t₀ y₀_non 5 = y₅ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter6 : abIterVec 9 α h f t₀ y₀_non 6 = y₆ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter7 : abIterVec 9 α h f t₀ y₀_non 7 = y₇ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter8 : abIterVec 9 α h f t₀ y₀_non 8 = y₈ := by
    unfold abIterVec; simp [hy_non_def]
  have hstart : abErrWindowVec hs α h f t₀ y₀_non y 0 ≤ ε₀ := by
    unfold abErrWindowVec
    apply Finset.sup'_le
    intro j _
    show abErrVec 9 α h f t₀ y₀_non y (0 + (j : ℕ)) ≤ ε₀
    unfold abErrVec
    fin_cases j
    · show ‖abIterVec 9 α h f t₀ y₀_non 0
          - y (t₀ + ((0 + (((0 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]; exact he0_bd
    · show ‖abIterVec 9 α h f t₀ y₀_non 1
          - y (t₀ + ((0 + (((1 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]; exact he1_bd
    · show ‖abIterVec 9 α h f t₀ y₀_non 2
          - y (t₀ + ((0 + (((2 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]; exact he2_bd
    · show ‖abIterVec 9 α h f t₀ y₀_non 3
          - y (t₀ + ((0 + (((3 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 9) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]; exact he3_bd
    · show ‖abIterVec 9 α h f t₀ y₀_non 4
          - y (t₀ + ((0 + (((4 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter4]
      have hval4 : ((4 : Fin 9) : ℕ) = 4 := rfl
      have : ((0 + (((4 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval4]; push_cast; ring
      rw [this]; exact he4_bd
    · show ‖abIterVec 9 α h f t₀ y₀_non 5
          - y (t₀ + ((0 + (((5 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter5]
      have hval5 : ((5 : Fin 9) : ℕ) = 5 := rfl
      have : ((0 + (((5 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval5]; push_cast; ring
      rw [this]; exact he5_bd
    · show ‖abIterVec 9 α h f t₀ y₀_non 6
          - y (t₀ + ((0 + (((6 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter6]
      have hval6 : ((6 : Fin 9) : ℕ) = 6 := rfl
      have : ((0 + (((6 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 6 := by
        rw [hval6]; push_cast; ring
      rw [this]; exact he6_bd
    · show ‖abIterVec 9 α h f t₀ y₀_non 7
          - y (t₀ + ((0 + (((7 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter7]
      have hval7 : ((7 : Fin 9) : ℕ) = 7 := rfl
      have : ((0 + (((7 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 7 := by
        rw [hval7]; push_cast; ring
      rw [this]; exact he7_bd
    · show ‖abIterVec 9 α h f t₀ y₀_non 8
          - y (t₀ + ((0 + (((8 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter8]
      have hval8 : ((8 : Fin 9) : ℕ) = 8 := rfl
      have : ((0 + (((8 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 8 := by
        rw [hval8]; push_cast; ring
      rw [this]; exact he8_bd
  have hres_gen : ∀ n : ℕ, n < N →
      ‖abResidualVec 9 α h y t₀ n‖ ≤ C * h ^ (9 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 9 ≤ (N : ℝ) + 8 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn9_le : ((n : ℝ) + 9) * h ≤ T := by
      have hmul : ((n : ℝ) + 9) * h ≤ ((N : ℝ) + 8) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn9_le
    have hbridge := ab9VecResidual_eq_abResidualVec (E := E) h y t₀ n
    have hpow : C * h ^ (9 + 1) = C * h ^ 10 := by norm_num
    rw [hα_def, ← hbridge]
    linarith [hres, hpow.symm.le, hpow.le]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 8) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 8 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic_vec (p := 9) hs α hh.le hL hC_nn hf t₀
      y₀_non y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 9 α L = (2231497 / 14175) * L from by
    rw [hα_def]; exact abLip_ab9GenericCoeff L] at hgeneric
  have hwindow_ge : abErrVec 9 α h f t₀ y₀_non y N
      ≤ abErrWindowVec hs α h f t₀ y₀_non y N := by
    show abErrVec 9 α h f t₀ y₀_non y (N + ((⟨0, hs⟩ : Fin 9) : ℕ))
        ≤ abErrWindowVec hs α h f t₀ y₀_non y N
    unfold abErrWindowVec
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 9 => abErrVec 9 α h f t₀ y₀_non y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIterVec 9 α h f t₀ y₀_non N
        = ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N := by
    rw [hα_def, hy_non_def]
    exact (ab9IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N).symm
  have habsErr :
      abErrVec 9 α h f t₀ y₀_non y N
        = ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N - y (t₀ + (N : ℝ) * h)‖ := by
    show ‖abIterVec 9 α h f t₀ y₀_non N - y (t₀ + (N : ℝ) * h)‖
        = ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N - y (t₀ + (N : ℝ) * h)‖
    rw [hbridge]
  show ‖ab9IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N - y (t₀ + (N : ℝ) * h)‖
      ≤ Real.exp ((2231497 / 14175) * L * T) * ε₀
        + T * Real.exp ((2231497 / 14175) * L * T) * C * h ^ 9
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]


end LMM
