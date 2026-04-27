import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB10Convergence
import OpenMath.LMMAM7VectorConvergence

/-! ## Adams-Bashforth 10-step Vector Quantitative Convergence Chain (Iserles §1.2)

Finite-dimensional vector-valued analogue of the scalar AB10 quantitative
convergence chain in `OpenMath.LMMAB10Convergence`.
-/

namespace LMM

/-- Helper: expand `∑ i : Fin 10, f i` as ten summands. -/
private lemma sum_univ_ten_aux {α : Type*} [AddCommMonoid α] (f : Fin 10 → α) :
    ∑ i : Fin 10, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

/-- AB10 vector iteration with ten starting samples. -/
noncomputable def ab10IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) : ℕ → E
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | 6 => y₆
  | 7 => y₇
  | 8 => y₈
  | 9 => y₉
  | n + 10 =>
      ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9)
        + h • ((30277247 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 9) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9))
              - (104995189 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8))
              + (265932680 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7))
              - (454661776 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6))
              + (538363838 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5))
              - (444772162 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4))
              + (252618224 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3))
              - (94307320 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2))
              + (20884811 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1))
              - (2082753 / 7257600 : ℝ) • f (t₀ + (n : ℝ) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n))

@[simp] lemma ab10IterVec_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 0 = y₀ := rfl

@[simp] lemma ab10IterVec_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 1 = y₁ := rfl

@[simp] lemma ab10IterVec_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 2 = y₂ := rfl

@[simp] lemma ab10IterVec_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 3 = y₃ := rfl

@[simp] lemma ab10IterVec_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 4 = y₄ := rfl

@[simp] lemma ab10IterVec_five
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 5 = y₅ := rfl

@[simp] lemma ab10IterVec_six
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 6 = y₆ := rfl

@[simp] lemma ab10IterVec_seven
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 7 = y₇ := rfl

@[simp] lemma ab10IterVec_eight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 8 = y₈ := rfl

@[simp] lemma ab10IterVec_nine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 9 = y₉ := rfl

lemma ab10IterVec_succ_ten
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) (n : ℕ) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10)
      = ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9)
        + h • ((30277247 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 9) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9))
              - (104995189 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8))
              + (265932680 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7))
              - (454661776 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6))
              + (538363838 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5))
              - (444772162 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4))
              + (252618224 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3))
              - (94307320 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2))
              + (20884811 / 7257600 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1))
              - (2082753 / 7257600 : ℝ) • f (t₀ + (n : ℝ) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n)) := rfl

/-- Vector AB10 local truncation residual. -/
noncomputable def ab10VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 10 * h) - y (t + 9 * h)
    - h • ((30277247 / 7257600 : ℝ) • deriv y (t + 9 * h)
          - (104995189 / 7257600 : ℝ) • deriv y (t + 8 * h)
          + (265932680 / 7257600 : ℝ) • deriv y (t + 7 * h)
          - (454661776 / 7257600 : ℝ) • deriv y (t + 6 * h)
          + (538363838 / 7257600 : ℝ) • deriv y (t + 5 * h)
          - (444772162 / 7257600 : ℝ) • deriv y (t + 4 * h)
          + (252618224 / 7257600 : ℝ) • deriv y (t + 3 * h)
          - (94307320 / 7257600 : ℝ) • deriv y (t + 2 * h)
          + (20884811 / 7257600 : ℝ) • deriv y (t + h)
          - (2082753 / 7257600 : ℝ) • deriv y t)

theorem ab10Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab10VecResidual h t y
      = y (t + 10 * h) - y (t + 9 * h)
          - h • ((30277247 / 7257600 : ℝ) • deriv y (t + 9 * h)
                - (104995189 / 7257600 : ℝ) • deriv y (t + 8 * h)
                + (265932680 / 7257600 : ℝ) • deriv y (t + 7 * h)
                - (454661776 / 7257600 : ℝ) • deriv y (t + 6 * h)
                + (538363838 / 7257600 : ℝ) • deriv y (t + 5 * h)
                - (444772162 / 7257600 : ℝ) • deriv y (t + 4 * h)
                + (252618224 / 7257600 : ℝ) • deriv y (t + 3 * h)
                - (94307320 / 7257600 : ℝ) • deriv y (t + 2 * h)
                + (20884811 / 7257600 : ℝ) • deriv y (t + h)
                - (2082753 / 7257600 : ℝ) • deriv y t) := rfl

theorem iteratedDeriv_eleven_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 11 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 11 y t‖ ≤ M := by
  have h_cont : Continuous (iteratedDeriv 11 y) :=
    hy.continuous_iteratedDeriv 11 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

theorem y_eleventh_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 11 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 11 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖y (t + r) - y t - r • deriv y t
        - (r ^ 2 / 2) • iteratedDeriv 2 y t
        - (r ^ 3 / 6) • iteratedDeriv 3 y t
        - (r ^ 4 / 24) • iteratedDeriv 4 y t
        - (r ^ 5 / 120) • iteratedDeriv 5 y t
        - (r ^ 6 / 720) • iteratedDeriv 6 y t
        - (r ^ 7 / 5040) • iteratedDeriv 7 y t
        - (r ^ 8 / 40320) • iteratedDeriv 8 y t
        - (r ^ 9 / 362880) • iteratedDeriv 9 y t
        - (r ^ 10 / 3628800) • iteratedDeriv 10 y t‖
      ≤ M / 39916800 * r ^ 11 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htr_le : t ≤ t + r := by linarith
  have h_dy_bound :
      ∀ s ∈ Set.Icc t (t + r),
        ‖deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
            - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
            - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
            - ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
            - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t
            - ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t
            - ((s - t) ^ 7 / 5040) • iteratedDeriv 8 y t
            - ((s - t) ^ 8 / 40320) • iteratedDeriv 9 y t
            - ((s - t) ^ 9 / 362880) • iteratedDeriv 10 y t‖
          ≤ M / 3628800 * (s - t) ^ 10 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have hdy : ContDiff ℝ 10 (deriv y) := hy.deriv'
    have hbnd_d :
        ∀ u ∈ Set.Icc a b, ‖iteratedDeriv 10 (deriv y) u‖ ≤ M := by
      intro u hu
      have hidd_eq : iteratedDeriv 10 (deriv y) = iteratedDeriv 11 y := by
        have : iteratedDeriv 11 y = iteratedDeriv 10 (deriv y) :=
          iteratedDeriv_succ' (n := 10) (f := y)
        exact this.symm
      simpa [hidd_eq] using hbnd u hu
    have hrem :=
      y_tenth_order_taylor_remainder_vec hdy hbnd_d ht
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
    have hiter7 : iteratedDeriv 7 (deriv y) t = iteratedDeriv 8 y t := by
      have : iteratedDeriv 8 y = iteratedDeriv 7 (deriv y) :=
        iteratedDeriv_succ' (n := 7) (f := y)
      rw [this]
    have hiter8 : iteratedDeriv 8 (deriv y) t = iteratedDeriv 9 y t := by
      have : iteratedDeriv 9 y = iteratedDeriv 8 (deriv y) :=
        iteratedDeriv_succ' (n := 8) (f := y)
      rw [this]
    have hiter9 : iteratedDeriv 9 (deriv y) t = iteratedDeriv 10 y t := by
      have : iteratedDeriv 10 y = iteratedDeriv 9 (deriv y) :=
        iteratedDeriv_succ' (n := 9) (f := y)
      rw [this]
    rw [hsplit] at hrem
    simpa [hderiv2, hiter2, hiter3, hiter4, hiter5, hiter6, hiter7, hiter8,
      hiter9] using hrem
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
  have h_septic_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 7 / 5040) • iteratedDeriv 8 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_octic_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 8 / 40320) • iteratedDeriv 9 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_nonic_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 9 / 362880) • iteratedDeriv 10 y t)
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
  have h_septic_eval :
      ∫ s in t..t + r, ((s - t) ^ 7 / 5040) • iteratedDeriv 8 y t
        = (r ^ 8 / 40320) • iteratedDeriv 8 y t := by
    rw [intervalIntegral.integral_smul_const]
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
    have h_fun :
        (fun s : ℝ => (s - t) ^ 7 / 5040)
          = fun s : ℝ => (1 / 5040 : ℝ) * (s - t) ^ 7 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 7 / 5040 = r ^ 8 / 40320 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_octic_eval :
      ∫ s in t..t + r, ((s - t) ^ 8 / 40320) • iteratedDeriv 9 y t
        = (r ^ 9 / 362880) • iteratedDeriv 9 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 8 = r ^ 9 / 9 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 8
            = ∫ s in (t - t)..(t + r - t), s ^ 8 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 8) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 8 / 40320)
          = fun s : ℝ => (1 / 40320 : ℝ) * (s - t) ^ 8 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 8 / 40320 = r ^ 9 / 362880 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_nonic_eval :
      ∫ s in t..t + r, ((s - t) ^ 9 / 362880) • iteratedDeriv 10 y t
        = (r ^ 10 / 3628800) • iteratedDeriv 10 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 9 = r ^ 10 / 10 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 9
            = ∫ s in (t - t)..(t + r - t), s ^ 9 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 9) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 9 / 362880)
          = fun s : ℝ => (1 / 362880 : ℝ) * (s - t) ^ 9 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 9 / 362880 = r ^ 10 / 3628800 := by
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
          - (r ^ 8 / 40320) • iteratedDeriv 8 y t
          - (r ^ 9 / 362880) • iteratedDeriv 9 y t
          - (r ^ 10 / 3628800) • iteratedDeriv 10 y t
        = ∫ s in t..t + r,
            (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
              - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
              - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
              - ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
              - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t
              - ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t
              - ((s - t) ^ 7 / 5040) • iteratedDeriv 8 y t
              - ((s - t) ^ 8 / 40320) • iteratedDeriv 9 y t
              - ((s - t) ^ 9 / 362880) • iteratedDeriv 10 y t) := by
    rw [intervalIntegral.integral_sub
        (((((((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int).sub h_quintic_int).sub
          h_sextic_int).sub h_septic_int).sub h_octic_int) h_nonic_int,
      intervalIntegral.integral_sub
        ((((((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int).sub h_quintic_int).sub
          h_sextic_int).sub h_septic_int) h_octic_int,
      intervalIntegral.integral_sub
        (((((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int).sub h_quintic_int).sub
          h_sextic_int) h_septic_int,
      intervalIntegral.integral_sub
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
      h_quintic_eval, h_sextic_eval, h_septic_eval, h_octic_eval, h_nonic_eval]
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
            - ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t
            - ((s - t) ^ 7 / 5040) • iteratedDeriv 8 y t
            - ((s - t) ^ 8 / 40320) • iteratedDeriv 9 y t
            - ((s - t) ^ 9 / 362880) • iteratedDeriv 10 y t)‖
        ≤ ∫ s in t..t + r, M / 3628800 * (s - t) ^ 10 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dy_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 3628800 * (s - t) ^ 10).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 3628800 * (s - t) ^ 10 = M / 39916800 * r ^ 11 := by
    have h_inner : ∫ s in t..t + r, (s - t) ^ 10 = r ^ 11 / 11 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 10
            = ∫ s in (t - t)..(t + r - t), s ^ 10 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 10) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

theorem derivY_tenth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 11 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 11 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖deriv y (t + r) - deriv y t - r • iteratedDeriv 2 y t
        - (r ^ 2 / 2) • iteratedDeriv 3 y t
        - (r ^ 3 / 6) • iteratedDeriv 4 y t
        - (r ^ 4 / 24) • iteratedDeriv 5 y t
        - (r ^ 5 / 120) • iteratedDeriv 6 y t
        - (r ^ 6 / 720) • iteratedDeriv 7 y t
        - (r ^ 7 / 5040) • iteratedDeriv 8 y t
        - (r ^ 8 / 40320) • iteratedDeriv 9 y t
        - (r ^ 9 / 362880) • iteratedDeriv 10 y t‖
      ≤ M / 3628800 * r ^ 10 := by
  have hdy : ContDiff ℝ 10 (deriv y) := hy.deriv'
  have hbnd_d :
      ∀ s ∈ Set.Icc a b, ‖iteratedDeriv 10 (deriv y) s‖ ≤ M := by
    intro s hs
    have hidd_eq : iteratedDeriv 10 (deriv y) = iteratedDeriv 11 y := by
      have : iteratedDeriv 11 y = iteratedDeriv 10 (deriv y) :=
        iteratedDeriv_succ' (n := 10) (f := y)
      exact this.symm
    simpa [hidd_eq] using hbnd s hs
  have hrem := y_tenth_order_taylor_remainder_vec hdy hbnd_d ht htr hr
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
  have hiter7 : iteratedDeriv 7 (deriv y) t = iteratedDeriv 8 y t := by
    have : iteratedDeriv 8 y = iteratedDeriv 7 (deriv y) :=
      iteratedDeriv_succ' (n := 7) (f := y)
    rw [this]
  have hiter8 : iteratedDeriv 8 (deriv y) t = iteratedDeriv 9 y t := by
    have : iteratedDeriv 9 y = iteratedDeriv 8 (deriv y) :=
      iteratedDeriv_succ' (n := 8) (f := y)
    rw [this]
  have hiter9 : iteratedDeriv 9 (deriv y) t = iteratedDeriv 10 y t := by
    have : iteratedDeriv 10 y = iteratedDeriv 9 (deriv y) :=
      iteratedDeriv_succ' (n := 9) (f := y)
    rw [this]
  simpa [hderiv2, hiter2, hiter3, hiter4, hiter5, hiter6, hiter7, hiter8,
    hiter9] using hrem

private lemma ab10Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 dd ddd dddd ddddd dddddd
      ddddddd dddddddd ddddddddd dddddddddd : E) (h : ℝ) :
    y10 - y9 - h • ((30277247 / 7257600 : ℝ) • d9 - (104995189 / 7257600 : ℝ) • d8
                  + (265932680 / 7257600 : ℝ) • d7 - (454661776 / 7257600 : ℝ) • d6
                  + (538363838 / 7257600 : ℝ) • d5 - (444772162 / 7257600 : ℝ) • d4
                  + (252618224 / 7257600 : ℝ) • d3 - (94307320 / 7257600 : ℝ) • d2
                  + (20884811 / 7257600 : ℝ) • d1 - (2082753 / 7257600 : ℝ) • d0)
      = (y10 - y0 - (10 * h) • d0
            - ((10 * h) ^ 2 / 2) • dd
            - ((10 * h) ^ 3 / 6) • ddd
            - ((10 * h) ^ 4 / 24) • dddd
            - ((10 * h) ^ 5 / 120) • ddddd
            - ((10 * h) ^ 6 / 720) • dddddd
            - ((10 * h) ^ 7 / 5040) • ddddddd
            - ((10 * h) ^ 8 / 40320) • dddddddd
            - ((10 * h) ^ 9 / 362880) • ddddddddd
            - ((10 * h) ^ 10 / 3628800) • dddddddddd)
        - (y9 - y0 - (9 * h) • d0
            - ((9 * h) ^ 2 / 2) • dd
            - ((9 * h) ^ 3 / 6) • ddd
            - ((9 * h) ^ 4 / 24) • dddd
            - ((9 * h) ^ 5 / 120) • ddddd
            - ((9 * h) ^ 6 / 720) • dddddd
            - ((9 * h) ^ 7 / 5040) • ddddddd
            - ((9 * h) ^ 8 / 40320) • dddddddd
            - ((9 * h) ^ 9 / 362880) • ddddddddd
            - ((9 * h) ^ 10 / 3628800) • dddddddddd)
        - (30277247 * h / 7257600 : ℝ)
            • (d9 - d0 - (9 * h) • dd
                - ((9 * h) ^ 2 / 2) • ddd
                - ((9 * h) ^ 3 / 6) • dddd
                - ((9 * h) ^ 4 / 24) • ddddd
                - ((9 * h) ^ 5 / 120) • dddddd
                - ((9 * h) ^ 6 / 720) • ddddddd
                - ((9 * h) ^ 7 / 5040) • dddddddd
                - ((9 * h) ^ 8 / 40320) • ddddddddd
                - ((9 * h) ^ 9 / 362880) • dddddddddd)
        + (104995189 * h / 7257600 : ℝ)
            • (d8 - d0 - (8 * h) • dd
                - ((8 * h) ^ 2 / 2) • ddd
                - ((8 * h) ^ 3 / 6) • dddd
                - ((8 * h) ^ 4 / 24) • ddddd
                - ((8 * h) ^ 5 / 120) • dddddd
                - ((8 * h) ^ 6 / 720) • ddddddd
                - ((8 * h) ^ 7 / 5040) • dddddddd
                - ((8 * h) ^ 8 / 40320) • ddddddddd
                - ((8 * h) ^ 9 / 362880) • dddddddddd)
        - (265932680 * h / 7257600 : ℝ)
            • (d7 - d0 - (7 * h) • dd
                - ((7 * h) ^ 2 / 2) • ddd
                - ((7 * h) ^ 3 / 6) • dddd
                - ((7 * h) ^ 4 / 24) • ddddd
                - ((7 * h) ^ 5 / 120) • dddddd
                - ((7 * h) ^ 6 / 720) • ddddddd
                - ((7 * h) ^ 7 / 5040) • dddddddd
                - ((7 * h) ^ 8 / 40320) • ddddddddd
                - ((7 * h) ^ 9 / 362880) • dddddddddd)
        + (454661776 * h / 7257600 : ℝ)
            • (d6 - d0 - (6 * h) • dd
                - ((6 * h) ^ 2 / 2) • ddd
                - ((6 * h) ^ 3 / 6) • dddd
                - ((6 * h) ^ 4 / 24) • ddddd
                - ((6 * h) ^ 5 / 120) • dddddd
                - ((6 * h) ^ 6 / 720) • ddddddd
                - ((6 * h) ^ 7 / 5040) • dddddddd
                - ((6 * h) ^ 8 / 40320) • ddddddddd
                - ((6 * h) ^ 9 / 362880) • dddddddddd)
        - (538363838 * h / 7257600 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd
                - ((5 * h) ^ 6 / 720) • ddddddd
                - ((5 * h) ^ 7 / 5040) • dddddddd
                - ((5 * h) ^ 8 / 40320) • ddddddddd
                - ((5 * h) ^ 9 / 362880) • dddddddddd)
        + (444772162 * h / 7257600 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd
                - ((4 * h) ^ 6 / 720) • ddddddd
                - ((4 * h) ^ 7 / 5040) • dddddddd
                - ((4 * h) ^ 8 / 40320) • ddddddddd
                - ((4 * h) ^ 9 / 362880) • dddddddddd)
        - (252618224 * h / 7257600 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd
                - ((3 * h) ^ 6 / 720) • ddddddd
                - ((3 * h) ^ 7 / 5040) • dddddddd
                - ((3 * h) ^ 8 / 40320) • ddddddddd
                - ((3 * h) ^ 9 / 362880) • dddddddddd)
        + (94307320 * h / 7257600 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd
                - ((2 * h) ^ 6 / 720) • ddddddd
                - ((2 * h) ^ 7 / 5040) • dddddddd
                - ((2 * h) ^ 8 / 40320) • ddddddddd
                - ((2 * h) ^ 9 / 362880) • dddddddddd)
        - (20884811 * h / 7257600 : ℝ)
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

private lemma ab10Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 39916800 * (10 * h) ^ 11 + M / 39916800 * (9 * h) ^ 11
      + (30277247 * h / 7257600) * (M / 3628800 * (9 * h) ^ 10)
      + (104995189 * h / 7257600) * (M / 3628800 * (8 * h) ^ 10)
      + (265932680 * h / 7257600) * (M / 3628800 * (7 * h) ^ 10)
      + (454661776 * h / 7257600) * (M / 3628800 * (6 * h) ^ 10)
      + (538363838 * h / 7257600) * (M / 3628800 * (5 * h) ^ 10)
      + (444772162 * h / 7257600) * (M / 3628800 * (4 * h) ^ 10)
      + (252618224 * h / 7257600) * (M / 3628800 * (3 * h) ^ 10)
      + (94307320 * h / 7257600) * (M / 3628800 * (2 * h) ^ 10)
      + (20884811 * h / 7257600) * (M / 3628800 * h ^ 10)
      = (11840488855359257 / 754427520000 : ℝ) * M * h ^ 11 := by
  ring

private lemma ab10Vec_triangle_aux
    {E : Type*} [NormedAddCommGroup E]
    (A B C D G J K R S U V : E) :
    ‖A - B - C + D - G + J - K + R - S + U - V‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖G‖ + ‖J‖ + ‖K‖ + ‖R‖ + ‖S‖ + ‖U‖ + ‖V‖ := by
  have h1 : ‖A - B - C + D - G + J - K + R - S + U - V‖
      ≤ ‖A - B - C + D - G + J - K + R - S + U‖ + ‖V‖ := norm_sub_le _ _
  have h2 : ‖A - B - C + D - G + J - K + R - S + U‖
      ≤ ‖A - B - C + D - G + J - K + R - S‖ + ‖U‖ := norm_add_le _ _
  have h3 : ‖A - B - C + D - G + J - K + R - S‖
      ≤ ‖A - B - C + D - G + J - K + R‖ + ‖S‖ := norm_sub_le _ _
  have h4 : ‖A - B - C + D - G + J - K + R‖
      ≤ ‖A - B - C + D - G + J - K‖ + ‖R‖ := norm_add_le _ _
  have h5 : ‖A - B - C + D - G + J - K‖
      ≤ ‖A - B - C + D - G + J‖ + ‖K‖ := norm_sub_le _ _
  have h6 : ‖A - B - C + D - G + J‖
      ≤ ‖A - B - C + D - G‖ + ‖J‖ := norm_add_le _ _
  have h7 : ‖A - B - C + D - G‖
      ≤ ‖A - B - C + D‖ + ‖G‖ := norm_sub_le _ _
  have h8 : ‖A - B - C + D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_add_le _ _
  have h9 : ‖A - B - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le _ _
  have h10 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith

private lemma ab10Vec_residual_eleven_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D G J K R S U V : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (30277247 * h / 7257600 : ℝ) • C
        + (104995189 * h / 7257600 : ℝ) • D
        - (265932680 * h / 7257600 : ℝ) • G
        + (454661776 * h / 7257600 : ℝ) • J
        - (538363838 * h / 7257600 : ℝ) • K
        + (444772162 * h / 7257600 : ℝ) • R
        - (252618224 * h / 7257600 : ℝ) • S
        + (94307320 * h / 7257600 : ℝ) • U
        - (20884811 * h / 7257600 : ℝ) • V‖
      ≤ ‖A‖ + ‖B‖ + (30277247 * h / 7257600) * ‖C‖
          + (104995189 * h / 7257600) * ‖D‖
          + (265932680 * h / 7257600) * ‖G‖
          + (454661776 * h / 7257600) * ‖J‖
          + (538363838 * h / 7257600) * ‖K‖
          + (444772162 * h / 7257600) * ‖R‖
          + (252618224 * h / 7257600) * ‖S‖
          + (94307320 * h / 7257600) * ‖U‖
          + (20884811 * h / 7257600) * ‖V‖ := by
  have hc9_nn : 0 ≤ (30277247 * h / 7257600 : ℝ) := by linarith
  have hc8_nn : 0 ≤ (104995189 * h / 7257600 : ℝ) := by linarith
  have hc7_nn : 0 ≤ (265932680 * h / 7257600 : ℝ) := by linarith
  have hc6_nn : 0 ≤ (454661776 * h / 7257600 : ℝ) := by linarith
  have hc5_nn : 0 ≤ (538363838 * h / 7257600 : ℝ) := by linarith
  have hc4_nn : 0 ≤ (444772162 * h / 7257600 : ℝ) := by linarith
  have hc3_nn : 0 ≤ (252618224 * h / 7257600 : ℝ) := by linarith
  have hc2_nn : 0 ≤ (94307320 * h / 7257600 : ℝ) := by linarith
  have hc1_nn : 0 ≤ (20884811 * h / 7257600 : ℝ) := by linarith
  have hC_norm :
      ‖(30277247 * h / 7257600 : ℝ) • C‖ = (30277247 * h / 7257600) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc9_nn]
  have hD_norm :
      ‖(104995189 * h / 7257600 : ℝ) • D‖ = (104995189 * h / 7257600) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc8_nn]
  have hG_norm :
      ‖(265932680 * h / 7257600 : ℝ) • G‖ = (265932680 * h / 7257600) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc7_nn]
  have hJ_norm :
      ‖(454661776 * h / 7257600 : ℝ) • J‖ = (454661776 * h / 7257600) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc6_nn]
  have hK_norm :
      ‖(538363838 * h / 7257600 : ℝ) • K‖ = (538363838 * h / 7257600) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc5_nn]
  have hR_norm :
      ‖(444772162 * h / 7257600 : ℝ) • R‖ = (444772162 * h / 7257600) * ‖R‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc4_nn]
  have hS_norm :
      ‖(252618224 * h / 7257600 : ℝ) • S‖ = (252618224 * h / 7257600) * ‖S‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc3_nn]
  have hU_norm :
      ‖(94307320 * h / 7257600 : ℝ) • U‖ = (94307320 * h / 7257600) * ‖U‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc2_nn]
  have hV_norm :
      ‖(20884811 * h / 7257600 : ℝ) • V‖ = (20884811 * h / 7257600) * ‖V‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc1_nn]
  have htri := ab10Vec_triangle_aux A B
    ((30277247 * h / 7257600 : ℝ) • C) ((104995189 * h / 7257600 : ℝ) • D)
    ((265932680 * h / 7257600 : ℝ) • G) ((454661776 * h / 7257600 : ℝ) • J)
    ((538363838 * h / 7257600 : ℝ) • K) ((444772162 * h / 7257600 : ℝ) • R)
    ((252618224 * h / 7257600 : ℝ) • S) ((94307320 * h / 7257600 : ℝ) • U)
    ((20884811 * h / 7257600 : ℝ) • V)
  rw [hC_norm, hD_norm, hG_norm, hJ_norm, hK_norm, hR_norm, hS_norm, hU_norm,
    hV_norm] at htri
  exact htri

private lemma ab10Vec_residual_combine_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D G J K R S U V : E) (M h : ℝ) (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (hA_bd : ‖A‖ ≤ M / 39916800 * (10 * h) ^ 11)
    (hB_bd : ‖B‖ ≤ M / 39916800 * (9 * h) ^ 11)
    (hC_bd : ‖C‖ ≤ M / 3628800 * (9 * h) ^ 10)
    (hD_bd : ‖D‖ ≤ M / 3628800 * (8 * h) ^ 10)
    (hG_bd : ‖G‖ ≤ M / 3628800 * (7 * h) ^ 10)
    (hJ_bd : ‖J‖ ≤ M / 3628800 * (6 * h) ^ 10)
    (hK_bd : ‖K‖ ≤ M / 3628800 * (5 * h) ^ 10)
    (hR_bd : ‖R‖ ≤ M / 3628800 * (4 * h) ^ 10)
    (hS_bd : ‖S‖ ≤ M / 3628800 * (3 * h) ^ 10)
    (hU_bd : ‖U‖ ≤ M / 3628800 * (2 * h) ^ 10)
    (hV_bd : ‖V‖ ≤ M / 3628800 * h ^ 10) :
    ‖A - B - (30277247 * h / 7257600 : ℝ) • C
        + (104995189 * h / 7257600 : ℝ) • D
        - (265932680 * h / 7257600 : ℝ) • G
        + (454661776 * h / 7257600 : ℝ) • J
        - (538363838 * h / 7257600 : ℝ) • K
        + (444772162 * h / 7257600 : ℝ) • R
        - (252618224 * h / 7257600 : ℝ) • S
        + (94307320 * h / 7257600 : ℝ) • U
        - (20884811 * h / 7257600 : ℝ) • V‖
      ≤ 15695 * M * h ^ 11 := by
  have htri := ab10Vec_residual_eleven_term_triangle A B C D G J K R S U V h hh
  have hc9_nn : 0 ≤ 30277247 * h / 7257600 := by linarith
  have hc8_nn : 0 ≤ 104995189 * h / 7257600 := by linarith
  have hc7_nn : 0 ≤ 265932680 * h / 7257600 := by linarith
  have hc6_nn : 0 ≤ 454661776 * h / 7257600 := by linarith
  have hc5_nn : 0 ≤ 538363838 * h / 7257600 := by linarith
  have hc4_nn : 0 ≤ 444772162 * h / 7257600 := by linarith
  have hc3_nn : 0 ≤ 252618224 * h / 7257600 := by linarith
  have hc2_nn : 0 ≤ 94307320 * h / 7257600 := by linarith
  have hc1_nn : 0 ≤ 20884811 * h / 7257600 := by linarith
  have hCbd_s : (30277247 * h / 7257600) * ‖C‖
      ≤ (30277247 * h / 7257600) * (M / 3628800 * (9 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hC_bd hc9_nn
  have hDbd_s : (104995189 * h / 7257600) * ‖D‖
      ≤ (104995189 * h / 7257600) * (M / 3628800 * (8 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hD_bd hc8_nn
  have hGbd_s : (265932680 * h / 7257600) * ‖G‖
      ≤ (265932680 * h / 7257600) * (M / 3628800 * (7 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hG_bd hc7_nn
  have hJbd_s : (454661776 * h / 7257600) * ‖J‖
      ≤ (454661776 * h / 7257600) * (M / 3628800 * (6 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hJ_bd hc6_nn
  have hKbd_s : (538363838 * h / 7257600) * ‖K‖
      ≤ (538363838 * h / 7257600) * (M / 3628800 * (5 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hK_bd hc5_nn
  have hRbd_s : (444772162 * h / 7257600) * ‖R‖
      ≤ (444772162 * h / 7257600) * (M / 3628800 * (4 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hR_bd hc4_nn
  have hSbd_s : (252618224 * h / 7257600) * ‖S‖
      ≤ (252618224 * h / 7257600) * (M / 3628800 * (3 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hS_bd hc3_nn
  have hUbd_s : (94307320 * h / 7257600) * ‖U‖
      ≤ (94307320 * h / 7257600) * (M / 3628800 * (2 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hU_bd hc2_nn
  have hVbd_s : (20884811 * h / 7257600) * ‖V‖
      ≤ (20884811 * h / 7257600) * (M / 3628800 * h ^ 10) :=
    mul_le_mul_of_nonneg_left hV_bd hc1_nn
  have hbound_alg := ab10Vec_residual_bound_alg_identity M h
  have hh11_nn : 0 ≤ h ^ 11 := by positivity
  have hMh11_nn : 0 ≤ M * h ^ 11 := mul_nonneg hMnn hh11_nn
  have hslack : (11840488855359257 / 754427520000 : ℝ) * M * h ^ 11
      ≤ 15695 * M * h ^ 11 := by
    rw [mul_assoc, mul_assoc (15695 : ℝ)]
    have hle : (11840488855359257 / 754427520000 : ℝ) ≤ 15695 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh11_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hGbd_s,
    hJbd_s, hKbd_s, hRbd_s, hSbd_s, hUbd_s, hVbd_s]

theorem ab10Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindowVec (by norm_num : (1 : ℕ) ≤ 10) ab10GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉] y (n + 1)
      ≤ (1 + h * ((172570 / 567) * L))
          * abErrWindowVec (by norm_num : (1 : ℕ) ≤ 10) ab10GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉] y n
        + ‖abResidualVec 10 ab10GenericCoeff h y t₀ n‖ := by
  have hs : (1 : ℕ) ≤ 10 := by norm_num
  have hgeneric :=
    abIter_lipschitz_one_step_vec hs ab10GenericCoeff hh hL hf t₀
      ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉] y hyf n
  rw [abLip_ab10GenericCoeff L] at hgeneric
  exact hgeneric

theorem ab10Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindowVec (by norm_num : (1 : ℕ) ≤ 10) ab10GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉] y (n + 1)
      ≤ (1 + h * ((172570 / 567) * L))
          * abErrWindowVec (by norm_num : (1 : ℕ) ≤ 10) ab10GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉] y n
        + ‖abResidualVec 10 ab10GenericCoeff h y t₀ n‖ := by
  exact ab10Vec_one_step_lipschitz hh hL hf t₀
    y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y hyf n

private theorem ab10Vec_pointwise_residual_bound
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
    (ht10h : t + 10 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖ab10VecResidual h t y‖ ≤ (15695 : ℝ) * M * h ^ 11 := by
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
    y_eleventh_order_taylor_remainder_vec hy hbnd ht ht9h h9h
  have hRy10 :=
    y_eleventh_order_taylor_remainder_vec hy hbnd ht ht10h h10h
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
  unfold ab10VecResidual
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
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  set ddddd : E := iteratedDeriv 5 y t with hddddd_def
  set dddddd : E := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd : E := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd : E := iteratedDeriv 8 y t with hdddddddd_def
  set ddddddddd : E := iteratedDeriv 9 y t with hddddddddd_def
  set dddddddddd : E := iteratedDeriv 10 y t with hdddddddddd_def
  clear_value y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
    dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd dddddddddd
  have hLTE_eq :=
    ab10Vec_residual_alg_identity y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
      dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd dddddddddd h
  rw [hLTE_eq]
  set A : E := y10 - y0 - (10 * h) • d0
            - ((10 * h) ^ 2 / 2) • dd
            - ((10 * h) ^ 3 / 6) • ddd
            - ((10 * h) ^ 4 / 24) • dddd
            - ((10 * h) ^ 5 / 120) • ddddd
            - ((10 * h) ^ 6 / 720) • dddddd
            - ((10 * h) ^ 7 / 5040) • ddddddd
            - ((10 * h) ^ 8 / 40320) • dddddddd
            - ((10 * h) ^ 9 / 362880) • ddddddddd
            - ((10 * h) ^ 10 / 3628800) • dddddddddd with hA_def
  set B : E := y9 - y0 - (9 * h) • d0
            - ((9 * h) ^ 2 / 2) • dd
            - ((9 * h) ^ 3 / 6) • ddd
            - ((9 * h) ^ 4 / 24) • dddd
            - ((9 * h) ^ 5 / 120) • ddddd
            - ((9 * h) ^ 6 / 720) • dddddd
            - ((9 * h) ^ 7 / 5040) • ddddddd
            - ((9 * h) ^ 8 / 40320) • dddddddd
            - ((9 * h) ^ 9 / 362880) • ddddddddd
            - ((9 * h) ^ 10 / 3628800) • dddddddddd with hB_def
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
  set G : E := d7 - d0 - (7 * h) • dd
            - ((7 * h) ^ 2 / 2) • ddd
            - ((7 * h) ^ 3 / 6) • dddd
            - ((7 * h) ^ 4 / 24) • ddddd
            - ((7 * h) ^ 5 / 120) • dddddd
            - ((7 * h) ^ 6 / 720) • ddddddd
            - ((7 * h) ^ 7 / 5040) • dddddddd
            - ((7 * h) ^ 8 / 40320) • ddddddddd
            - ((7 * h) ^ 9 / 362880) • dddddddddd with hG_def
  set J : E := d6 - d0 - (6 * h) • dd
            - ((6 * h) ^ 2 / 2) • ddd
            - ((6 * h) ^ 3 / 6) • dddd
            - ((6 * h) ^ 4 / 24) • ddddd
            - ((6 * h) ^ 5 / 120) • dddddd
            - ((6 * h) ^ 6 / 720) • ddddddd
            - ((6 * h) ^ 7 / 5040) • dddddddd
            - ((6 * h) ^ 8 / 40320) • ddddddddd
            - ((6 * h) ^ 9 / 362880) • dddddddddd with hJ_def
  set K : E := d5 - d0 - (5 * h) • dd
            - ((5 * h) ^ 2 / 2) • ddd
            - ((5 * h) ^ 3 / 6) • dddd
            - ((5 * h) ^ 4 / 24) • ddddd
            - ((5 * h) ^ 5 / 120) • dddddd
            - ((5 * h) ^ 6 / 720) • ddddddd
            - ((5 * h) ^ 7 / 5040) • dddddddd
            - ((5 * h) ^ 8 / 40320) • ddddddddd
            - ((5 * h) ^ 9 / 362880) • dddddddddd with hK_def
  set R : E := d4 - d0 - (4 * h) • dd
            - ((4 * h) ^ 2 / 2) • ddd
            - ((4 * h) ^ 3 / 6) • dddd
            - ((4 * h) ^ 4 / 24) • ddddd
            - ((4 * h) ^ 5 / 120) • dddddd
            - ((4 * h) ^ 6 / 720) • ddddddd
            - ((4 * h) ^ 7 / 5040) • dddddddd
            - ((4 * h) ^ 8 / 40320) • ddddddddd
            - ((4 * h) ^ 9 / 362880) • dddddddddd with hR_def
  set S : E := d3 - d0 - (3 * h) • dd
            - ((3 * h) ^ 2 / 2) • ddd
            - ((3 * h) ^ 3 / 6) • dddd
            - ((3 * h) ^ 4 / 24) • ddddd
            - ((3 * h) ^ 5 / 120) • dddddd
            - ((3 * h) ^ 6 / 720) • ddddddd
            - ((3 * h) ^ 7 / 5040) • dddddddd
            - ((3 * h) ^ 8 / 40320) • ddddddddd
            - ((3 * h) ^ 9 / 362880) • dddddddddd with hS_def
  set U : E := d2 - d0 - (2 * h) • dd
            - ((2 * h) ^ 2 / 2) • ddd
            - ((2 * h) ^ 3 / 6) • dddd
            - ((2 * h) ^ 4 / 24) • ddddd
            - ((2 * h) ^ 5 / 120) • dddddd
            - ((2 * h) ^ 6 / 720) • ddddddd
            - ((2 * h) ^ 7 / 5040) • dddddddd
            - ((2 * h) ^ 8 / 40320) • ddddddddd
            - ((2 * h) ^ 9 / 362880) • dddddddddd with hU_def
  set V : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd
            - (h ^ 4 / 24) • ddddd
            - (h ^ 5 / 120) • dddddd
            - (h ^ 6 / 720) • ddddddd
            - (h ^ 7 / 5040) • dddddddd
            - (h ^ 8 / 40320) • ddddddddd
            - (h ^ 9 / 362880) • dddddddddd with hV_def
  clear_value A B C D G J K R S U V
  have hA_bd : ‖A‖ ≤ M / 39916800 * (10 * h) ^ 11 := hRy10
  have hB_bd : ‖B‖ ≤ M / 39916800 * (9 * h) ^ 11 := hRy9
  have hC_bd : ‖C‖ ≤ M / 3628800 * (9 * h) ^ 10 := hRyp9
  have hD_bd : ‖D‖ ≤ M / 3628800 * (8 * h) ^ 10 := hRyp8
  have hG_bd : ‖G‖ ≤ M / 3628800 * (7 * h) ^ 10 := hRyp7
  have hJ_bd : ‖J‖ ≤ M / 3628800 * (6 * h) ^ 10 := hRyp6
  have hK_bd : ‖K‖ ≤ M / 3628800 * (5 * h) ^ 10 := hRyp5
  have hR_bd : ‖R‖ ≤ M / 3628800 * (4 * h) ^ 10 := hRyp4
  have hS_bd : ‖S‖ ≤ M / 3628800 * (3 * h) ^ 10 := hRyp3
  have hU_bd : ‖U‖ ≤ M / 3628800 * (2 * h) ^ 10 := hRyp2
  have hV_bd : ‖V‖ ≤ M / 3628800 * h ^ 10 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  exact ab10Vec_residual_combine_aux A B C D G J K R S U V M h hh hMnn
    hA_bd hB_bd hC_bd hD_bd hG_bd hJ_bd hK_bd hR_bd hS_bd hU_bd hV_bd

theorem ab10Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 11 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 10) * h ≤ T →
        ‖ab10VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 11 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_eleven_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(15695 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
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
  show ‖ab10VecResidual h t y‖ ≤ 15695 * M * h ^ 11
  exact ab10Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem
    ht10h_mem hh.le

lemma ab10IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E) (n : ℕ) :
    ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n
      = abIterVec 10 ab10GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 0 = _
      rw [ab10IterVec_zero]
      unfold abIterVec
      simp
    | 1 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 1 = _
      rw [ab10IterVec_one]
      unfold abIterVec
      simp
    | 2 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 2 = _
      rw [ab10IterVec_two]
      unfold abIterVec
      simp
    | 3 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 3 = _
      rw [ab10IterVec_three]
      unfold abIterVec
      simp
    | 4 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 4 = _
      rw [ab10IterVec_four]
      unfold abIterVec
      simp
    | 5 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 5 = _
      rw [ab10IterVec_five]
      unfold abIterVec
      simp
    | 6 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 6 = _
      rw [ab10IterVec_six]
      unfold abIterVec
      simp
    | 7 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 7 = _
      rw [ab10IterVec_seven]
      unfold abIterVec
      simp
    | 8 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 8 = _
      rw [ab10IterVec_eight]
      unfold abIterVec
      simp
    | 9 =>
      show ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 9 = _
      rw [ab10IterVec_nine]
      unfold abIterVec
      simp
    | k + 10 =>
      rw [ab10IterVec_succ_ten]
      rw [abIterVec_step (s := 10) (by norm_num)
          ab10GenericCoeff h f t₀
            ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉] k]
      rw [show (k + 10 - 1 : ℕ) = k + 9 from by omega]
      rw [sum_univ_ten_aux]
      have hval3 : ((3 : Fin 10) : ℕ) = 3 := rfl
      have hval4 : ((4 : Fin 10) : ℕ) = 4 := rfl
      have hval5 : ((5 : Fin 10) : ℕ) = 5 := rfl
      have hval6 : ((6 : Fin 10) : ℕ) = 6 := rfl
      have hval7 : ((7 : Fin 10) : ℕ) = 7 := rfl
      have hval8 : ((8 : Fin 10) : ℕ) = 8 := rfl
      have hval9 : ((9 : Fin 10) : ℕ) = 9 := rfl
      simp only [ab10GenericCoeff_zero, ab10GenericCoeff_one,
        ab10GenericCoeff_two, ab10GenericCoeff_three, ab10GenericCoeff_four,
        ab10GenericCoeff_five, ab10GenericCoeff_six, ab10GenericCoeff_seven,
        ab10GenericCoeff_eight, ab10GenericCoeff_nine,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5, hval6,
        hval7, hval8, hval9, Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega), ← ih (k + 4) (by omega),
        ← ih (k + 5) (by omega), ← ih (k + 6) (by omega),
        ← ih (k + 7) (by omega), ← ih (k + 8) (by omega),
        ← ih (k + 9) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring,
        show ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 by push_cast; ring,
        show ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring,
        show ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 by push_cast; ring,
        show ((k + 7 : ℕ) : ℝ) = (k : ℝ) + 7 by push_cast; ring,
        show ((k + 8 : ℕ) : ℝ) = (k : ℝ) + 8 by push_cast; ring,
        show ((k + 9 : ℕ) : ℝ) = (k : ℝ) + 9 by push_cast; ring]
      rw [show (-(2082753 : ℝ) / 7257600) •
              f (t₀ + (k : ℝ) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ k)
            = -((2082753 / 7257600 : ℝ) •
              f (t₀ + (k : ℝ) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ k)) by
        rw [show (-(2082753 : ℝ) / 7257600) = -(2082753 / 7257600 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(94307320 : ℝ) / 7257600) •
              f (t₀ + ((k : ℝ) + 2) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (k + 2))
            = -((94307320 / 7257600 : ℝ) •
              f (t₀ + ((k : ℝ) + 2) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (k + 2))) by
        rw [show (-(94307320 : ℝ) / 7257600) = -(94307320 / 7257600 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(444772162 : ℝ) / 7257600) •
              f (t₀ + ((k : ℝ) + 4) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (k + 4))
            = -((444772162 / 7257600 : ℝ) •
              f (t₀ + ((k : ℝ) + 4) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (k + 4))) by
        rw [show (-(444772162 : ℝ) / 7257600) = -(444772162 / 7257600 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(454661776 : ℝ) / 7257600) •
              f (t₀ + ((k : ℝ) + 6) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (k + 6))
            = -((454661776 / 7257600 : ℝ) •
              f (t₀ + ((k : ℝ) + 6) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (k + 6))) by
        rw [show (-(454661776 : ℝ) / 7257600) = -(454661776 / 7257600 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(104995189 : ℝ) / 7257600) •
              f (t₀ + ((k : ℝ) + 8) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (k + 8))
            = -((104995189 / 7257600 : ℝ) •
              f (t₀ + ((k : ℝ) + 8) * h)
                (ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (k + 8))) by
        rw [show (-(104995189 : ℝ) / 7257600) = -(104995189 / 7257600 : ℝ) by ring]
        exact neg_smul _ _]
      abel_nf

lemma ab10VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab10VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 10 ab10GenericCoeff h y t₀ n := by
  unfold ab10VecResidual abResidualVec
  rw [sum_univ_ten_aux, ab10GenericCoeff_zero, ab10GenericCoeff_one,
    ab10GenericCoeff_two, ab10GenericCoeff_three, ab10GenericCoeff_four,
    ab10GenericCoeff_five, ab10GenericCoeff_six, ab10GenericCoeff_seven,
    ab10GenericCoeff_eight, ab10GenericCoeff_nine]
  have eA : t₀ + (n : ℝ) * h + 10 * h = t₀ + ((n + 10 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 9 * h = t₀ + ((n + 10 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 10 - 1 : ℕ) = n + 9 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 10) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 10) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 10) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 10) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  have eJ : t₀ + (n : ℝ) * h + 7 * h
      = t₀ + ((n + ((7 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((7 : Fin 10) : ℕ) = 7 := rfl
    rw [this]; push_cast; ring
  have eK : t₀ + (n : ℝ) * h + 8 * h
      = t₀ + ((n + ((8 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((8 : Fin 10) : ℕ) = 8 := rfl
    rw [this]; push_cast; ring
  have eL : t₀ + (n : ℝ) * h + 9 * h
      = t₀ + ((n + ((9 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((9 : Fin 10) : ℕ) = 9 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI, ← eJ, ← eK, ← eL]
  rw [show (-(2082753 : ℝ) / 7257600) • deriv y (t₀ + (n : ℝ) * h)
        = -((2082753 / 7257600 : ℝ) • deriv y (t₀ + (n : ℝ) * h)) by
    rw [show (-(2082753 : ℝ) / 7257600) = -(2082753 / 7257600 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(94307320 : ℝ) / 7257600) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
        = -((94307320 / 7257600 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)) by
    rw [show (-(94307320 : ℝ) / 7257600) = -(94307320 / 7257600 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(444772162 : ℝ) / 7257600) • deriv y (t₀ + (n : ℝ) * h + 4 * h)
        = -((444772162 / 7257600 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 4 * h)) by
    rw [show (-(444772162 : ℝ) / 7257600) = -(444772162 / 7257600 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(454661776 : ℝ) / 7257600) • deriv y (t₀ + (n : ℝ) * h + 6 * h)
        = -((454661776 / 7257600 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 6 * h)) by
    rw [show (-(454661776 : ℝ) / 7257600) = -(454661776 / 7257600 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(104995189 : ℝ) / 7257600) • deriv y (t₀ + (n : ℝ) * h + 8 * h)
        = -((104995189 / 7257600 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 8 * h)) by
    rw [show (-(104995189 : ℝ) / 7257600) = -(104995189 / 7257600 : ℝ) by ring]
    exact neg_smul _ _]
  abel_nf

theorem ab10Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 11 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
      ‖y₀ - y t₀‖ ≤ ε₀ → ‖y₁ - y (t₀ + h)‖ ≤ ε₀ →
      ‖y₂ - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖y₃ - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖y₄ - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖y₅ - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖y₆ - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ‖y₇ - y (t₀ + 7 * h)‖ ≤ ε₀ →
      ‖y₈ - y (t₀ + 8 * h)‖ ≤ ε₀ →
      ‖y₉ - y (t₀ + 9 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 9) * h ≤ T →
      ‖ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N
          - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((172570 / 567) * L * T) * ε₀ + K * h ^ 10 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab10Vec_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((172570 / 567) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd N hNh
  set α : Fin 10 → ℝ := ab10GenericCoeff with hα_def
  set y₀_non : Fin 10 → E := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉]
    with hy_non_def
  have hs : (1 : ℕ) ≤ 10 := by norm_num
  haveI : Nonempty (Fin 10) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIterVec 10 α h f t₀ y₀_non 0 = y₀ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter1 : abIterVec 10 α h f t₀ y₀_non 1 = y₁ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter2 : abIterVec 10 α h f t₀ y₀_non 2 = y₂ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter3 : abIterVec 10 α h f t₀ y₀_non 3 = y₃ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter4 : abIterVec 10 α h f t₀ y₀_non 4 = y₄ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter5 : abIterVec 10 α h f t₀ y₀_non 5 = y₅ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter6 : abIterVec 10 α h f t₀ y₀_non 6 = y₆ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter7 : abIterVec 10 α h f t₀ y₀_non 7 = y₇ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter8 : abIterVec 10 α h f t₀ y₀_non 8 = y₈ := by
    unfold abIterVec; simp [hy_non_def]
  have hiter9 : abIterVec 10 α h f t₀ y₀_non 9 = y₉ := by
    unfold abIterVec; simp [hy_non_def]
  have hstart : abErrWindowVec hs α h f t₀ y₀_non y 0 ≤ ε₀ := by
    unfold abErrWindowVec
    apply Finset.sup'_le
    intro j _
    show abErrVec 10 α h f t₀ y₀_non y (0 + (j : ℕ)) ≤ ε₀
    unfold abErrVec
    fin_cases j
    · show ‖abIterVec 10 α h f t₀ y₀_non 0
          - y (t₀ + ((0 + (((0 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]; exact he0_bd
    · show ‖abIterVec 10 α h f t₀ y₀_non 1
          - y (t₀ + ((0 + (((1 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]; exact he1_bd
    · show ‖abIterVec 10 α h f t₀ y₀_non 2
          - y (t₀ + ((0 + (((2 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]; exact he2_bd
    · show ‖abIterVec 10 α h f t₀ y₀_non 3
          - y (t₀ + ((0 + (((3 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 10) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]; exact he3_bd
    · show ‖abIterVec 10 α h f t₀ y₀_non 4
          - y (t₀ + ((0 + (((4 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter4]
      have hval4 : ((4 : Fin 10) : ℕ) = 4 := rfl
      have : ((0 + (((4 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval4]; push_cast; ring
      rw [this]; exact he4_bd
    · show ‖abIterVec 10 α h f t₀ y₀_non 5
          - y (t₀ + ((0 + (((5 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter5]
      have hval5 : ((5 : Fin 10) : ℕ) = 5 := rfl
      have : ((0 + (((5 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval5]; push_cast; ring
      rw [this]; exact he5_bd
    · show ‖abIterVec 10 α h f t₀ y₀_non 6
          - y (t₀ + ((0 + (((6 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter6]
      have hval6 : ((6 : Fin 10) : ℕ) = 6 := rfl
      have : ((0 + (((6 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 6 := by
        rw [hval6]; push_cast; ring
      rw [this]; exact he6_bd
    · show ‖abIterVec 10 α h f t₀ y₀_non 7
          - y (t₀ + ((0 + (((7 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter7]
      have hval7 : ((7 : Fin 10) : ℕ) = 7 := rfl
      have : ((0 + (((7 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 7 := by
        rw [hval7]; push_cast; ring
      rw [this]; exact he7_bd
    · show ‖abIterVec 10 α h f t₀ y₀_non 8
          - y (t₀ + ((0 + (((8 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter8]
      have hval8 : ((8 : Fin 10) : ℕ) = 8 := rfl
      have : ((0 + (((8 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 8 := by
        rw [hval8]; push_cast; ring
      rw [this]; exact he8_bd
    · show ‖abIterVec 10 α h f t₀ y₀_non 9
          - y (t₀ + ((0 + (((9 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter9]
      have hval9 : ((9 : Fin 10) : ℕ) = 9 := rfl
      have : ((0 + (((9 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 9 := by
        rw [hval9]; push_cast; ring
      rw [this]; exact he9_bd
  have hres_gen : ∀ n : ℕ, n < N →
      ‖abResidualVec 10 α h y t₀ n‖ ≤ C * h ^ (10 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 10 ≤ (N : ℝ) + 9 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn10_le : ((n : ℝ) + 10) * h ≤ T := by
      have hmul : ((n : ℝ) + 10) * h ≤ ((N : ℝ) + 9) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn10_le
    rw [hα_def, ← ab10VecResidual_eq_abResidualVec (E := E) h y t₀ n]
    simpa using hres
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 9) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 9 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic_vec (p := 10) hs α hh.le hL hC_nn hf t₀
      y₀_non y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 10 α L = (172570 / 567) * L from by
    rw [hα_def]; exact abLip_ab10GenericCoeff L] at hgeneric
  have hwindow_ge : abErrVec 10 α h f t₀ y₀_non y N
      ≤ abErrWindowVec hs α h f t₀ y₀_non y N := by
    show abErrVec 10 α h f t₀ y₀_non y (N + ((⟨0, hs⟩ : Fin 10) : ℕ))
        ≤ abErrWindowVec hs α h f t₀ y₀_non y N
    unfold abErrWindowVec
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 10 => abErrVec 10 α h f t₀ y₀_non y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIterVec 10 α h f t₀ y₀_non N
        = ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N := by
    rw [hα_def, hy_non_def]
    exact (ab10IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N).symm
  have habsErr :
      abErrVec 10 α h f t₀ y₀_non y N
        = ‖ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N
            - y (t₀ + (N : ℝ) * h)‖ := by
    show ‖abIterVec 10 α h f t₀ y₀_non N - y (t₀ + (N : ℝ) * h)‖
        = ‖ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N
            - y (t₀ + (N : ℝ) * h)‖
    rw [hbridge]
  show ‖ab10IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N
        - y (t₀ + (N : ℝ) * h)‖
      ≤ Real.exp ((172570 / 567) * L * T) * ε₀
        + T * Real.exp ((172570 / 567) * L * T) * C * h ^ 10
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
