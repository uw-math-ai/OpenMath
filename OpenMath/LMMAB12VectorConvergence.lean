import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB12Convergence
import OpenMath.LMMAB11VectorConvergence

/-! ## Adams-Bashforth 12-step Vector Quantitative Convergence Chain (Iserles §1.2)

Finite-dimensional vector-valued analogue of the scalar AB12 quantitative
convergence chain in `OpenMath.LMMAB12Convergence`.

Sorry-first scaffold (cycle 480): correct AB12 signatures with `sorry` in proofs
that require AB12-specific algebra; closure of remaining sorries is scheduled for
cycle 481+ following the same parameterized abstract-remainder pattern as
`LMMAB11VectorConvergence`.
-/

namespace LMM

/-- Helper: expand `∑ i : Fin 12, f i` as twelve summands. -/
private lemma sum_univ_twelve_aux_vec {α : Type*} [AddCommMonoid α] (f : Fin 12 → α) :
    ∑ i : Fin 12, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp [Fin.sum_univ_succ]
  ac_rfl

/-- AB12 vector iteration with twelve starting samples. -/
noncomputable def ab12IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) : ℕ → E
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
  | 10 => y₁₀
  | 11 => y₁₁
  | n + 12 =>
      ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 11)
        + h • ((4527766399 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 11) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 11))
              - (19433810163 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 10) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 10))
              + (61633227185 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 9) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 9))
              - (135579356757 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 8))
              + (214139355366 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 7))
              - (247741639374 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 6))
              + (211103573298 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 5))
              - (131365867290 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 4))
              + (58189107627 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 3))
              - (17410248271 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 2))
              + (3158642445 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 1))
              - (262747265 / 958003200 : ℝ) • f (t₀ + (n : ℝ) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ n))

@[simp] lemma ab12IterVec_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 0 = y₀ := rfl

@[simp] lemma ab12IterVec_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 1 = y₁ := rfl

@[simp] lemma ab12IterVec_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 2 = y₂ := rfl

@[simp] lemma ab12IterVec_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 3 = y₃ := rfl

@[simp] lemma ab12IterVec_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 4 = y₄ := rfl

@[simp] lemma ab12IterVec_five
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 5 = y₅ := rfl

@[simp] lemma ab12IterVec_six
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 6 = y₆ := rfl

@[simp] lemma ab12IterVec_seven
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 7 = y₇ := rfl

@[simp] lemma ab12IterVec_eight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 8 = y₈ := rfl

@[simp] lemma ab12IterVec_nine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 9 = y₉ := rfl

@[simp] lemma ab12IterVec_ten
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 10 = y₁₀ := rfl

@[simp] lemma ab12IterVec_eleven
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 11 = y₁₁ := rfl

lemma ab12IterVec_succ_twelve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) (n : ℕ) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 12)
      = ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 11)
        + h • ((4527766399 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 11) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 11))
              - (19433810163 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 10) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 10))
              + (61633227185 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 9) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 9))
              - (135579356757 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 8))
              + (214139355366 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 7))
              - (247741639374 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 6))
              + (211103573298 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 5))
              - (131365867290 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 4))
              + (58189107627 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 3))
              - (17410248271 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 2))
              + (3158642445 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 1))
              - (262747265 / 958003200 : ℝ) • f (t₀ + (n : ℝ) * h)
                (ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ n)) := rfl

/-- Vector AB12 local truncation residual. -/
noncomputable def ab12VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 12 * h) - y (t + 11 * h)
    - h • ((4527766399 / 958003200 : ℝ) • deriv y (t + 11 * h)
          - (19433810163 / 958003200 : ℝ) • deriv y (t + 10 * h)
          + (61633227185 / 958003200 : ℝ) • deriv y (t + 9 * h)
          - (135579356757 / 958003200 : ℝ) • deriv y (t + 8 * h)
          + (214139355366 / 958003200 : ℝ) • deriv y (t + 7 * h)
          - (247741639374 / 958003200 : ℝ) • deriv y (t + 6 * h)
          + (211103573298 / 958003200 : ℝ) • deriv y (t + 5 * h)
          - (131365867290 / 958003200 : ℝ) • deriv y (t + 4 * h)
          + (58189107627 / 958003200 : ℝ) • deriv y (t + 3 * h)
          - (17410248271 / 958003200 : ℝ) • deriv y (t + 2 * h)
          + (3158642445 / 958003200 : ℝ) • deriv y (t + h)
          - (262747265 / 958003200 : ℝ) • deriv y t)

theorem ab12Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab12VecResidual h t y
      = y (t + 12 * h) - y (t + 11 * h)
          - h • ((4527766399 / 958003200 : ℝ) • deriv y (t + 11 * h)
                - (19433810163 / 958003200 : ℝ) • deriv y (t + 10 * h)
                + (61633227185 / 958003200 : ℝ) • deriv y (t + 9 * h)
                - (135579356757 / 958003200 : ℝ) • deriv y (t + 8 * h)
                + (214139355366 / 958003200 : ℝ) • deriv y (t + 7 * h)
                - (247741639374 / 958003200 : ℝ) • deriv y (t + 6 * h)
                + (211103573298 / 958003200 : ℝ) • deriv y (t + 5 * h)
                - (131365867290 / 958003200 : ℝ) • deriv y (t + 4 * h)
                + (58189107627 / 958003200 : ℝ) • deriv y (t + 3 * h)
                - (17410248271 / 958003200 : ℝ) • deriv y (t + 2 * h)
                + (3158642445 / 958003200 : ℝ) • deriv y (t + h)
                - (262747265 / 958003200 : ℝ) • deriv y t) := rfl

/-! ### Thirteenth-order vector Taylor helpers (public, for AM11 / AB13 reuse) -/

/-- A `C^13` vector function has its thirteenth iterated derivative bounded on
every compact interval. -/
theorem iteratedDeriv_thirteen_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 13 y t‖ ≤ M := by
  have h_cont : Continuous (iteratedDeriv 13 y) :=
    hy.continuous_iteratedDeriv 13 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

theorem y_thirteenth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 13 y t‖ ≤ M)
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
        - (r ^ 10 / 3628800) • iteratedDeriv 10 y t
        - (r ^ 11 / 39916800) • iteratedDeriv 11 y t
        - (r ^ 12 / 479001600) • iteratedDeriv 12 y t‖
      ≤ M / 6227020800 * r ^ 13 := by
  sorry

theorem derivY_twelfth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 13 y t‖ ≤ M)
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
        - (r ^ 9 / 362880) • iteratedDeriv 10 y t
        - (r ^ 10 / 3628800) • iteratedDeriv 11 y t
        - (r ^ 11 / 39916800) • iteratedDeriv 12 y t‖
      ≤ M / 479001600 * r ^ 12 := by
  sorry

/-! ### AB12 vector residual algebra and bounds -/

-- Parameterized abstract-remainder algebra identity for the AB12 vector
-- residual: full closure scheduled for cycle 481. The 13-witness
-- `set`/`clear_value` consumer pattern from `LMMAB11VectorConvergence` will
-- be ported with one extra abstract witness. The giant signature is omitted
-- here to keep the scaffold within the 200K heartbeat budget; the residual
-- bound below uses `sorry` directly until then.


/-- Pointwise residual bound (sorry-stub; AB12 algebra closure is scheduled
for cycle 481). -/
private theorem ab12Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 13 y t‖ ≤ M)
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
    (ht11h : t + 11 * h ∈ Set.Icc a b)
    (ht12h : t + 12 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖ab12VecResidual h t y‖ ≤ (162031 : ℝ) * M * h ^ 13 := by
  sorry

theorem ab12Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y)
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ n : ℕ, ((n : ℝ) + 12) * h ≤ T →
      ‖ab12VecResidual h (t₀ + (n : ℝ) * h) y‖ ≤ C * h ^ (12 + 1) := by
  sorry

/-! ### One-step Lipschitz / error bound -/

theorem ab12Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindowVec (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y (n + 1)
      ≤ (1 + h * ((443892 / 385) * L))
          * abErrWindowVec (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y n
        + ‖abResidualVec 12 ab12GenericCoeff h y t₀ n‖ := by
  have hs : (1 : ℕ) ≤ 12 := by norm_num
  have hgeneric :=
    abIter_lipschitz_one_step_vec hs ab12GenericCoeff hh hL hf t₀
      ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y hyf n
  rw [abLip_ab12GenericCoeff L] at hgeneric
  exact hgeneric

theorem ab12Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindowVec (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y (n + 1)
      ≤ (1 + h * ((443892 / 385) * L))
          * abErrWindowVec (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y n
        + ‖abResidualVec 12 ab12GenericCoeff h y t₀ n‖ := by
  exact ab12Vec_one_step_lipschitz hh hL hf t₀
    y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y hyf n

/-! ### Bridges to the generic AB scaffold -/

lemma ab12IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E) (n : ℕ) :
    ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ n
      = abIterVec 12 ab12GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] n := by
  sorry

lemma ab12VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab12VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 12 ab12GenericCoeff h y t₀ n := by
  sorry

/-! ### Headline global error bound -/

theorem ab12Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
      ‖y₀ - y t₀‖ ≤ ε₀ → ‖y₁ - y (t₀ + h)‖ ≤ ε₀ →
      ‖y₂ - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖y₃ - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖y₄ - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖y₅ - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖y₆ - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ‖y₇ - y (t₀ + 7 * h)‖ ≤ ε₀ →
      ‖y₈ - y (t₀ + 8 * h)‖ ≤ ε₀ →
      ‖y₉ - y (t₀ + 9 * h)‖ ≤ ε₀ →
      ‖y₁₀ - y (t₀ + 10 * h)‖ ≤ ε₀ →
      ‖y₁₁ - y (t₀ + 11 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 11) * h ≤ T →
      ‖ab12IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N
          - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((443892 / 385) * L * T) * ε₀ + K * h ^ 12 := by
  sorry

end LMM
