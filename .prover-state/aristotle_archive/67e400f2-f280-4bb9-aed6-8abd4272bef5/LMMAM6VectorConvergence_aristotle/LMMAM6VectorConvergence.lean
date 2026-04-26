import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB6VectorConvergence

/-! ## Adams--Moulton 6-step Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the AM6 scalar quantitative convergence chain in
`OpenMath/LMMAM6Convergence.lean`. The implicit AM6 update is parameterised
by a supplied trajectory; existence of such a trajectory is a separate
fixed-point problem and is not part of this chain.
-/

namespace LMM

/-- AM6 vector trajectory predicate:
`y_{n+6} = y_{n+5} + h • (19087/60480 f_{n+6} + 65112/60480 f_{n+5}
  - 46461/60480 f_{n+4} + 37504/60480 f_{n+3} - 20211/60480 f_{n+2}
  + 6312/60480 f_{n+1} - 863/60480 f_n)`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM6TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 6)
      = y (n + 5)
        + h • ((19087 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             + (65112 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             - (46461 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             + (37504 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             - (20211 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             + (6312 / 60480 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             - (863 / 60480 : ℝ) • f (t₀ + (n : ℝ) * h) (y n))

/-- Textbook AM6 vector residual: the value of the local truncation error of
the AM6 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def am6VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 6 * h) - y (t + 5 * h)
    - h • ((19087 / 60480 : ℝ) • deriv y (t + 6 * h)
          + (65112 / 60480 : ℝ) • deriv y (t + 5 * h)
          - (46461 / 60480 : ℝ) • deriv y (t + 4 * h)
          + (37504 / 60480 : ℝ) • deriv y (t + 3 * h)
          - (20211 / 60480 : ℝ) • deriv y (t + 2 * h)
          + (6312 / 60480 : ℝ) • deriv y (t + h)
          - (863 / 60480 : ℝ) • deriv y t)

/-- The vector AM6 residual unfolds to the textbook form. -/
theorem am6Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am6VecResidual h t y
      = y (t + 6 * h) - y (t + 5 * h)
          - h • ((19087 / 60480 : ℝ) • deriv y (t + 6 * h)
                + (65112 / 60480 : ℝ) • deriv y (t + 5 * h)
                - (46461 / 60480 : ℝ) • deriv y (t + 4 * h)
                + (37504 / 60480 : ℝ) • deriv y (t + 3 * h)
                - (20211 / 60480 : ℝ) • deriv y (t + 2 * h)
                + (6312 / 60480 : ℝ) • deriv y (t + h)
                - (863 / 60480 : ℝ) • deriv y t) := by
  rfl

theorem am6Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (19087 / 60480 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM6TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (19087 / 60480 : ℝ) * h * L)
        * ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
      ≤ ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (65112 / 60480 : ℝ) * h * L
            * ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (46461 / 60480 : ℝ) * h * L
            * ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (37504 / 60480 : ℝ) * h * L
            * ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (20211 / 60480 : ℝ) * h * L
            * ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (6312 / 60480 : ℝ) * h * L
            * ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (863 / 60480 : ℝ) * h * L
            * ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + ‖am6VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  sorry

theorem am6Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (19087 / 60480 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM6TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
      ≤ (1 + h * (7 * L))
            * max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
        + 2 * ‖am6VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  sorry

theorem am6Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (19087 / 60480 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM6TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max
          ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
          ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
      ≤ (1 + h * (7 * L))
            * max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
        + 2 * ‖am6VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  sorry

private theorem iteratedDeriv_eight_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 8 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 8 y t‖ ≤ M := by
  sorry

private theorem y_eighth_order_taylor_remainder_vec
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
  sorry

private theorem derivY_seventh_order_taylor_remainder_vec
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
  sorry

private lemma am6Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y5 y6 d0 d1 d2 d3 d4 d5 d6 dd ddd dddd ddddd dddddd ddddddd : E)
    (h : ℝ) :
    y6 - y5 - h • ((19087 / 60480 : ℝ) • d6 + (65112 / 60480 : ℝ) • d5
                  - (46461 / 60480 : ℝ) • d4 + (37504 / 60480 : ℝ) • d3
                  - (20211 / 60480 : ℝ) • d2 + (6312 / 60480 : ℝ) • d1
                  - (863 / 60480 : ℝ) • d0)
      = (y6 - y0 - (6 * h) • d0
            - ((6 * h) ^ 2 / 2) • dd
            - ((6 * h) ^ 3 / 6) • ddd
            - ((6 * h) ^ 4 / 24) • dddd
            - ((6 * h) ^ 5 / 120) • ddddd
            - ((6 * h) ^ 6 / 720) • dddddd
            - ((6 * h) ^ 7 / 5040) • ddddddd)
        - (y5 - y0 - (5 * h) • d0
            - ((5 * h) ^ 2 / 2) • dd
            - ((5 * h) ^ 3 / 6) • ddd
            - ((5 * h) ^ 4 / 24) • dddd
            - ((5 * h) ^ 5 / 120) • ddddd
            - ((5 * h) ^ 6 / 720) • dddddd
            - ((5 * h) ^ 7 / 5040) • ddddddd)
        - (19087 * h / 60480 : ℝ)
            • (d6 - d0 - (6 * h) • dd
                - ((6 * h) ^ 2 / 2) • ddd
                - ((6 * h) ^ 3 / 6) • dddd
                - ((6 * h) ^ 4 / 24) • ddddd
                - ((6 * h) ^ 5 / 120) • dddddd
                - ((6 * h) ^ 6 / 720) • ddddddd)
        - (65112 * h / 60480 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd
                - ((5 * h) ^ 6 / 720) • ddddddd)
        + (46461 * h / 60480 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd
                - ((4 * h) ^ 6 / 720) • ddddddd)
        - (37504 * h / 60480 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd
                - ((3 * h) ^ 6 / 720) • ddddddd)
        + (20211 * h / 60480 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd
                - ((2 * h) ^ 6 / 720) • ddddddd)
        - (6312 * h / 60480 : ℝ)
            • (d1 - d0 - h • dd
                - (h ^ 2 / 2) • ddd
                - (h ^ 3 / 6) • dddd
                - (h ^ 4 / 24) • ddddd
                - (h ^ 5 / 120) • dddddd
                - (h ^ 6 / 720) • ddddddd) := by
  sorry

private lemma am6Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 40320 * (6 * h) ^ 8 + M / 40320 * (5 * h) ^ 8
      + (19087 * h / 60480) * (M / 5040 * (6 * h) ^ 7)
      + (65112 * h / 60480) * (M / 5040 * (5 * h) ^ 7)
      + (46461 * h / 60480) * (M / 5040 * (4 * h) ^ 7)
      + (37504 * h / 60480) * (M / 5040 * (3 * h) ^ 7)
      + (20211 * h / 60480) * (M / 5040 * (2 * h) ^ 7)
      + (6312 * h / 60480) * (M / 5040 * h ^ 7)
      = (1121952791 / 12700800 : ℝ) * M * h ^ 8 := by
  sorry

private lemma am6Vec_residual_eight_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D G J K R : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (19087 * h / 60480 : ℝ) • C - (65112 * h / 60480 : ℝ) • D
        + (46461 * h / 60480 : ℝ) • G - (37504 * h / 60480 : ℝ) • J
        + (20211 * h / 60480 : ℝ) • K - (6312 * h / 60480 : ℝ) • R‖
      ≤ ‖A‖ + ‖B‖ + (19087 * h / 60480) * ‖C‖
          + (65112 * h / 60480) * ‖D‖ + (46461 * h / 60480) * ‖G‖
          + (37504 * h / 60480) * ‖J‖ + (20211 * h / 60480) * ‖K‖
          + (6312 * h / 60480) * ‖R‖ := by
  sorry

private lemma am6Vec_residual_combine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D G J K R : E)
    (htri : ‖A - B - (19087 * h / 60480 : ℝ) • C
              - (65112 * h / 60480 : ℝ) • D + (46461 * h / 60480 : ℝ) • G
              - (37504 * h / 60480 : ℝ) • J + (20211 * h / 60480 : ℝ) • K
              - (6312 * h / 60480 : ℝ) • R‖
            ≤ ‖A‖ + ‖B‖ + (19087 * h / 60480) * ‖C‖
              + (65112 * h / 60480) * ‖D‖ + (46461 * h / 60480) * ‖G‖
              + (37504 * h / 60480) * ‖J‖ + (20211 * h / 60480) * ‖K‖
              + (6312 * h / 60480) * ‖R‖)
    (hA_bd : ‖A‖ ≤ M / 40320 * (6 * h) ^ 8)
    (hB_bd : ‖B‖ ≤ M / 40320 * (5 * h) ^ 8)
    (hC_bd : ‖C‖ ≤ M / 5040 * (6 * h) ^ 7)
    (hD_bd : ‖D‖ ≤ M / 5040 * (5 * h) ^ 7)
    (hG_bd : ‖G‖ ≤ M / 5040 * (4 * h) ^ 7)
    (hJ_bd : ‖J‖ ≤ M / 5040 * (3 * h) ^ 7)
    (hK_bd : ‖K‖ ≤ M / 5040 * (2 * h) ^ 7)
    (hR_bd : ‖R‖ ≤ M / 5040 * h ^ 7) :
    ‖A - B - (19087 * h / 60480 : ℝ) • C - (65112 * h / 60480 : ℝ) • D
        + (46461 * h / 60480 : ℝ) • G - (37504 * h / 60480 : ℝ) • J
        + (20211 * h / 60480 : ℝ) • K - (6312 * h / 60480 : ℝ) • R‖
      ≤ (89 : ℝ) * M * h ^ 8 := by
  -- Substitute the upper bounds from hA_bd, hB_bd, etc. into the right-hand side of htri.
  have h_subst : ‖A‖ + ‖B‖ + (19087 * h / 60480) * ‖C‖ + (65112 * h / 60480) * ‖D‖ + (46461 * h / 60480) * ‖G‖ + (37504 * h / 60480) * ‖J‖ + (20211 * h / 60480) * ‖K‖ + (6312 * h / 60480) * ‖R‖ ≤ (1121952791 / 12700800 : ℝ) * M * h ^ 8 := by
    refine le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( add_le_add hA_bd hB_bd ) ( mul_le_mul_of_nonneg_left hC_bd <| by positivity ) ) ( mul_le_mul_of_nonneg_left hD_bd <| by positivity ) ) ( mul_le_mul_of_nonneg_left hG_bd <| by positivity ) ) ( mul_le_mul_of_nonneg_left hJ_bd <| by positivity ) ) ( mul_le_mul_of_nonneg_left hK_bd <| by positivity ) ) ( mul_le_mul_of_nonneg_left hR_bd <| by positivity ) ) ?_ ; ring_nf ; norm_num;
  exact htri.trans ( h_subst.trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( by norm_num ) hMnn ) ( by positivity ) ) )

theorem am6Vec_pointwise_residual_bound
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
    (hh : 0 ≤ h) :
    ‖y (t + 6 * h) - y (t + 5 * h)
        - h • ((19087 / 60480 : ℝ) • deriv y (t + 6 * h)
              + (65112 / 60480 : ℝ) • deriv y (t + 5 * h)
              - (46461 / 60480 : ℝ) • deriv y (t + 4 * h)
              + (37504 / 60480 : ℝ) • deriv y (t + 3 * h)
              - (20211 / 60480 : ℝ) • deriv y (t + 2 * h)
              + (6312 / 60480 : ℝ) • deriv y (t + h)
              - (863 / 60480 : ℝ) • deriv y t)‖
      ≤ (89 : ℝ) * M * h ^ 8 := by
  sorry

theorem am6Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 8 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 6) * h ≤ T →
        ‖am6VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 8 := by
  sorry

theorem am6Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 8 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (19087 / 60480 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsAM6TrajectoryVec h f t₀ yseq →
      0 ≤ ε₀ →
      ‖yseq 0 - y t₀‖ ≤ ε₀ →
      ‖yseq 1 - y (t₀ + h)‖ ≤ ε₀ →
      ‖yseq 2 - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖yseq 3 - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖yseq 4 - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖yseq 5 - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 5) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((7 * L) * T) * ε₀ + K * h ^ 7 := by
  sorry

end LMM
