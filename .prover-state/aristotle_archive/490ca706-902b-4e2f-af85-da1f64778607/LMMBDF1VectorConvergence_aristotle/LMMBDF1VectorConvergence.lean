import Mathlib

/-! ## Backward Euler (BDF1) Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the scalar BDF1 quantitative convergence chain in
`OpenMath/LMMBDF1Convergence.lean`.  The implicit update is parameterised by a
supplied trajectory satisfying the backward-Euler recurrence; existence of such
a fixed point is a separate frontier theorem and is not part of this chain.

The vector files in this development use a method-specific vector residual
instead of `LMM.localTruncationError`, which is currently scalar-valued.
-/

namespace LMM

/-- BDF1 vector trajectory predicate:
`y_{n+1} = y_n + h • f(t_{n+1}, y_{n+1})`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF1TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 1)
      = y n + h • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))

/-- Textbook BDF1 vector residual: the value of the one-step local residual
on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def bdf1VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + h) - y t - h • deriv y (t + h)

/-- The vector BDF1 residual unfolds to the textbook one-step form. -/
theorem bdf1Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    bdf1VecResidual h t y = y (t + h) - y t - h • deriv y (t + h) := rfl

/-- One-step BDF1 Lipschitz inequality before dividing by the implicit
new-point factor.  The side condition records the small-step regime used by
the divided form. -/
theorem bdf1Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsBDF1TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - h * L)
        * ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
      ≤ ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + ‖bdf1VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  sorry

/-
Divided one-step BDF1 vector error bound.  The effective Lipschitz
constant is slackened to `2L`; under `h·L ≤ 1/2`, the local residual
coefficient is bounded by `2`.
-/
theorem bdf1Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsBDF1TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
      ≤ (1 + h * (2 * L))
            * ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + 2 * ‖bdf1VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  have h_step : ‖yseq (n + 1) - y (t₀ + (n + 1) * h)‖ ≤ (1 / (1 - h * L)) * ‖yseq n - y (t₀ + n * h)‖ + (1 / (1 - h * L)) * ‖bdf1VecResidual h (t₀ + n * h) y‖ := by
    have := bdf1Vec_one_step_lipschitz hh hsmall hf t₀ hy y hyf n;
    rw [ ← mul_add, div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith;
  refine' le_trans h_step ( add_le_add _ _ );
  · exact mul_le_mul_of_nonneg_right ( by rw [ div_le_iff₀ ] <;> nlinarith [ mul_nonneg hh hL ] ) ( norm_nonneg _ );
  · exact mul_le_mul_of_nonneg_right ( by rw [ div_le_iff₀ ] <;> linarith ) ( norm_nonneg _ )

/-- A vector-valued `C^3` function has its second derivative bounded on
every compact interval `[a, b]`.  Local port of the private forward-Euler
helper from `LMMTruncationOp`. -/
private theorem iteratedDeriv_two_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 2 y t‖ ≤ M := by
  sorry

/-- First-order Taylor bound for the derivative:
`‖y'(t+h) - y'(t)‖ ≤ M·h`, assuming `‖y''‖ ≤ M` on a compact interval
containing the segment. -/
private theorem derivY_first_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 2 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b) (hth : t + h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖deriv y (t + h) - deriv y t‖ ≤ M * h := by
  sorry

/-- Second-order vector Taylor remainder for the value:
`‖y(t+h) - y(t) - h • y'(t)‖ ≤ M/2 · h²`. -/
private theorem y_second_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 2 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b) (hth : t + h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + h) - y t - h • deriv y t‖ ≤ M / 2 * h ^ 2 := by
  sorry

/-- Pointwise BDF1 vector truncation residual bound:
`‖y(t+h) − y(t) − h • y'(t+h)‖ ≤ 2·M·h²`. -/
private theorem bdf1Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 2 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b) (hth : t + h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + h) - y t - h • deriv y (t + h)‖ ≤ 2 * M * h ^ 2 := by
  sorry

/-- Uniform bound on the BDF1 vector one-step truncation residual on a
finite horizon, given a `C^3` exact solution. -/
theorem bdf1Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 1) * h ≤ T →
        ‖bdf1VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 2 := by
  sorry

/-- Headline BDF1 vector global error bound.  Given a supplied BDF1 vector
trajectory and starting error bounded by `ε₀`, the global error is
`O(ε₀ + h)` on a finite horizon. -/
theorem bdf1Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 3 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsBDF1TrajectoryVec h f t₀ yseq →
      0 ≤ ε₀ →
      ‖yseq 0 - y t₀‖ ≤ ε₀ →
      ∀ N : ℕ, (N : ℝ) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((2 * L) * T) * ε₀ + K * h := by
  sorry

end LMM