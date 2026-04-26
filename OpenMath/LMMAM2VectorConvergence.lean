import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB3Convergence

/-! ## Adams--Moulton 2-step Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the AM2 scalar quantitative convergence chain in
`OpenMath/LMMAM2Convergence.lean`. The implicit AM2 update is parameterised
by a supplied trajectory; existence of such a trajectory is a separate
fixed-point problem and is not part of this chain.

The chain mirrors the AB2/AB3 vector templates:
* rewrite the local truncation residual in textbook form,
* prove a max-norm Lipschitz one-step recurrence,
* divide out the implicit `(1 − (5/12)·h·L)` factor,
* bound the local residual via the fourth-order vector Taylor remainder
  helpers from `LMMAB3Convergence`,
* assemble the global error via `lmm_error_bound_from_local_truncation`.
-/

namespace LMM

/-- AM2 vector trajectory predicate:
`y_{n+2} = y_{n+1} + h • ((5/12) • f_{n+2} + (8/12) • f_{n+1} − (1/12) • f_n)`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM2TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 2)
      = y (n + 1)
        + h • ((5 / 12 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             + (8 / 12 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             - (1 / 12 : ℝ) • f (t₀ + (n : ℝ) * h) (y n))

/-- Textbook AM2 vector residual: the value of the local truncation error of
the AM2 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def am2VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 2 * h) - y (t + h)
    - h • ((5 / 12 : ℝ) • deriv y (t + 2 * h)
          + (8 / 12 : ℝ) • deriv y (t + h)
          - (1 / 12 : ℝ) • deriv y t)

/-- The vector AM2 residual unfolds to the textbook form. -/
theorem am2Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am2VecResidual h t y
      = y (t + 2 * h) - y (t + h)
          - h • ((5 / 12 : ℝ) • deriv y (t + 2 * h)
                + (8 / 12 : ℝ) • deriv y (t + h)
                - (1 / 12 : ℝ) • deriv y t) := rfl

/-- One-step AM2 Lipschitz inequality before dividing by the implicit
new-point factor.  The side condition records the small-step regime used by
the divided form. -/
theorem am2Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (5 / 12 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM2TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (5 / 12 : ℝ) * h * L)
        * ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
      ≤ ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (8 / 12 : ℝ) * h * L
            * ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (1 / 12 : ℝ) * h * L
            * ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + ‖am2VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set yn2 : E := yseq (n + 2) with hyn2_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set τ : E := am2VecResidual h tn y with hτ_def
  have _hsmall_record : (5 / 12 : ℝ) * h * L ≤ 1 / 2 := hsmall
  -- AM2 step formula for the supplied implicit trajectory.
  have hstep : yn2
      = yn1
        + h • ((5 / 12 : ℝ) • f tn2 yn2
             + (8 / 12 : ℝ) • f tn1 yn1
             - (1 / 12 : ℝ) • f tn yn) := by
    simpa [hyn2_def, hyn1_def, hyn_def, htn2_def, htn1_def, htn_def]
      using hy.recurrence n
  -- Local truncation residual at `tn`, expressed via `f` along the trajectory.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have hτ_eq : τ = zn2 - zn1
      - h • ((5 / 12 : ℝ) • f tn2 zn2
             + (8 / 12 : ℝ) • f tn1 zn1
             - (1 / 12 : ℝ) • f tn zn) := by
    show am2VecResidual h tn y = _
    unfold am2VecResidual
    rw [htn1_h, htn_2h, hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the implicit global-error increment.
  have halg : yn2 - zn2
      = (yn1 - zn1)
        + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        + h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        - h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_add]
    abel
  -- Lipschitz bounds.
  have hLip2 : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ := hf tn2 yn2 zn2
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ := hf tn1 yn1 zn1
  have hLip0 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ := hf tn yn zn
  have h5_nn : (0 : ℝ) ≤ 5 / 12 := by norm_num
  have h8_nn : (0 : ℝ) ≤ 8 / 12 := by norm_num
  have h1_nn : (0 : ℝ) ≤ 1 / 12 := by norm_num
  -- Norm of each smul term.
  have h5_norm :
      ‖h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
        ≤ (5 / 12 : ℝ) * h * L * ‖yn2 - zn2‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h5_nn]
    have : h * ((5 / 12 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((5 / 12 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 h5_nn
    nlinarith [this]
  have h8_norm :
      ‖h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
        ≤ (8 / 12 : ℝ) * h * L * ‖yn1 - zn1‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h8_nn]
    have : h * ((8 / 12 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((8 / 12 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 h8_nn
    nlinarith [this]
  have h1_norm :
      ‖h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))‖
        ≤ (1 / 12 : ℝ) * h * L * ‖yn - zn‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h1_nn]
    have : h * ((1 / 12 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((1 / 12 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 h1_nn
    nlinarith [this]
  -- Triangle inequality (5 terms).
  have htri :
      ‖(yn1 - zn1)
        + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        + h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        - h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))
        - τ‖
        ≤ ‖yn1 - zn1‖
          + ‖h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
          + ‖h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
          + ‖h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))‖
          + ‖τ‖ := by
    have h1 :
        ‖(yn1 - zn1)
          + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))
          + h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))
          - h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))
          - τ‖
          ≤ ‖(yn1 - zn1)
              + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))
              + h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))
              - h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))‖
            + ‖τ‖ := norm_sub_le _ _
    have h2 :
        ‖(yn1 - zn1)
          + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))
          + h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))
          - h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))‖
          ≤ ‖(yn1 - zn1)
              + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))
              + h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
            + ‖h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))‖ := norm_sub_le _ _
    have h3 :
        ‖(yn1 - zn1)
          + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))
          + h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
          ≤ ‖(yn1 - zn1) + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
              + ‖h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖ :=
      norm_add_le _ _
    have h4 :
        ‖(yn1 - zn1) + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
          ≤ ‖yn1 - zn1‖
              + ‖h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖ :=
      norm_add_le _ _
    linarith
  have hmain :
      ‖yn2 - zn2‖
        ≤ ‖yn1 - zn1‖
          + (5 / 12 : ℝ) * h * L * ‖yn2 - zn2‖
          + (8 / 12 : ℝ) * h * L * ‖yn1 - zn1‖
          + (1 / 12 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    calc ‖yn2 - zn2‖
        = ‖(yn1 - zn1)
            + h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))
            + h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))
            - h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))
            - τ‖ := by rw [halg]
      _ ≤ ‖yn1 - zn1‖
          + ‖h • ((5 / 12 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
          + ‖h • ((8 / 12 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
          + ‖h • ((1 / 12 : ℝ) • (f tn yn - f tn zn))‖
          + ‖τ‖ := htri
      _ ≤ ‖yn1 - zn1‖
          + (5 / 12 : ℝ) * h * L * ‖yn2 - zn2‖
          + (8 / 12 : ℝ) * h * L * ‖yn1 - zn1‖
          + (1 / 12 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by linarith [h5_norm, h8_norm, h1_norm]
  linarith [hmain]

/-- Divided one-step AM2 error bound.  The effective Lipschitz constant is
slackened to `3L`; under `(5/12)·h·L ≤ 1/2`, the local residual coefficient
is bounded by `2`. -/
theorem am2Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (5 / 12 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM2TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
      ≤ (1 + h * (3 * L))
            * max ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                  ‖yseq (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)‖
        + 2 * ‖am2VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖yseq n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set τabs : ℝ :=
    ‖am2VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set EE : ℝ := max en en1 with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ EE := le_trans hen_nn (le_max_left _ _)
  have hen_le_E : en ≤ EE := le_max_left _ _
  have hen1_le_E : en1 ≤ EE := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 6 / 5 := by nlinarith [hsmall]
  have hA_pos : 0 < 1 - (5 / 12 : ℝ) * h * L := by nlinarith [hsmall]
  have hstep :
      (1 - (5 / 12 : ℝ) * h * L) * en2
        ≤ en1
          + (8 / 12 : ℝ) * h * L * en1
          + (1 / 12 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hτabs_def] using
      (am2Vec_one_step_lipschitz (E := E) (h := h) (L := L)
        hh hsmall hf t₀ hy y hyf n)
  have h8_nn : 0 ≤ (8 / 12 : ℝ) * h * L := by positivity
  have h1_nn : 0 ≤ (1 / 12 : ℝ) * h * L := by positivity
  have h8_le :
      (8 / 12 : ℝ) * h * L * en1
        ≤ (8 / 12 : ℝ) * h * L * EE :=
    mul_le_mul_of_nonneg_left hen1_le_E h8_nn
  have h1_le :
      (1 / 12 : ℝ) * h * L * en
        ≤ (1 / 12 : ℝ) * h * L * EE :=
    mul_le_mul_of_nonneg_left hen_le_E h1_nn
  have hR_le :
      en1
          + (8 / 12 : ℝ) * h * L * en1
          + (1 / 12 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (3 / 4 : ℝ) * (h * L)) * EE + τabs := by
    have h_alg :
        EE + (8 / 12 : ℝ) * h * L * EE
            + (1 / 12 : ℝ) * h * L * EE + τabs
          = (1 + (3 / 4 : ℝ) * (h * L)) * EE + τabs := by ring
    linarith
  have hcoeffE_le :
      1 + (3 / 4 : ℝ) * (h * L)
        ≤ (1 - (5 / 12 : ℝ) * h * L) * (1 + h * (3 * L)) := by
    nlinarith [hx_nn, hx_small]
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (5 / 12 : ℝ) * h * L) * 2 := by
    nlinarith [hsmall]
  have hE_part :
      (1 + (3 / 4 : ℝ) * (h * L)) * EE
        ≤ ((1 - (5 / 12 : ℝ) * h * L) * (1 + h * (3 * L))) * EE :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (5 / 12 : ℝ) * h * L) * 2) * τabs := by
    simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (3 / 4 : ℝ) * (h * L)) * EE + τabs
        ≤ (1 - (5 / 12 : ℝ) * h * L)
            * ((1 + h * (3 * L)) * EE + 2 * τabs) := by
    have hsplit :
        (1 - (5 / 12 : ℝ) * h * L)
            * ((1 + h * (3 * L)) * EE + 2 * τabs)
          = ((1 - (5 / 12 : ℝ) * h * L) * (1 + h * (3 * L))) * EE
              + ((1 - (5 / 12 : ℝ) * h * L) * 2) * τabs := by ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (5 / 12 : ℝ) * h * L) * en2
        ≤ (1 - (5 / 12 : ℝ) * h * L)
            * ((1 + h * (3 * L)) * EE + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  exact le_of_mul_le_mul_left hprod hA_pos

/-- Max-norm AM2 vector one-step recurrence on the rolling pair `(en, en1)`. -/
theorem am2Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (5 / 12 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM2TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
      ≤ (1 + h * (3 * L))
            * max ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                  ‖yseq (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)‖
        + 2 * ‖am2VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖yseq n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set τabs : ℝ :=
    ‖am2VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set EE : ℝ := max en en1 with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ EE := le_trans hen_nn (le_max_left _ _)
  have hen1_le_E : en1 ≤ EE := le_max_right _ _
  have h3hL_nn : 0 ≤ h * (3 * L) := by positivity
  have hen2_bd :
      en2 ≤ (1 + h * (3 * L)) * EE + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hτabs_def, hE_def] using
      (am2Vec_one_step_error_bound (E := E) (h := h) (L := L)
        hh hL hsmall hf t₀ hy y hyf n)
  have hen1_bd : en1 ≤ (1 + h * (3 * L)) * EE + 2 * τabs := by
    have hone_le : EE ≤ (1 + h * (3 * L)) * EE := by
      have : (1 : ℝ) * EE ≤ (1 + h * (3 * L)) * EE :=
        mul_le_mul_of_nonneg_right (by linarith) hE_nn
      linarith
    linarith [hen1_le_E]
  exact max_le hen1_bd hen2_bd

/-- Pointwise vector AM2 truncation residual bound.  Algebraic identity
`R = R_y(2) − R_y(1) − (5h/12)•R_y'(2) − (8h/12)•R_y'(1)`, then bound each
term by the fourth-order Taylor remainder.  We slack the residual to
`2·M·h⁴`. -/
theorem am2Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 4 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 2 * h) - y (t + h)
        - h • ((5 / 12 : ℝ) • deriv y (t + 2 * h)
              + (8 / 12 : ℝ) • deriv y (t + h)
              - (1 / 12 : ℝ) • deriv y t)‖
      ≤ (2 : ℝ) * M * h ^ 4 := by
  have h2h : 0 ≤ 2 * h := by linarith
  -- R_y(1): ‖y(t+h) - y(t) - h•y'(t) - h²/2•y''(t) - h³/6•y'''(t)‖ ≤ M/24·h⁴.
  have hRy1 :=
    y_fourth_order_taylor_remainder_vec hy hbnd ht hth hh
  -- R_y(2): ‖y(t+2h) - y(t) - 2h•y'(t) - 2h²•y''(t) - (4h³/3)•y'''(t)‖ ≤ M/24·(2h)⁴.
  have hRy2 :=
    y_fourth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  -- R_y'(1): ‖y'(t+h) - y'(t) - h•y''(t) - (h²/2)•y'''(t)‖ ≤ M/6·h³.
  have hRyp1 :=
    derivY_third_order_taylor_remainder_vec hy hbnd ht hth hh
  -- R_y'(2): ‖y'(t+2h) - y'(t) - 2h•y''(t) - 2h²•y'''(t)‖ ≤ M/6·(2h)³.
  have hRyp2 :=
    derivY_third_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  set y0 : E := y t with hy0_def
  set y1 : E := y (t + h) with hy1_def
  set y2 : E := y (t + 2 * h) with hy2_def
  set d0 : E := deriv y t with hd0_def
  set d1 : E := deriv y (t + h) with hd1_def
  set d2 : E := deriv y (t + 2 * h) with hd2_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  -- Algebraic identity decomposing the LTE as a signed sum of remainders.
  have hLTE_eq :
      y2 - y1 - h • ((5 / 12 : ℝ) • d2 + (8 / 12 : ℝ) • d1 - (1 / 12 : ℝ) • d0)
        = (y2 - y0 - (2 * h) • d0
              - ((2 * h) ^ 2 / 2) • dd - ((2 * h) ^ 3 / 6) • ddd)
          - (y1 - y0 - h • d0 - (h ^ 2 / 2) • dd - (h ^ 3 / 6) • ddd)
          - (5 * h / 12 : ℝ)
              • (d2 - d0 - (2 * h) • dd - ((2 * h) ^ 2 / 2) • ddd)
          - (8 * h / 12 : ℝ)
              • (d1 - d0 - h • dd - (h ^ 2 / 2) • ddd) := by
    simp only [smul_sub, smul_add, smul_smul]
    module
  rw [hLTE_eq]
  set A : E := y2 - y0 - (2 * h) • d0
            - ((2 * h) ^ 2 / 2) • dd - ((2 * h) ^ 3 / 6) • ddd with hA_def
  set B : E := y1 - y0 - h • d0 - (h ^ 2 / 2) • dd - (h ^ 3 / 6) • ddd
    with hB_def
  set C : E := d2 - d0 - (2 * h) • dd - ((2 * h) ^ 2 / 2) • ddd with hC_def
  set D : E := d1 - d0 - h • dd - (h ^ 2 / 2) • ddd with hD_def
  have h5h_nn : 0 ≤ (5 * h / 12 : ℝ) := by linarith
  have h8h_nn : 0 ≤ (8 * h / 12 : ℝ) := by linarith
  have htri :
      ‖A - B - (5 * h / 12 : ℝ) • C - (8 * h / 12 : ℝ) • D‖
        ≤ ‖A‖ + ‖B‖
          + ‖(5 * h / 12 : ℝ) • C‖
          + ‖(8 * h / 12 : ℝ) • D‖ := by
    have h1 :
        ‖A - B - (5 * h / 12 : ℝ) • C - (8 * h / 12 : ℝ) • D‖
          ≤ ‖A - B - (5 * h / 12 : ℝ) • C‖
              + ‖(8 * h / 12 : ℝ) • D‖ := norm_sub_le _ _
    have h2 :
        ‖A - B - (5 * h / 12 : ℝ) • C‖
          ≤ ‖A - B‖ + ‖(5 * h / 12 : ℝ) • C‖ := norm_sub_le _ _
    have h3 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
    linarith
  have hA_bd : ‖A‖ ≤ M / 24 * (2 * h) ^ 4 := hRy2
  have hB_bd : ‖B‖ ≤ M / 24 * h ^ 4 := hRy1
  have hC_bd : ‖C‖ ≤ M / 6 * (2 * h) ^ 3 := hRyp2
  have hD_bd : ‖D‖ ≤ M / 6 * h ^ 3 := hRyp1
  have h5C_bd :
      ‖(5 * h / 12 : ℝ) • C‖ ≤ (5 * h / 12 : ℝ) * (M / 6 * (2 * h) ^ 3) := by
    rw [norm_smul, Real.norm_of_nonneg h5h_nn]
    exact mul_le_mul_of_nonneg_left hC_bd h5h_nn
  have h8D_bd :
      ‖(8 * h / 12 : ℝ) • D‖ ≤ (8 * h / 12 : ℝ) * (M / 6 * h ^ 3) := by
    rw [norm_smul, Real.norm_of_nonneg h8h_nn]
    exact mul_le_mul_of_nonneg_left hD_bd h8h_nn
  -- Numeric bound: 16/24 + 1/24 + 40/72 + 8/72 = 17/24 + 48/72 = 33/24 = 11/8.
  have hbound_alg :
      M / 24 * (2 * h) ^ 4 + M / 24 * h ^ 4
        + (5 * h / 12) * (M / 6 * (2 * h) ^ 3)
        + (8 * h / 12) * (M / 6 * h ^ 3)
        = (11 / 8 : ℝ) * M * h ^ 4 := by ring
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  have hh4_nn : 0 ≤ h ^ 4 := by positivity
  have hslack : (11 / 8 : ℝ) * M * h ^ 4 ≤ 2 * M * h ^ 4 := by
    have : (11 / 8 : ℝ) ≤ 2 := by norm_num
    nlinarith [hMnn, hh4_nn]
  linarith [htri, hA_bd, hB_bd, h5C_bd, h8D_bd, hbound_alg.le,
    hbound_alg.ge, hslack]

/-- Uniform bound on the AM2 vector one-step truncation residual on a finite
horizon, given a `C^4` exact solution. -/
theorem am2Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 4 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 2) * h ≤ T →
        ‖am2VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 4 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_four_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(2 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 2) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 2) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h = ((n : ℝ) + 2) * h := by ring
    linarith
  show ‖am2VecResidual h t y‖ ≤ 2 * M * h ^ 4
  unfold am2VecResidual
  exact am2Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem hh.le

/-- Headline AM2 vector global error bound.  Given a supplied AM2 trajectory
and starting errors bounded by `ε₀`, the vector global error is `O(ε₀ + h^3)`
on a finite horizon. -/
theorem am2Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 4 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (5 / 12 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsAM2TrajectoryVec h f t₀ yseq →
      0 ≤ ε₀ →
      ‖yseq 0 - y t₀‖ ≤ ε₀ →
      ‖yseq 1 - y (t₀ + h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 1) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((3 * L) * T) * ε₀ + K * h ^ 3 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am2Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((3 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => ‖yseq k - y (t₀ + (k : ℝ) * h)‖ with heN_def
  set EN : ℕ → ℝ := fun k => max (eN k) (eN (k + 1)) with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => norm_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k => le_max_of_le_left (heN_nn k)
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (eN 0) (eN 1) ≤ ε₀
    refine max_le ?_ ?_
    · show ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀
      simpa using he0_bd
    · show ‖yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)‖ ≤ ε₀
      simpa using he1_bd
  have h3L_nn : (0 : ℝ) ≤ 3 * L := by linarith
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 2) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (3 * L)) * EN n + (2 * C) * h ^ 4 := by
    intro n hnh_le
    have honestep := am2Vec_one_step_error_pair_bound
      (E := E) (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
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
    show max (eN (n + 1)) (eN (n + 1 + 1))
        ≤ (1 + h * (3 * L)) * max (eN n) (eN (n + 1)) + (2 * C) * h ^ 4
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2]
    have h2τ : 2 * ‖am2VecResidual h (t₀ + (n : ℝ) * h) y‖
        ≤ (2 * C) * h ^ 4 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith [this]
    linarith [honestep, h2τ]
  rcases N with _ | N'
  · show ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖
        ≤ Real.exp ((3 * L) * T) * ε₀
            + T * Real.exp ((3 * L) * T) * (2 * C) * h ^ 3
    have hbase : ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖
        ≤ ε₀ := by simpa using he0_bd
    have hexp_ge : (1 : ℝ) ≤ Real.exp ((3 * L) * T) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hKnn : 0 ≤ T * Real.exp ((3 * L) * T) * (2 * C) :=
      mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
    have hh3_nn : 0 ≤ h ^ 3 := by positivity
    nlinarith [hbase, hexp_ge, hKnn, hh3_nn, hε₀]
  · have hN_hyp : ((N' : ℝ) + 1 + 1) * h ≤ T := by
      have hcast : (((N' + 1 : ℕ) : ℝ) + 1) = (N' : ℝ) + 1 + 1 := by
        push_cast; ring
      linarith [hcast.symm ▸ hNh]
    have hgronwall_step : ∀ n, n < N' →
        EN (n + 1) ≤ (1 + h * (3 * L)) * EN n + (2 * C) * h ^ (3 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (3 + 1) = (2 * C) * h ^ 4 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn1_le_N' : (n : ℝ) + 1 ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      have h_le_chain : (n : ℝ) + 2 ≤ (N' : ℝ) + 1 + 1 := by linarith
      have h_mul : ((n : ℝ) + 2) * h ≤ ((N' : ℝ) + 1 + 1) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'h_le_T : (N' : ℝ) * h ≤ T := by
      have hle : (N' : ℝ) ≤ (N' : ℝ) + 1 + 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 3 * L) (C := 2 * C) (T := T) (p := 3) (e := EN) (N := N')
        hh.le h3L_nn (by linarith) (hEN_nn 0) hgronwall_step N' le_rfl hN'h_le_T
    have heN_le_EN : eN (N' + 1) ≤ EN N' := le_max_right _ _
    have hexp_nn : 0 ≤ Real.exp ((3 * L) * T) := Real.exp_nonneg _
    have h_chain :
        Real.exp ((3 * L) * T) * EN 0 ≤ Real.exp ((3 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show ‖yseq (N' + 1) - y (t₀ + ((N' + 1 : ℕ) : ℝ) * h)‖
        ≤ Real.exp ((3 * L) * T) * ε₀
            + T * Real.exp ((3 * L) * T) * (2 * C) * h ^ 3
    have heN_eq :
        eN (N' + 1)
          = ‖yseq (N' + 1) - y (t₀ + ((N' + 1 : ℕ) : ℝ) * h)‖ := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
