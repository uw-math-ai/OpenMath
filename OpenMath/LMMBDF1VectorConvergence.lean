import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.LMMTruncationOp

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
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set τ : E := bdf1VecResidual h tn y with hτ_def
  have _hsmall_record : h * L ≤ 1 / 2 := hsmall
  -- BDF1 step formula for the supplied implicit trajectory.
  have hstep : yn1 = yn + h • f tn1 yn1 := by
    simpa [hyn1_def, hyn_def, htn1_def] using hy.recurrence n
  -- Local residual at `tn`, expressed via `f` along the exact trajectory.
  have htn1_h : tn + h = tn1 := by
    simp [htn_def, htn1_def]
    ring
  have hτ_eq : τ = zn1 - zn - h • f tn1 zn1 := by
    show bdf1VecResidual h tn y = _
    unfold bdf1VecResidual
    rw [htn1_h, hyf tn1]
  -- Algebraic decomposition of the implicit global-error increment.
  have halg : yn1 - zn1
      = (yn - zn) + h • (f tn1 yn1 - f tn1 zn1) - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub]
    abel
  -- Lipschitz bound on the `f` increment.
  have hLip : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ :=
    hf tn1 yn1 zn1
  have hh_norm : ‖(h : ℝ)‖ = h := Real.norm_of_nonneg hh
  have hh_norm_term :
      ‖h • (f tn1 yn1 - f tn1 zn1)‖
        ≤ h * L * ‖yn1 - zn1‖ := by
    rw [norm_smul, hh_norm]
    calc h * ‖f tn1 yn1 - f tn1 zn1‖
        ≤ h * (L * ‖yn1 - zn1‖) :=
          mul_le_mul_of_nonneg_left hLip hh
      _ = h * L * ‖yn1 - zn1‖ := by ring
  -- Triangle inequality.
  have htri :
      ‖(yn - zn) + h • (f tn1 yn1 - f tn1 zn1) - τ‖
        ≤ ‖yn - zn‖
          + ‖h • (f tn1 yn1 - f tn1 zn1)‖
          + ‖τ‖ := by
    have h1 :
        ‖(yn - zn) + h • (f tn1 yn1 - f tn1 zn1) - τ‖
          ≤ ‖(yn - zn) + h • (f tn1 yn1 - f tn1 zn1)‖ + ‖τ‖ :=
      norm_sub_le _ _
    have h2 :
        ‖(yn - zn) + h • (f tn1 yn1 - f tn1 zn1)‖
          ≤ ‖yn - zn‖ + ‖h • (f tn1 yn1 - f tn1 zn1)‖ :=
      norm_add_le _ _
    linarith
  have hmain :
      ‖yn1 - zn1‖
        ≤ ‖yn - zn‖ + h * L * ‖yn1 - zn1‖ + ‖τ‖ := by
    calc ‖yn1 - zn1‖
        = ‖(yn - zn) + h • (f tn1 yn1 - f tn1 zn1) - τ‖ := by rw [halg]
      _ ≤ ‖yn - zn‖
          + ‖h • (f tn1 yn1 - f tn1 zn1)‖
          + ‖τ‖ := htri
      _ ≤ ‖yn - zn‖ + h * L * ‖yn1 - zn1‖ + ‖τ‖ := by
          linarith [hh_norm_term]
  linarith [hmain]

/-- Divided one-step BDF1 vector error bound.  The effective Lipschitz
constant is slackened to `2L`; under `h·L ≤ 1/2`, the local residual
coefficient is bounded by `2`. -/
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
  set en : ℝ := ‖yseq n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set τabs : ℝ :=
    ‖bdf1VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hA_pos : 0 < 1 - h * L := by linarith
  have hstep :
      (1 - h * L) * en1
        ≤ en + τabs := by
    simpa [hen_def, hen1_def, hτabs_def] using
      (bdf1Vec_one_step_lipschitz (E := E) (h := h) (L := L)
        hh hsmall hf t₀ hy y hyf n)
  have hcoeff_en :
      (1 : ℝ) ≤ (1 - h * L) * (1 + h * (2 * L)) := by
    nlinarith [hx_nn, hsmall]
  have hcoeff_τ :
      (1 : ℝ) ≤ (1 - h * L) * 2 := by
    nlinarith [hsmall]
  have h_en_part :
      en ≤ (1 - h * L) * ((1 + h * (2 * L)) * en) := by
    have := mul_le_mul_of_nonneg_right hcoeff_en hen_nn
    have halg : (1 - h * L) * ((1 + h * (2 * L)) * en)
        = (1 - h * L) * (1 + h * (2 * L)) * en := by ring
    linarith [halg.symm.le, halg.le]
  have h_τ_part :
      τabs ≤ (1 - h * L) * (2 * τabs) := by
    have := mul_le_mul_of_nonneg_right hcoeff_τ hτ_nn
    have halg : (1 - h * L) * (2 * τabs)
        = (1 - h * L) * 2 * τabs := by ring
    linarith [halg.symm.le, halg.le]
  have hRHS :
      en + τabs
        ≤ (1 - h * L) * ((1 + h * (2 * L)) * en + 2 * τabs) := by
    have hsplit :
        (1 - h * L) * ((1 + h * (2 * L)) * en + 2 * τabs)
          = (1 - h * L) * ((1 + h * (2 * L)) * en)
              + (1 - h * L) * (2 * τabs) := by ring
    rw [hsplit]
    linarith [h_en_part, h_τ_part]
  have hprod :
      (1 - h * L) * en1
        ≤ (1 - h * L) * ((1 + h * (2 * L)) * en + 2 * τabs) :=
    le_trans hstep hRHS
  exact le_of_mul_le_mul_left hprod hA_pos

/-- A vector-valued `C^3` function has its second derivative bounded on
every compact interval `[a, b]`.  Local port of the private forward-Euler
helper from `LMMTruncationOp`. -/
private theorem iteratedDeriv_two_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 2 y t‖ ≤ M := by
  have h_cont : Continuous (iteratedDeriv 2 y) :=
    hy.continuous_iteratedDeriv 2 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

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
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hdiff_deriv : Differentiable ℝ (deriv y) := by
    exact (hy.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).differentiable_deriv_two
  have hderiv_on :
      ∀ x ∈ Set.Icc t (t + h),
        HasDerivWithinAt (deriv y) (iteratedDeriv 2 y x)
          (Set.Icc t (t + h)) x := by
    intro x _
    have hxderiv : HasDerivAt (deriv y) (iteratedDeriv 2 y x) x := by
      convert (hdiff_deriv x).hasDerivAt using 1
      norm_num [iteratedDeriv_succ']
    exact hxderiv.hasDerivWithinAt
  have hbound_seg :
      ∀ x ∈ Set.Ico t (t + h), ‖iteratedDeriv 2 y x‖ ≤ M := by
    intro x hx
    have hx_ab : x ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hx.1]
      · linarith [hth.2, hx.2]
    exact hbnd x hx_ab
  have hth_le : t ≤ t + h := by linarith
  have hseg :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (f := deriv y) (f' := fun x => iteratedDeriv 2 y x)
      (a := t) (b := t + h) hderiv_on hbound_seg (t + h)
      (Set.right_mem_Icc.mpr hth_le)
  simpa using hseg

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
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hth_le : t ≤ t + h := by linarith
  have h_deriv_bound :
      ∀ s ∈ Set.Icc t (t + h), ‖deriv y s - deriv y t‖ ≤ M * (s - t) := by
    intro s hs
    have hts : t ≤ s := hs.1
    have hdiff_deriv : Differentiable ℝ (deriv y) := by
      exact (hy.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).differentiable_deriv_two
    have hderiv_on :
        ∀ x ∈ Set.Icc t s,
          HasDerivWithinAt (deriv y) (iteratedDeriv 2 y x) (Set.Icc t s) x := by
      intro x hx
      have hxderiv : HasDerivAt (deriv y) (iteratedDeriv 2 y x) x := by
        convert (hdiff_deriv x).hasDerivAt using 1
        norm_num [iteratedDeriv_succ']
      exact hxderiv.hasDerivWithinAt
    have hbound_seg : ∀ x ∈ Set.Ico t s, ‖iteratedDeriv 2 y x‖ ≤ M := by
      intro x hx
      have hx_ab : x ∈ Set.Icc a b := by
        refine ⟨?_, ?_⟩
        · linarith [ht.1, hx.1]
        · linarith [hth.2, hs.2, hx.2]
      exact hbnd x hx_ab
    have hseg :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        (f := deriv y) (f' := fun x => iteratedDeriv 2 y x)
        (a := t) (b := s) hderiv_on hbound_seg s
        (Set.right_mem_Icc.mpr hts)
    simpa using hseg
  have hderiv_cont : Continuous (deriv y) :=
    hy.continuous_deriv (by norm_num)
  have h_deriv_int : IntervalIntegrable (fun s => deriv y s) MeasureTheory.volume t (t + h) :=
    hderiv_cont.intervalIntegrable _ _
  have h_const_int : IntervalIntegrable (fun _ : ℝ => deriv y t) MeasureTheory.volume t (t + h) :=
    intervalIntegrable_const
  have h_ftc_y :
      ∫ s in t..t + h, deriv y s = y (t + h) - y t := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hy.contDiffAt.differentiableAt (by norm_num))
      h_deriv_int
  have h_residual_integral :
      y (t + h) - y t - h • deriv y t
        = ∫ s in t..t + h, (deriv y s - deriv y t) := by
    rw [intervalIntegral.integral_sub h_deriv_int h_const_int, h_ftc_y]
    simp
  have h_bound_integral :
      ‖∫ s in t..t + h, (deriv y s - deriv y t)‖
        ≤ ∫ s in t..t + h, M * (s - t) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hth_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs => h_deriv_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop : Continuous fun s : ℝ => M * (s - t)).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + h, M * (s - t) = M / 2 * h ^ 2 := by
    calc
      ∫ s in t..t + h, M * (s - t)
          = M * (∫ s in t..t + h, (s - t)) := by
            rw [intervalIntegral.integral_const_mul]
      _ = M / 2 * h ^ 2 := by
        simp [intervalIntegral.integral_sub, integral_id,
          intervalIntegral.integral_const]
        ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

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
  have hRFE :
      ‖y (t + h) - y t - h • deriv y t‖ ≤ M / 2 * h ^ 2 :=
    y_second_order_taylor_remainder_vec hy hbnd ht hth hh
  have hdy :
      ‖deriv y (t + h) - deriv y t‖ ≤ M * h :=
    derivY_first_order_taylor_remainder_vec hy hbnd ht hth hh
  have h_res_split :
      y (t + h) - y t - h • deriv y (t + h)
        = (y (t + h) - y t - h • deriv y t)
          - h • (deriv y (t + h) - deriv y t) := by
    simp only [smul_sub]
    abel
  have h_h_term :
      ‖h • (deriv y (t + h) - deriv y t)‖
        ≤ h * (M * h) := by
    rw [norm_smul, Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hdy hh
  have h_split_abs :
      ‖y (t + h) - y t - h • deriv y (t + h)‖
        ≤ ‖y (t + h) - y t - h • deriv y t‖
          + ‖h • (deriv y (t + h) - deriv y t)‖ := by
    rw [h_res_split]
    exact norm_sub_le _ _
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  have hh2_nn : 0 ≤ h ^ 2 := by positivity
  have hslack :
      M / 2 * h ^ 2 + h * (M * h) ≤ 2 * M * h ^ 2 := by
    nlinarith [hMnn, hh2_nn]
  linarith [h_split_abs, hRFE, h_h_term, hslack]

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
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_two_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨2 * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 1) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h = ((n : ℝ) + 1) * h := by ring
    linarith
  show ‖bdf1VecResidual h t y‖ ≤ 2 * M * h ^ 2
  unfold bdf1VecResidual
  exact bdf1Vec_pointwise_residual_bound hy hM ht_mem hth_mem hh.le

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
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    bdf1Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((2 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => ‖yseq k - y (t₀ + (k : ℝ) * h)‖ with heN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => norm_nonneg _
  have heN0_le : eN 0 ≤ ε₀ := by
    show ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀
    simpa using he0_bd
  have h2L_nn : (0 : ℝ) ≤ 2 * L := by linarith
  have hstep : ∀ n, n < N →
      eN (n + 1) ≤ (1 + h * (2 * L)) * eN n + (2 * C) * h ^ (1 + 1) := by
    intro n hn_lt
    have honestep := bdf1Vec_one_step_error_bound
      (E := E) (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hn1_le_N : (n : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
    have hres_cond : ((n : ℝ) + 1) * h ≤ T := by
      have hmul : ((n : ℝ) + 1) * h ≤ (N : ℝ) * h :=
        mul_le_mul_of_nonneg_right hn1_le_N hh.le
      linarith
    have hres := hresidual hh hδ_le n hres_cond
    have h2τ : 2 * ‖bdf1VecResidual h (t₀ + (n : ℝ) * h) y‖
        ≤ (2 * C) * h ^ 2 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have heq_eN_n : eN n
        = ‖yseq n - y (t₀ + (n : ℝ) * h)‖ := rfl
    have heq_eN_n1 : eN (n + 1)
        = ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast]
    have hpow : (2 * C) * h ^ (1 + 1) = (2 * C) * h ^ 2 := by norm_num
    rw [hpow, heq_eN_n, heq_eN_n1]
    linarith [honestep, h2τ]
  have hgronwall :=
    lmm_error_bound_from_local_truncation
      (h := h) (L := 2 * L) (C := 2 * C) (T := T) (p := 1) (e := eN) (N := N)
      hh.le h2L_nn (by linarith) (heN_nn 0) hstep N le_rfl hNh
  have hexp_nn : 0 ≤ Real.exp ((2 * L) * T) := Real.exp_nonneg _
  have h_chain :
      Real.exp ((2 * L) * T) * eN 0 ≤ Real.exp ((2 * L) * T) * ε₀ :=
    mul_le_mul_of_nonneg_left heN0_le hexp_nn
  show ‖yseq N - y (t₀ + (N : ℝ) * h)‖
      ≤ Real.exp ((2 * L) * T) * ε₀
          + T * Real.exp ((2 * L) * T) * (2 * C) * h
  have heN_eq : eN N = ‖yseq N - y (t₀ + (N : ℝ) * h)‖ := rfl
  have hpow1 : h ^ 1 = h := pow_one h
  rw [hpow1] at hgronwall
  linarith [hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
