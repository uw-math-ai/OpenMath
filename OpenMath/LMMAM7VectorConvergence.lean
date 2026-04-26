import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB6VectorConvergence

/-! ## Adams--Moulton 7-step Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the AM7 scalar quantitative convergence chain in
`OpenMath/LMMAM7Convergence.lean`. The implicit AM7 update is parameterised
by a supplied trajectory; existence of such a trajectory is a separate
fixed-point problem and is not part of this chain.
-/

namespace LMM

private theorem iteratedDeriv_nine_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 9 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 9 y t‖ ≤ M := by
  have h_cont : Continuous (iteratedDeriv 9 y) :=
    hy.continuous_iteratedDeriv 9 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

private theorem am7Vec_y_eighth_order_taylor_remainder_vec
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

private theorem y_ninth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 9 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 9 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖y (t + r) - y t - r • deriv y t
        - (r ^ 2 / 2) • iteratedDeriv 2 y t
        - (r ^ 3 / 6) • iteratedDeriv 3 y t
        - (r ^ 4 / 24) • iteratedDeriv 4 y t
        - (r ^ 5 / 120) • iteratedDeriv 5 y t
        - (r ^ 6 / 720) • iteratedDeriv 6 y t
        - (r ^ 7 / 5040) • iteratedDeriv 7 y t
        - (r ^ 8 / 40320) • iteratedDeriv 8 y t‖
      ≤ M / 362880 * r ^ 9 := by
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
            - ((s - t) ^ 7 / 5040) • iteratedDeriv 8 y t‖
          ≤ M / 40320 * (s - t) ^ 8 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have hdy : ContDiff ℝ 8 (deriv y) := hy.deriv'
    have hbnd_d :
        ∀ u ∈ Set.Icc a b, ‖iteratedDeriv 8 (deriv y) u‖ ≤ M := by
      intro u hu
      have hidd_eq : iteratedDeriv 8 (deriv y) = iteratedDeriv 9 y := by
        have : iteratedDeriv 9 y = iteratedDeriv 8 (deriv y) :=
          iteratedDeriv_succ' (n := 8) (f := y)
        exact this.symm
      simpa [hidd_eq] using hbnd u hu
    have hrem :=
      am7Vec_y_eighth_order_taylor_remainder_vec hdy hbnd_d ht
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
    rw [hsplit] at hrem
    simpa [hderiv2, hiter2, hiter3, hiter4, hiter5, hiter6, hiter7] using hrem
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
  have h_residual_integral :
      y (t + r) - y t - r • deriv y t
          - (r ^ 2 / 2) • iteratedDeriv 2 y t
          - (r ^ 3 / 6) • iteratedDeriv 3 y t
          - (r ^ 4 / 24) • iteratedDeriv 4 y t
          - (r ^ 5 / 120) • iteratedDeriv 5 y t
          - (r ^ 6 / 720) • iteratedDeriv 6 y t
          - (r ^ 7 / 5040) • iteratedDeriv 7 y t
          - (r ^ 8 / 40320) • iteratedDeriv 8 y t
        = ∫ s in t..t + r,
            (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
              - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
              - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
              - ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
              - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t
              - ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t
              - ((s - t) ^ 7 / 5040) • iteratedDeriv 8 y t) := by
    rw [intervalIntegral.integral_sub
        (((((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int).sub h_quintic_int).sub h_sextic_int)
          h_septic_int,
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
      h_quintic_eval, h_sextic_eval, h_septic_eval]
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
            - ((s - t) ^ 7 / 5040) • iteratedDeriv 8 y t)‖
        ≤ ∫ s in t..t + r, M / 40320 * (s - t) ^ 8 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dy_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 40320 * (s - t) ^ 8).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 40320 * (s - t) ^ 8 = M / 362880 * r ^ 9 := by
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
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

private theorem derivY_eighth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 9 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 9 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖deriv y (t + r) - deriv y t - r • iteratedDeriv 2 y t
        - (r ^ 2 / 2) • iteratedDeriv 3 y t
        - (r ^ 3 / 6) • iteratedDeriv 4 y t
        - (r ^ 4 / 24) • iteratedDeriv 5 y t
        - (r ^ 5 / 120) • iteratedDeriv 6 y t
        - (r ^ 6 / 720) • iteratedDeriv 7 y t
        - (r ^ 7 / 5040) • iteratedDeriv 8 y t‖
      ≤ M / 40320 * r ^ 8 := by
  have hdy : ContDiff ℝ 8 (deriv y) := hy.deriv'
  have hbnd_d :
      ∀ s ∈ Set.Icc a b, ‖iteratedDeriv 8 (deriv y) s‖ ≤ M := by
    intro s hs
    have hidd_eq : iteratedDeriv 8 (deriv y) = iteratedDeriv 9 y := by
      have : iteratedDeriv 9 y = iteratedDeriv 8 (deriv y) :=
        iteratedDeriv_succ' (n := 8) (f := y)
      exact this.symm
    simpa [hidd_eq] using hbnd s hs
  have hrem := am7Vec_y_eighth_order_taylor_remainder_vec hdy hbnd_d ht htr hr
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
  simpa [hderiv2, hiter2, hiter3, hiter4, hiter5, hiter6, hiter7] using hrem

/-- AM7 vector trajectory predicate. The new value appears inside `f`, so
existence of such a trajectory is a separate fixed-point problem. -/
structure IsAM7TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 7)
      = y (n + 6)
        + h • ((36799 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h) (y (n + 7))
             + (139849 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             - (121797 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             + (123133 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             - (88547 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             + (41499 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             - (11351 / 120960 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             + (1375 / 120960 : ℝ) • f (t₀ + (n : ℝ) * h) (y n))

/-- Textbook AM7 vector residual: the value of the local truncation error of
the AM7 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def am7VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 7 * h) - y (t + 6 * h)
    - h • ((36799 / 120960 : ℝ) • deriv y (t + 7 * h)
          + (139849 / 120960 : ℝ) • deriv y (t + 6 * h)
          - (121797 / 120960 : ℝ) • deriv y (t + 5 * h)
          + (123133 / 120960 : ℝ) • deriv y (t + 4 * h)
          - (88547 / 120960 : ℝ) • deriv y (t + 3 * h)
          + (41499 / 120960 : ℝ) • deriv y (t + 2 * h)
          - (11351 / 120960 : ℝ) • deriv y (t + h)
          + (1375 / 120960 : ℝ) • deriv y t)

theorem am7Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am7VecResidual h t y
      = y (t + 7 * h) - y (t + 6 * h)
          - h • ((36799 / 120960 : ℝ) • deriv y (t + 7 * h)
                + (139849 / 120960 : ℝ) • deriv y (t + 6 * h)
                - (121797 / 120960 : ℝ) • deriv y (t + 5 * h)
                + (123133 / 120960 : ℝ) • deriv y (t + 4 * h)
                - (88547 / 120960 : ℝ) • deriv y (t + 3 * h)
                + (41499 / 120960 : ℝ) • deriv y (t + 2 * h)
                - (11351 / 120960 : ℝ) • deriv y (t + h)
                + (1375 / 120960 : ℝ) • deriv y t) := by
  rfl

theorem am7Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (36799 / 120960 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM7TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (36799 / 120960 : ℝ) * h * L)
        * ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
      ≤ ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (139849 / 120960 : ℝ) * h * L
            * ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (121797 / 120960 : ℝ) * h * L
            * ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (123133 / 120960 : ℝ) * h * L
            * ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (88547 / 120960 : ℝ) * h * L
            * ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (41499 / 120960 : ℝ) * h * L
            * ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (11351 / 120960 : ℝ) * h * L
            * ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (1375 / 120960 : ℝ) * h * L
            * ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + ‖am7VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set yn2 : E := yseq (n + 2) with hyn2_def
  set yn3 : E := yseq (n + 3) with hyn3_def
  set yn4 : E := yseq (n + 4) with hyn4_def
  set yn5 : E := yseq (n + 5) with hyn5_def
  set yn6 : E := yseq (n + 6) with hyn6_def
  set yn7 : E := yseq (n + 7) with hyn7_def
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
  set τ : E := am7VecResidual h tn y with hτ_def
  have _hsmall_record : (36799 / 120960 : ℝ) * h * L ≤ 1 / 2 := hsmall
  have hstep : yn7
      = yn6
        + h • ((36799 / 120960 : ℝ) • f tn7 yn7
             + (139849 / 120960 : ℝ) • f tn6 yn6
             - (121797 / 120960 : ℝ) • f tn5 yn5
             + (123133 / 120960 : ℝ) • f tn4 yn4
             - (88547 / 120960 : ℝ) • f tn3 yn3
             + (41499 / 120960 : ℝ) • f tn2 yn2
             - (11351 / 120960 : ℝ) • f tn1 yn1
             + (1375 / 120960 : ℝ) • f tn yn) := by
    simpa [hyn7_def, hyn6_def, hyn5_def, hyn4_def, hyn3_def, hyn2_def, hyn1_def,
      hyn_def, htn7_def, htn6_def, htn5_def, htn4_def, htn3_def, htn2_def,
      htn1_def, htn_def] using hy.recurrence n
  have htn1_h : tn + h = tn1 := by
    simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by
    simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by
    simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by
    simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by
    simp [htn_def, htn5_def]; ring
  have htn_6h : tn + 6 * h = tn6 := by
    simp [htn_def, htn6_def]; ring
  have htn_7h : tn + 7 * h = tn7 := by
    simp [htn_def, htn7_def]; ring
  have hτ_eq : τ = zn7 - zn6
      - h • ((36799 / 120960 : ℝ) • f tn7 zn7
             + (139849 / 120960 : ℝ) • f tn6 zn6
             - (121797 / 120960 : ℝ) • f tn5 zn5
             + (123133 / 120960 : ℝ) • f tn4 zn4
             - (88547 / 120960 : ℝ) • f tn3 zn3
             + (41499 / 120960 : ℝ) • f tn2 zn2
             - (11351 / 120960 : ℝ) • f tn1 zn1
             + (1375 / 120960 : ℝ) • f tn zn) := by
    show am7VecResidual h tn y = _
    unfold am7VecResidual
    rw [htn1_h, htn_2h, htn_3h, htn_4h, htn_5h, htn_6h, htn_7h,
      hyf tn7, hyf tn6, hyf tn5, hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  have halg : yn7 - zn7
      = (yn6 - zn6)
        + h • ((36799 / 120960 : ℝ) • (f tn7 yn7 - f tn7 zn7))
        + h • ((139849 / 120960 : ℝ) • (f tn6 yn6 - f tn6 zn6))
        - h • ((121797 / 120960 : ℝ) • (f tn5 yn5 - f tn5 zn5))
        + h • ((123133 / 120960 : ℝ) • (f tn4 yn4 - f tn4 zn4))
        - h • ((88547 / 120960 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        + h • ((41499 / 120960 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        - h • ((11351 / 120960 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        + h • ((1375 / 120960 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_add]
    abel
  have hLip7 : ‖f tn7 yn7 - f tn7 zn7‖ ≤ L * ‖yn7 - zn7‖ :=
    hf tn7 yn7 zn7
  have hLip6 : ‖f tn6 yn6 - f tn6 zn6‖ ≤ L * ‖yn6 - zn6‖ :=
    hf tn6 yn6 zn6
  have hLip5 : ‖f tn5 yn5 - f tn5 zn5‖ ≤ L * ‖yn5 - zn5‖ :=
    hf tn5 yn5 zn5
  have hLip4 : ‖f tn4 yn4 - f tn4 zn4‖ ≤ L * ‖yn4 - zn4‖ :=
    hf tn4 yn4 zn4
  have hLip3 : ‖f tn3 yn3 - f tn3 zn3‖ ≤ L * ‖yn3 - zn3‖ :=
    hf tn3 yn3 zn3
  have hLip2 : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ :=
    hf tn2 yn2 zn2
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ :=
    hf tn1 yn1 zn1
  have hLip0 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ :=
    hf tn yn zn
  have h36799_nn : (0 : ℝ) ≤ 36799 / 120960 := by norm_num
  have h139849_nn : (0 : ℝ) ≤ 139849 / 120960 := by norm_num
  have h121797_nn : (0 : ℝ) ≤ 121797 / 120960 := by norm_num
  have h123133_nn : (0 : ℝ) ≤ 123133 / 120960 := by norm_num
  have h88547_nn : (0 : ℝ) ≤ 88547 / 120960 := by norm_num
  have h41499_nn : (0 : ℝ) ≤ 41499 / 120960 := by norm_num
  have h11351_nn : (0 : ℝ) ≤ 11351 / 120960 := by norm_num
  have h1375_nn : (0 : ℝ) ≤ 1375 / 120960 := by norm_num
  have h36799_norm :
      ‖h • ((36799 / 120960 : ℝ) • (f tn7 yn7 - f tn7 zn7))‖
        ≤ (36799 / 120960 : ℝ) * h * L * ‖yn7 - zn7‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh, norm_smul, Real.norm_of_nonneg h36799_nn]
    have : h * ((36799 / 120960 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((36799 / 120960 : ℝ) * (L * ‖yn7 - zn7‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip7 h36799_nn
    calc h * ((36799 / 120960 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((36799 / 120960 : ℝ) * (L * ‖yn7 - zn7‖)) := this
      _ = (36799 / 120960 : ℝ) * h * L * ‖yn7 - zn7‖ := by ring
  have h139849_norm :
      ‖h • ((139849 / 120960 : ℝ) • (f tn6 yn6 - f tn6 zn6))‖
        ≤ (139849 / 120960 : ℝ) * h * L * ‖yn6 - zn6‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh, norm_smul, Real.norm_of_nonneg h139849_nn]
    have : h * ((139849 / 120960 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((139849 / 120960 : ℝ) * (L * ‖yn6 - zn6‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip6 h139849_nn
    calc h * ((139849 / 120960 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((139849 / 120960 : ℝ) * (L * ‖yn6 - zn6‖)) := this
      _ = (139849 / 120960 : ℝ) * h * L * ‖yn6 - zn6‖ := by ring
  have h121797_norm :
      ‖h • ((121797 / 120960 : ℝ) • (f tn5 yn5 - f tn5 zn5))‖
        ≤ (121797 / 120960 : ℝ) * h * L * ‖yn5 - zn5‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh, norm_smul, Real.norm_of_nonneg h121797_nn]
    have : h * ((121797 / 120960 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((121797 / 120960 : ℝ) * (L * ‖yn5 - zn5‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip5 h121797_nn
    calc h * ((121797 / 120960 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((121797 / 120960 : ℝ) * (L * ‖yn5 - zn5‖)) := this
      _ = (121797 / 120960 : ℝ) * h * L * ‖yn5 - zn5‖ := by ring
  have h123133_norm :
      ‖h • ((123133 / 120960 : ℝ) • (f tn4 yn4 - f tn4 zn4))‖
        ≤ (123133 / 120960 : ℝ) * h * L * ‖yn4 - zn4‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh, norm_smul, Real.norm_of_nonneg h123133_nn]
    have : h * ((123133 / 120960 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((123133 / 120960 : ℝ) * (L * ‖yn4 - zn4‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip4 h123133_nn
    calc h * ((123133 / 120960 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((123133 / 120960 : ℝ) * (L * ‖yn4 - zn4‖)) := this
      _ = (123133 / 120960 : ℝ) * h * L * ‖yn4 - zn4‖ := by ring
  have h88547_norm :
      ‖h • ((88547 / 120960 : ℝ) • (f tn3 yn3 - f tn3 zn3))‖
        ≤ (88547 / 120960 : ℝ) * h * L * ‖yn3 - zn3‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh, norm_smul, Real.norm_of_nonneg h88547_nn]
    have : h * ((88547 / 120960 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((88547 / 120960 : ℝ) * (L * ‖yn3 - zn3‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip3 h88547_nn
    calc h * ((88547 / 120960 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((88547 / 120960 : ℝ) * (L * ‖yn3 - zn3‖)) := this
      _ = (88547 / 120960 : ℝ) * h * L * ‖yn3 - zn3‖ := by ring
  have h41499_norm :
      ‖h • ((41499 / 120960 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
        ≤ (41499 / 120960 : ℝ) * h * L * ‖yn2 - zn2‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh, norm_smul, Real.norm_of_nonneg h41499_nn]
    have : h * ((41499 / 120960 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((41499 / 120960 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 h41499_nn
    calc h * ((41499 / 120960 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((41499 / 120960 : ℝ) * (L * ‖yn2 - zn2‖)) := this
      _ = (41499 / 120960 : ℝ) * h * L * ‖yn2 - zn2‖ := by ring
  have h11351_norm :
      ‖h • ((11351 / 120960 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
        ≤ (11351 / 120960 : ℝ) * h * L * ‖yn1 - zn1‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh, norm_smul, Real.norm_of_nonneg h11351_nn]
    have : h * ((11351 / 120960 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((11351 / 120960 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 h11351_nn
    calc h * ((11351 / 120960 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((11351 / 120960 : ℝ) * (L * ‖yn1 - zn1‖)) := this
      _ = (11351 / 120960 : ℝ) * h * L * ‖yn1 - zn1‖ := by ring
  have h1375_norm :
      ‖h • ((1375 / 120960 : ℝ) • (f tn yn - f tn zn))‖
        ≤ (1375 / 120960 : ℝ) * h * L * ‖yn - zn‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh, norm_smul, Real.norm_of_nonneg h1375_nn]
    have : h * ((1375 / 120960 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((1375 / 120960 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 h1375_nn
    calc h * ((1375 / 120960 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((1375 / 120960 : ℝ) * (L * ‖yn - zn‖)) := this
      _ = (1375 / 120960 : ℝ) * h * L * ‖yn - zn‖ := by ring
  have htri_terms (A B C D F G J K R S : E) :
      ‖A + B + C - D + F - G + J - K + R - S‖
        ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖F‖ + ‖G‖ + ‖J‖ + ‖K‖ + ‖R‖ + ‖S‖ := by
    have h1 : ‖A + B + C - D + F - G + J - K + R - S‖
        ≤ ‖A + B + C - D + F - G + J - K + R‖ + ‖S‖ := norm_sub_le _ _
    have h2 : ‖A + B + C - D + F - G + J - K + R‖
        ≤ ‖A + B + C - D + F - G + J - K‖ + ‖R‖ := norm_add_le _ _
    have h3 : ‖A + B + C - D + F - G + J - K‖
        ≤ ‖A + B + C - D + F - G + J‖ + ‖K‖ := norm_sub_le _ _
    have h4 : ‖A + B + C - D + F - G + J‖
        ≤ ‖A + B + C - D + F - G‖ + ‖J‖ := norm_add_le _ _
    have h5 : ‖A + B + C - D + F - G‖
        ≤ ‖A + B + C - D + F‖ + ‖G‖ := norm_sub_le _ _
    have h6 : ‖A + B + C - D + F‖
        ≤ ‖A + B + C - D‖ + ‖F‖ := norm_add_le _ _
    have h7 : ‖A + B + C - D‖ ≤ ‖A + B + C‖ + ‖D‖ := norm_sub_le _ _
    have h8 : ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
    have h9 : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    linarith
  have htri :
      ‖(yn6 - zn6)
        + h • ((36799 / 120960 : ℝ) • (f tn7 yn7 - f tn7 zn7))
        + h • ((139849 / 120960 : ℝ) • (f tn6 yn6 - f tn6 zn6))
        - h • ((121797 / 120960 : ℝ) • (f tn5 yn5 - f tn5 zn5))
        + h • ((123133 / 120960 : ℝ) • (f tn4 yn4 - f tn4 zn4))
        - h • ((88547 / 120960 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        + h • ((41499 / 120960 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        - h • ((11351 / 120960 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        + h • ((1375 / 120960 : ℝ) • (f tn yn - f tn zn))
        - τ‖
        ≤ ‖yn6 - zn6‖
          + ‖h • ((36799 / 120960 : ℝ) • (f tn7 yn7 - f tn7 zn7))‖
          + ‖h • ((139849 / 120960 : ℝ) • (f tn6 yn6 - f tn6 zn6))‖
          + ‖h • ((121797 / 120960 : ℝ) • (f tn5 yn5 - f tn5 zn5))‖
          + ‖h • ((123133 / 120960 : ℝ) • (f tn4 yn4 - f tn4 zn4))‖
          + ‖h • ((88547 / 120960 : ℝ) • (f tn3 yn3 - f tn3 zn3))‖
          + ‖h • ((41499 / 120960 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
          + ‖h • ((11351 / 120960 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
          + ‖h • ((1375 / 120960 : ℝ) • (f tn yn - f tn zn))‖
          + ‖τ‖ :=
    htri_terms (yn6 - zn6)
      (h • ((36799 / 120960 : ℝ) • (f tn7 yn7 - f tn7 zn7)))
      (h • ((139849 / 120960 : ℝ) • (f tn6 yn6 - f tn6 zn6)))
      (h • ((121797 / 120960 : ℝ) • (f tn5 yn5 - f tn5 zn5)))
      (h • ((123133 / 120960 : ℝ) • (f tn4 yn4 - f tn4 zn4)))
      (h • ((88547 / 120960 : ℝ) • (f tn3 yn3 - f tn3 zn3)))
      (h • ((41499 / 120960 : ℝ) • (f tn2 yn2 - f tn2 zn2)))
      (h • ((11351 / 120960 : ℝ) • (f tn1 yn1 - f tn1 zn1)))
      (h • ((1375 / 120960 : ℝ) • (f tn yn - f tn zn))) τ
  have hmain :
      ‖yn7 - zn7‖
        ≤ ‖yn6 - zn6‖
          + (36799 / 120960 : ℝ) * h * L * ‖yn7 - zn7‖
          + (139849 / 120960 : ℝ) * h * L * ‖yn6 - zn6‖
          + (121797 / 120960 : ℝ) * h * L * ‖yn5 - zn5‖
          + (123133 / 120960 : ℝ) * h * L * ‖yn4 - zn4‖
          + (88547 / 120960 : ℝ) * h * L * ‖yn3 - zn3‖
          + (41499 / 120960 : ℝ) * h * L * ‖yn2 - zn2‖
          + (11351 / 120960 : ℝ) * h * L * ‖yn1 - zn1‖
          + (1375 / 120960 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    calc ‖yn7 - zn7‖
        = ‖(yn6 - zn6)
            + h • ((36799 / 120960 : ℝ) • (f tn7 yn7 - f tn7 zn7))
            + h • ((139849 / 120960 : ℝ) • (f tn6 yn6 - f tn6 zn6))
            - h • ((121797 / 120960 : ℝ) • (f tn5 yn5 - f tn5 zn5))
            + h • ((123133 / 120960 : ℝ) • (f tn4 yn4 - f tn4 zn4))
            - h • ((88547 / 120960 : ℝ) • (f tn3 yn3 - f tn3 zn3))
            + h • ((41499 / 120960 : ℝ) • (f tn2 yn2 - f tn2 zn2))
            - h • ((11351 / 120960 : ℝ) • (f tn1 yn1 - f tn1 zn1))
            + h • ((1375 / 120960 : ℝ) • (f tn yn - f tn zn))
            - τ‖ := by rw [halg]
      _ ≤ ‖yn6 - zn6‖
          + ‖h • ((36799 / 120960 : ℝ) • (f tn7 yn7 - f tn7 zn7))‖
          + ‖h • ((139849 / 120960 : ℝ) • (f tn6 yn6 - f tn6 zn6))‖
          + ‖h • ((121797 / 120960 : ℝ) • (f tn5 yn5 - f tn5 zn5))‖
          + ‖h • ((123133 / 120960 : ℝ) • (f tn4 yn4 - f tn4 zn4))‖
          + ‖h • ((88547 / 120960 : ℝ) • (f tn3 yn3 - f tn3 zn3))‖
          + ‖h • ((41499 / 120960 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
          + ‖h • ((11351 / 120960 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
          + ‖h • ((1375 / 120960 : ℝ) • (f tn yn - f tn zn))‖
          + ‖τ‖ := htri
      _ ≤ ‖yn6 - zn6‖
          + (36799 / 120960 : ℝ) * h * L * ‖yn7 - zn7‖
          + (139849 / 120960 : ℝ) * h * L * ‖yn6 - zn6‖
          + (121797 / 120960 : ℝ) * h * L * ‖yn5 - zn5‖
          + (123133 / 120960 : ℝ) * h * L * ‖yn4 - zn4‖
          + (88547 / 120960 : ℝ) * h * L * ‖yn3 - zn3‖
          + (41499 / 120960 : ℝ) * h * L * ‖yn2 - zn2‖
          + (11351 / 120960 : ℝ) * h * L * ‖yn1 - zn1‖
          + (1375 / 120960 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
        linarith [h36799_norm, h139849_norm, h121797_norm, h123133_norm,
          h88547_norm, h41499_norm, h11351_norm, h1375_norm]
  linarith [hmain]

theorem am7Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (36799 / 120960 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM7TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
      ≤ (1 + h * (10 * L))
            * max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
        + 2 * ‖am7VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖yseq n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set en3 : ℝ :=
    ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖ with hen3_def
  set en4 : ℝ :=
    ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖ with hen4_def
  set en5 : ℝ :=
    ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖ with hen5_def
  set en6 : ℝ :=
    ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖ with hen6_def
  set en7 : ℝ :=
    ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖ with hen7_def
  set τabs : ℝ :=
    ‖am7VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max en en1) en2) en3) en4) en5) en6
    with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hen4_nn : 0 ≤ en4 := norm_nonneg _
  have hen5_nn : 0 ≤ en5 := norm_nonneg _
  have hen6_nn : 0 ≤ en6 := norm_nonneg _
  have hen7_nn : 0 ≤ en7 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen_le_E : en ≤ Emax :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen1_le_E : en1 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen2_le_E : en2 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen3_le_E : en3 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen4_le_E : en4 ≤ Emax :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen5_le_E : en5 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen6_le_E : en6 ≤ Emax := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 60480 / 36799 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (36799 / 120960 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (36799 / 120960 : ℝ) * h * L) * en7
        ≤ en6
          + (139849 / 120960 : ℝ) * h * L * en6
          + (121797 / 120960 : ℝ) * h * L * en5
          + (123133 / 120960 : ℝ) * h * L * en4
          + (88547 / 120960 : ℝ) * h * L * en3
          + (41499 / 120960 : ℝ) * h * L * en2
          + (11351 / 120960 : ℝ) * h * L * en1
          + (1375 / 120960 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hτabs_def]
      using
      (am7Vec_one_step_lipschitz (E := E) (h := h) (L := L)
        hh hsmall hf t₀ hy y hyf n)
  have h139849_nn : 0 ≤ (139849 / 120960 : ℝ) * h * L := by positivity
  have h121797_nn : 0 ≤ (121797 / 120960 : ℝ) * h * L := by positivity
  have h123133_nn : 0 ≤ (123133 / 120960 : ℝ) * h * L := by positivity
  have h88547_nn : 0 ≤ (88547 / 120960 : ℝ) * h * L := by positivity
  have h41499_nn : 0 ≤ (41499 / 120960 : ℝ) * h * L := by positivity
  have h11351_nn : 0 ≤ (11351 / 120960 : ℝ) * h * L := by positivity
  have h1375_nn : 0 ≤ (1375 / 120960 : ℝ) * h * L := by positivity
  have h139849_le :
      (139849 / 120960 : ℝ) * h * L * en6
        ≤ (139849 / 120960 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen6_le_E h139849_nn
  have h121797_le :
      (121797 / 120960 : ℝ) * h * L * en5
        ≤ (121797 / 120960 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen5_le_E h121797_nn
  have h123133_le :
      (123133 / 120960 : ℝ) * h * L * en4
        ≤ (123133 / 120960 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen4_le_E h123133_nn
  have h88547_le :
      (88547 / 120960 : ℝ) * h * L * en3
        ≤ (88547 / 120960 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen3_le_E h88547_nn
  have h41499_le :
      (41499 / 120960 : ℝ) * h * L * en2
        ≤ (41499 / 120960 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen2_le_E h41499_nn
  have h11351_le :
      (11351 / 120960 : ℝ) * h * L * en1
        ≤ (11351 / 120960 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen1_le_E h11351_nn
  have h1375_le :
      (1375 / 120960 : ℝ) * h * L * en
        ≤ (1375 / 120960 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen_le_E h1375_nn
  have hR_le :
      en6
          + (139849 / 120960 : ℝ) * h * L * en6
          + (121797 / 120960 : ℝ) * h * L * en5
          + (123133 / 120960 : ℝ) * h * L * en4
          + (88547 / 120960 : ℝ) * h * L * en3
          + (41499 / 120960 : ℝ) * h * L * en2
          + (11351 / 120960 : ℝ) * h * L * en1
          + (1375 / 120960 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (527551 / 120960 : ℝ) * (h * L)) * Emax + τabs := by
    have h_alg :
        Emax + (139849 / 120960 : ℝ) * h * L * Emax
            + (121797 / 120960 : ℝ) * h * L * Emax
            + (123133 / 120960 : ℝ) * h * L * Emax
            + (88547 / 120960 : ℝ) * h * L * Emax
            + (41499 / 120960 : ℝ) * h * L * Emax
            + (11351 / 120960 : ℝ) * h * L * Emax
            + (1375 / 120960 : ℝ) * h * L * Emax + τabs
          = (1 + (527551 / 120960 : ℝ) * (h * L)) * Emax + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (527551 / 120960 : ℝ) * (h * L)
        ≤ (1 - (36799 / 120960 : ℝ) * h * L) * (1 + h * (10 * L)) := by
    have hxL_eq :
        (1 - (36799 / 120960 : ℝ) * h * L) * (1 + h * (10 * L))
          - (1 + (527551 / 120960 : ℝ) * (h * L))
          = (h * L) / 120960 * (645250 - 367990 * (h * L)) := by ring
    have hpos : 0 ≤ 645250 - 367990 * (h * L) := by
      have hbound : 367990 * (h * L) ≤ 367990 * (60480 / 36799) := by
        have h367990_nn : (0 : ℝ) ≤ 367990 := by norm_num
        exact mul_le_mul_of_nonneg_left hx_small h367990_nn
      have hnum : (367990 : ℝ) * (60480 / 36799) ≤ 645250 := by norm_num
      linarith
    have hprod : 0 ≤ (h * L) / 120960 * (645250 - 367990 * (h * L)) := by
      apply mul_nonneg
      · positivity
      · exact hpos
    linarith
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (36799 / 120960 : ℝ) * h * L) * 2 := by
    linarith [hsmall]
  have hE_part :
      (1 + (527551 / 120960 : ℝ) * (h * L)) * Emax
        ≤ ((1 - (36799 / 120960 : ℝ) * h * L) * (1 + h * (10 * L))) * Emax :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (36799 / 120960 : ℝ) * h * L) * 2) * τabs := by
    simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (527551 / 120960 : ℝ) * (h * L)) * Emax + τabs
        ≤ (1 - (36799 / 120960 : ℝ) * h * L)
            * ((1 + h * (10 * L)) * Emax + 2 * τabs) := by
    have hsplit :
        (1 - (36799 / 120960 : ℝ) * h * L)
            * ((1 + h * (10 * L)) * Emax + 2 * τabs)
          = ((1 - (36799 / 120960 : ℝ) * h * L) * (1 + h * (10 * L))) * Emax
              + ((1 - (36799 / 120960 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (36799 / 120960 : ℝ) * h * L) * en7
        ≤ (1 - (36799 / 120960 : ℝ) * h * L)
            * ((1 + h * (10 * L)) * Emax + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  exact le_of_mul_le_mul_left hprod hA_pos

theorem am7Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (36799 / 120960 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM7TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max
          ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
          ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
          ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
      ≤ (1 + h * (10 * L))
            * max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
        + 2 * ‖am7VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖yseq n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set en3 : ℝ :=
    ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖ with hen3_def
  set en4 : ℝ :=
    ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖ with hen4_def
  set en5 : ℝ :=
    ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖ with hen5_def
  set en6 : ℝ :=
    ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖ with hen6_def
  set en7 : ℝ :=
    ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖ with hen7_def
  set τabs : ℝ :=
    ‖am7VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max en en1) en2) en3) en4) en5) en6
    with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hen4_nn : 0 ≤ en4 := norm_nonneg _
  have hen5_nn : 0 ≤ en5 := norm_nonneg _
  have hen6_nn : 0 ≤ en6 := norm_nonneg _
  have hen7_nn : 0 ≤ en7 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen1_le_E : en1 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen2_le_E : en2 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen3_le_E : en3 ≤ Emax :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen4_le_E : en4 ≤ Emax :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen5_le_E : en5 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen6_le_E : en6 ≤ Emax := le_max_right _ _
  have h10hL_nn : 0 ≤ h * (10 * L) := by positivity
  have hen7_bd :
      en7 ≤ (1 + h * (10 * L)) * Emax + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hτabs_def, hE_def]
      using
      (am7Vec_one_step_error_bound (E := E) (h := h) (L := L)
        hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : Emax ≤ (1 + h * (10 * L)) * Emax := by
    have hone : (1 : ℝ) * Emax ≤ (1 + h * (10 * L)) * Emax :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (10 * L)) * Emax + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (10 * L)) * Emax + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (10 * L)) * Emax + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  have hen4_bd : en4 ≤ (1 + h * (10 * L)) * Emax + 2 * τabs := by
    linarith [hen4_le_E, hE_le_grow]
  have hen5_bd : en5 ≤ (1 + h * (10 * L)) * Emax + 2 * τabs := by
    linarith [hen5_le_E, hE_le_grow]
  have hen6_bd : en6 ≤ (1 + h * (10 * L)) * Emax + 2 * τabs := by
    linarith [hen6_le_E, hE_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd)
    hen4_bd) hen5_bd) hen6_bd) hen7_bd

private lemma am7Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y6 y7 d0 d1 d2 d3 d4 d5 d6 d7 dd ddd dddd ddddd dddddd ddddddd
        dddddddd : E) (h : ℝ) :
    y7 - y6 - h • ((36799 / 120960 : ℝ) • d7 + (139849 / 120960 : ℝ) • d6
                  - (121797 / 120960 : ℝ) • d5 + (123133 / 120960 : ℝ) • d4
                  - (88547 / 120960 : ℝ) • d3 + (41499 / 120960 : ℝ) • d2
                  - (11351 / 120960 : ℝ) • d1 + (1375 / 120960 : ℝ) • d0)
      = (y7 - y0 - (7 * h) • d0
            - ((7 * h) ^ 2 / 2) • dd
            - ((7 * h) ^ 3 / 6) • ddd
            - ((7 * h) ^ 4 / 24) • dddd
            - ((7 * h) ^ 5 / 120) • ddddd
            - ((7 * h) ^ 6 / 720) • dddddd
            - ((7 * h) ^ 7 / 5040) • ddddddd
            - ((7 * h) ^ 8 / 40320) • dddddddd)
        - (y6 - y0 - (6 * h) • d0
            - ((6 * h) ^ 2 / 2) • dd
            - ((6 * h) ^ 3 / 6) • ddd
            - ((6 * h) ^ 4 / 24) • dddd
            - ((6 * h) ^ 5 / 120) • ddddd
            - ((6 * h) ^ 6 / 720) • dddddd
            - ((6 * h) ^ 7 / 5040) • ddddddd
            - ((6 * h) ^ 8 / 40320) • dddddddd)
        - (36799 * h / 120960 : ℝ)
            • (d7 - d0 - (7 * h) • dd
                - ((7 * h) ^ 2 / 2) • ddd
                - ((7 * h) ^ 3 / 6) • dddd
                - ((7 * h) ^ 4 / 24) • ddddd
                - ((7 * h) ^ 5 / 120) • dddddd
                - ((7 * h) ^ 6 / 720) • ddddddd
                - ((7 * h) ^ 7 / 5040) • dddddddd)
        - (139849 * h / 120960 : ℝ)
            • (d6 - d0 - (6 * h) • dd
                - ((6 * h) ^ 2 / 2) • ddd
                - ((6 * h) ^ 3 / 6) • dddd
                - ((6 * h) ^ 4 / 24) • ddddd
                - ((6 * h) ^ 5 / 120) • dddddd
                - ((6 * h) ^ 6 / 720) • ddddddd
                - ((6 * h) ^ 7 / 5040) • dddddddd)
        + (121797 * h / 120960 : ℝ)
            • (d5 - d0 - (5 * h) • dd
                - ((5 * h) ^ 2 / 2) • ddd
                - ((5 * h) ^ 3 / 6) • dddd
                - ((5 * h) ^ 4 / 24) • ddddd
                - ((5 * h) ^ 5 / 120) • dddddd
                - ((5 * h) ^ 6 / 720) • ddddddd
                - ((5 * h) ^ 7 / 5040) • dddddddd)
        - (123133 * h / 120960 : ℝ)
            • (d4 - d0 - (4 * h) • dd
                - ((4 * h) ^ 2 / 2) • ddd
                - ((4 * h) ^ 3 / 6) • dddd
                - ((4 * h) ^ 4 / 24) • ddddd
                - ((4 * h) ^ 5 / 120) • dddddd
                - ((4 * h) ^ 6 / 720) • ddddddd
                - ((4 * h) ^ 7 / 5040) • dddddddd)
        + (88547 * h / 120960 : ℝ)
            • (d3 - d0 - (3 * h) • dd
                - ((3 * h) ^ 2 / 2) • ddd
                - ((3 * h) ^ 3 / 6) • dddd
                - ((3 * h) ^ 4 / 24) • ddddd
                - ((3 * h) ^ 5 / 120) • dddddd
                - ((3 * h) ^ 6 / 720) • ddddddd
                - ((3 * h) ^ 7 / 5040) • dddddddd)
        - (41499 * h / 120960 : ℝ)
            • (d2 - d0 - (2 * h) • dd
                - ((2 * h) ^ 2 / 2) • ddd
                - ((2 * h) ^ 3 / 6) • dddd
                - ((2 * h) ^ 4 / 24) • ddddd
                - ((2 * h) ^ 5 / 120) • dddddd
                - ((2 * h) ^ 6 / 720) • ddddddd
                - ((2 * h) ^ 7 / 5040) • dddddddd)
      + (11351 * h / 120960 : ℝ)
            • (d1 - d0 - h • dd
                - (h ^ 2 / 2) • ddd
                - (h ^ 3 / 6) • dddd
                - (h ^ 4 / 24) • ddddd
                - (h ^ 5 / 120) • dddddd
                - (h ^ 6 / 720) • ddddddd
                - (h ^ 7 / 5040) • dddddddd) := by
  simp only [smul_sub, smul_add, smul_smul]
  module

private lemma am7Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 362880 * (7 * h) ^ 9 + M / 362880 * (6 * h) ^ 9
      + (36799 * h / 120960) * (M / 40320 * (7 * h) ^ 8)
      + (139849 * h / 120960) * (M / 40320 * (6 * h) ^ 8)
      + (121797 * h / 120960) * (M / 40320 * (5 * h) ^ 8)
      + (123133 * h / 120960) * (M / 40320 * (4 * h) ^ 8)
      + (88547 * h / 120960) * (M / 40320 * (3 * h) ^ 8)
      + (41499 * h / 120960) * (M / 40320 * (2 * h) ^ 8)
      + (11351 * h / 120960) * (M / 40320 * h ^ 8)
      = (84361887977 / 348364800 : ℝ) * M * h ^ 9 := by
  ring

private lemma am7Vec_residual_nine_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G J K R : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (36799 * h / 120960 : ℝ) • C - (139849 * h / 120960 : ℝ) • D
        + (121797 * h / 120960 : ℝ) • F - (123133 * h / 120960 : ℝ) • G
        + (88547 * h / 120960 : ℝ) • J - (41499 * h / 120960 : ℝ) • K
        + (11351 * h / 120960 : ℝ) • R‖
      ≤ ‖A‖ + ‖B‖ + (36799 * h / 120960) * ‖C‖
          + (139849 * h / 120960) * ‖D‖ + (121797 * h / 120960) * ‖F‖
          + (123133 * h / 120960) * ‖G‖ + (88547 * h / 120960) * ‖J‖
          + (41499 * h / 120960) * ‖K‖ + (11351 * h / 120960) * ‖R‖ := by
  have h36799h_nn : 0 ≤ (36799 * h / 120960 : ℝ) := by linarith
  have h139849h_nn : 0 ≤ (139849 * h / 120960 : ℝ) := by linarith
  have h121797h_nn : 0 ≤ (121797 * h / 120960 : ℝ) := by linarith
  have h123133h_nn : 0 ≤ (123133 * h / 120960 : ℝ) := by linarith
  have h88547h_nn : 0 ≤ (88547 * h / 120960 : ℝ) := by linarith
  have h41499h_nn : 0 ≤ (41499 * h / 120960 : ℝ) := by linarith
  have h11351h_nn : 0 ≤ (11351 * h / 120960 : ℝ) := by linarith
  have hC_norm :
      ‖(36799 * h / 120960 : ℝ) • C‖ = (36799 * h / 120960) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg h36799h_nn]
  have hD_norm :
      ‖(139849 * h / 120960 : ℝ) • D‖ = (139849 * h / 120960) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg h139849h_nn]
  have hF_norm :
      ‖(121797 * h / 120960 : ℝ) • F‖ = (121797 * h / 120960) * ‖F‖ := by
    rw [norm_smul, Real.norm_of_nonneg h121797h_nn]
  have hG_norm :
      ‖(123133 * h / 120960 : ℝ) • G‖ = (123133 * h / 120960) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg h123133h_nn]
  have hJ_norm :
      ‖(88547 * h / 120960 : ℝ) • J‖ = (88547 * h / 120960) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg h88547h_nn]
  have hK_norm :
      ‖(41499 * h / 120960 : ℝ) • K‖ = (41499 * h / 120960) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg h41499h_nn]
  have hR_norm :
      ‖(11351 * h / 120960 : ℝ) • R‖ = (11351 * h / 120960) * ‖R‖ := by
    rw [norm_smul, Real.norm_of_nonneg h11351h_nn]
  have h1 :
      ‖A - B - (36799 * h / 120960 : ℝ) • C - (139849 * h / 120960 : ℝ) • D
          + (121797 * h / 120960 : ℝ) • F - (123133 * h / 120960 : ℝ) • G
          + (88547 * h / 120960 : ℝ) • J - (41499 * h / 120960 : ℝ) • K
          + (11351 * h / 120960 : ℝ) • R‖
        ≤ ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D
              + (121797 * h / 120960 : ℝ) • F
              - (123133 * h / 120960 : ℝ) • G
              + (88547 * h / 120960 : ℝ) • J
              - (41499 * h / 120960 : ℝ) • K‖
          + ‖(11351 * h / 120960 : ℝ) • R‖ := norm_add_le _ _
  have h2 :
      ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D
              + (121797 * h / 120960 : ℝ) • F
              - (123133 * h / 120960 : ℝ) • G
              + (88547 * h / 120960 : ℝ) • J
              - (41499 * h / 120960 : ℝ) • K‖
        ≤ ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D
              + (121797 * h / 120960 : ℝ) • F
              - (123133 * h / 120960 : ℝ) • G
              + (88547 * h / 120960 : ℝ) • J‖
          + ‖(41499 * h / 120960 : ℝ) • K‖ := norm_sub_le _ _
  have h3 :
      ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D
              + (121797 * h / 120960 : ℝ) • F
              - (123133 * h / 120960 : ℝ) • G
              + (88547 * h / 120960 : ℝ) • J‖
        ≤ ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D
              + (121797 * h / 120960 : ℝ) • F
              - (123133 * h / 120960 : ℝ) • G‖
          + ‖(88547 * h / 120960 : ℝ) • J‖ := norm_add_le _ _
  have h4 :
      ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D
              + (121797 * h / 120960 : ℝ) • F
              - (123133 * h / 120960 : ℝ) • G‖
        ≤ ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D
              + (121797 * h / 120960 : ℝ) • F‖
          + ‖(123133 * h / 120960 : ℝ) • G‖ := norm_sub_le _ _
  have h5 :
      ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D
              + (121797 * h / 120960 : ℝ) • F‖
        ≤ ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D‖
          + ‖(121797 * h / 120960 : ℝ) • F‖ := norm_add_le _ _
  have h6 :
      ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D‖
        ≤ ‖A - B - (36799 * h / 120960 : ℝ) • C‖
          + ‖(139849 * h / 120960 : ℝ) • D‖ := norm_sub_le _ _
  have h7 :
      ‖A - B - (36799 * h / 120960 : ℝ) • C‖
        ≤ ‖A - B‖ + ‖(36799 * h / 120960 : ℝ) • C‖ := norm_sub_le _ _
  have h8 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith [hC_norm.le, hC_norm.ge, hD_norm.le, hD_norm.ge, hF_norm.le,
    hF_norm.ge, hG_norm.le, hG_norm.ge, hJ_norm.le, hJ_norm.ge,
    hK_norm.le, hK_norm.ge, hR_norm.le, hR_norm.ge]

private lemma am7Vec_residual_combine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D F G J K R : E)
    (htri : ‖A - B - (36799 * h / 120960 : ℝ) • C
              - (139849 * h / 120960 : ℝ) • D + (121797 * h / 120960 : ℝ) • F
              - (123133 * h / 120960 : ℝ) • G + (88547 * h / 120960 : ℝ) • J
              - (41499 * h / 120960 : ℝ) • K + (11351 * h / 120960 : ℝ) • R‖
            ≤ ‖A‖ + ‖B‖ + (36799 * h / 120960) * ‖C‖
              + (139849 * h / 120960) * ‖D‖ + (121797 * h / 120960) * ‖F‖
              + (123133 * h / 120960) * ‖G‖ + (88547 * h / 120960) * ‖J‖
              + (41499 * h / 120960) * ‖K‖ + (11351 * h / 120960) * ‖R‖)
    (hA_bd : ‖A‖ ≤ M / 362880 * (7 * h) ^ 9)
    (hB_bd : ‖B‖ ≤ M / 362880 * (6 * h) ^ 9)
    (hC_bd : ‖C‖ ≤ M / 40320 * (7 * h) ^ 8)
    (hD_bd : ‖D‖ ≤ M / 40320 * (6 * h) ^ 8)
    (hF_bd : ‖F‖ ≤ M / 40320 * (5 * h) ^ 8)
    (hG_bd : ‖G‖ ≤ M / 40320 * (4 * h) ^ 8)
    (hJ_bd : ‖J‖ ≤ M / 40320 * (3 * h) ^ 8)
    (hK_bd : ‖K‖ ≤ M / 40320 * (2 * h) ^ 8)
    (hR_bd : ‖R‖ ≤ M / 40320 * h ^ 8) :
    ‖A - B - (36799 * h / 120960 : ℝ) • C - (139849 * h / 120960 : ℝ) • D
        + (121797 * h / 120960 : ℝ) • F - (123133 * h / 120960 : ℝ) • G
        + (88547 * h / 120960 : ℝ) • J - (41499 * h / 120960 : ℝ) • K
        + (11351 * h / 120960 : ℝ) • R‖
      ≤ (243 : ℝ) * M * h ^ 9 := by
  have h36799h_nn : 0 ≤ (36799 * h / 120960 : ℝ) := by linarith
  have h139849h_nn : 0 ≤ (139849 * h / 120960 : ℝ) := by linarith
  have h121797h_nn : 0 ≤ (121797 * h / 120960 : ℝ) := by linarith
  have h123133h_nn : 0 ≤ (123133 * h / 120960 : ℝ) := by linarith
  have h88547h_nn : 0 ≤ (88547 * h / 120960 : ℝ) := by linarith
  have h41499h_nn : 0 ≤ (41499 * h / 120960 : ℝ) := by linarith
  have h11351h_nn : 0 ≤ (11351 * h / 120960 : ℝ) := by linarith
  have h36799C_bd : (36799 * h / 120960) * ‖C‖
      ≤ (36799 * h / 120960) * (M / 40320 * (7 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hC_bd h36799h_nn
  have h139849D_bd : (139849 * h / 120960) * ‖D‖
      ≤ (139849 * h / 120960) * (M / 40320 * (6 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hD_bd h139849h_nn
  have h121797F_bd : (121797 * h / 120960) * ‖F‖
      ≤ (121797 * h / 120960) * (M / 40320 * (5 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hF_bd h121797h_nn
  have h123133G_bd : (123133 * h / 120960) * ‖G‖
      ≤ (123133 * h / 120960) * (M / 40320 * (4 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hG_bd h123133h_nn
  have h88547J_bd : (88547 * h / 120960) * ‖J‖
      ≤ (88547 * h / 120960) * (M / 40320 * (3 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hJ_bd h88547h_nn
  have h41499K_bd : (41499 * h / 120960) * ‖K‖
      ≤ (41499 * h / 120960) * (M / 40320 * (2 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hK_bd h41499h_nn
  have h11351R_bd : (11351 * h / 120960) * ‖R‖
      ≤ (11351 * h / 120960) * (M / 40320 * h ^ 8) :=
    mul_le_mul_of_nonneg_left hR_bd h11351h_nn
  have hbound_alg :
      M / 362880 * (7 * h) ^ 9 + M / 362880 * (6 * h) ^ 9
        + (36799 * h / 120960) * (M / 40320 * (7 * h) ^ 8)
        + (139849 * h / 120960) * (M / 40320 * (6 * h) ^ 8)
        + (121797 * h / 120960) * (M / 40320 * (5 * h) ^ 8)
        + (123133 * h / 120960) * (M / 40320 * (4 * h) ^ 8)
        + (88547 * h / 120960) * (M / 40320 * (3 * h) ^ 8)
        + (41499 * h / 120960) * (M / 40320 * (2 * h) ^ 8)
        + (11351 * h / 120960) * (M / 40320 * h ^ 8)
        = (84361887977 / 348364800 : ℝ) * M * h ^ 9 :=
    am7Vec_residual_bound_alg_identity M h
  have hh9_nn : 0 ≤ h ^ 9 := by positivity
  have hMh9_nn : 0 ≤ M * h ^ 9 := mul_nonneg hMnn hh9_nn
  have hslack :
      (84361887977 / 348364800 : ℝ) * M * h ^ 9 ≤ 243 * M * h ^ 9 := by
    have hle : (84361887977 / 348364800 : ℝ) ≤ 243 := by norm_num
    have hbase :
        (84361887977 / 348364800 : ℝ) * (M * h ^ 9) ≤ 243 * (M * h ^ 9) :=
      mul_le_mul_of_nonneg_right hle hMh9_nn
    have hL : (84361887977 / 348364800 : ℝ) * M * h ^ 9
        = (84361887977 / 348364800 : ℝ) * (M * h ^ 9) := by ring
    have hR : (243 : ℝ) * M * h ^ 9 = 243 * (M * h ^ 9) := by ring
    rw [hL, hR]
    exact hbase
  linarith [htri, hA_bd, hB_bd, h36799C_bd, h139849D_bd, h121797F_bd,
    h123133G_bd, h88547J_bd, h41499K_bd, h11351R_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

theorem am7Vec_pointwise_residual_bound
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
    (hh : 0 ≤ h) :
    ‖y (t + 7 * h) - y (t + 6 * h)
        - h • ((36799 / 120960 : ℝ) • deriv y (t + 7 * h)
              + (139849 / 120960 : ℝ) • deriv y (t + 6 * h)
              - (121797 / 120960 : ℝ) • deriv y (t + 5 * h)
              + (123133 / 120960 : ℝ) • deriv y (t + 4 * h)
              - (88547 / 120960 : ℝ) • deriv y (t + 3 * h)
              + (41499 / 120960 : ℝ) • deriv y (t + 2 * h)
              - (11351 / 120960 : ℝ) • deriv y (t + h)
              + (1375 / 120960 : ℝ) • deriv y t)‖
      ≤ (243 : ℝ) * M * h ^ 9 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have hRy6 :=
    y_ninth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRy7 :=
    y_ninth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
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
  set y6 : E := y (t + 6 * h) with hy6_def
  set y7 : E := y (t + 7 * h) with hy7_def
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
  have hLTE_eq :
      y7 - y6 - h • ((36799 / 120960 : ℝ) • d7 + (139849 / 120960 : ℝ) • d6
                    - (121797 / 120960 : ℝ) • d5 + (123133 / 120960 : ℝ) • d4
                    - (88547 / 120960 : ℝ) • d3 + (41499 / 120960 : ℝ) • d2
                    - (11351 / 120960 : ℝ) • d1 + (1375 / 120960 : ℝ) • d0)
        = (y7 - y0 - (7 * h) • d0
              - ((7 * h) ^ 2 / 2) • dd
              - ((7 * h) ^ 3 / 6) • ddd
              - ((7 * h) ^ 4 / 24) • dddd
              - ((7 * h) ^ 5 / 120) • ddddd
              - ((7 * h) ^ 6 / 720) • dddddd
              - ((7 * h) ^ 7 / 5040) • ddddddd
              - ((7 * h) ^ 8 / 40320) • dddddddd)
          - (y6 - y0 - (6 * h) • d0
              - ((6 * h) ^ 2 / 2) • dd
              - ((6 * h) ^ 3 / 6) • ddd
              - ((6 * h) ^ 4 / 24) • dddd
              - ((6 * h) ^ 5 / 120) • ddddd
              - ((6 * h) ^ 6 / 720) • dddddd
              - ((6 * h) ^ 7 / 5040) • ddddddd
              - ((6 * h) ^ 8 / 40320) • dddddddd)
          - (36799 * h / 120960 : ℝ)
              • (d7 - d0 - (7 * h) • dd
                  - ((7 * h) ^ 2 / 2) • ddd
                  - ((7 * h) ^ 3 / 6) • dddd
                  - ((7 * h) ^ 4 / 24) • ddddd
                  - ((7 * h) ^ 5 / 120) • dddddd
                  - ((7 * h) ^ 6 / 720) • ddddddd
                  - ((7 * h) ^ 7 / 5040) • dddddddd)
          - (139849 * h / 120960 : ℝ)
              • (d6 - d0 - (6 * h) • dd
                  - ((6 * h) ^ 2 / 2) • ddd
                  - ((6 * h) ^ 3 / 6) • dddd
                  - ((6 * h) ^ 4 / 24) • ddddd
                  - ((6 * h) ^ 5 / 120) • dddddd
                  - ((6 * h) ^ 6 / 720) • ddddddd
                  - ((6 * h) ^ 7 / 5040) • dddddddd)
          + (121797 * h / 120960 : ℝ)
              • (d5 - d0 - (5 * h) • dd
                  - ((5 * h) ^ 2 / 2) • ddd
                  - ((5 * h) ^ 3 / 6) • dddd
                  - ((5 * h) ^ 4 / 24) • ddddd
                  - ((5 * h) ^ 5 / 120) • dddddd
                  - ((5 * h) ^ 6 / 720) • ddddddd
                  - ((5 * h) ^ 7 / 5040) • dddddddd)
          - (123133 * h / 120960 : ℝ)
              • (d4 - d0 - (4 * h) • dd
                  - ((4 * h) ^ 2 / 2) • ddd
                  - ((4 * h) ^ 3 / 6) • dddd
                  - ((4 * h) ^ 4 / 24) • ddddd
                  - ((4 * h) ^ 5 / 120) • dddddd
                  - ((4 * h) ^ 6 / 720) • ddddddd
                  - ((4 * h) ^ 7 / 5040) • dddddddd)
          + (88547 * h / 120960 : ℝ)
              • (d3 - d0 - (3 * h) • dd
                  - ((3 * h) ^ 2 / 2) • ddd
                  - ((3 * h) ^ 3 / 6) • dddd
                  - ((3 * h) ^ 4 / 24) • ddddd
                  - ((3 * h) ^ 5 / 120) • dddddd
                  - ((3 * h) ^ 6 / 720) • ddddddd
                  - ((3 * h) ^ 7 / 5040) • dddddddd)
          - (41499 * h / 120960 : ℝ)
              • (d2 - d0 - (2 * h) • dd
                  - ((2 * h) ^ 2 / 2) • ddd
                  - ((2 * h) ^ 3 / 6) • dddd
                  - ((2 * h) ^ 4 / 24) • ddddd
                  - ((2 * h) ^ 5 / 120) • dddddd
                  - ((2 * h) ^ 6 / 720) • ddddddd
                  - ((2 * h) ^ 7 / 5040) • dddddddd)
          + (11351 * h / 120960 : ℝ)
              • (d1 - d0 - h • dd
                  - (h ^ 2 / 2) • ddd
                  - (h ^ 3 / 6) • dddd
                  - (h ^ 4 / 24) • ddddd
                  - (h ^ 5 / 120) • dddddd
                  - (h ^ 6 / 720) • ddddddd
                  - (h ^ 7 / 5040) • dddddddd) :=
    am7Vec_residual_alg_identity y0 y6 y7 d0 d1 d2 d3 d4 d5 d6 d7 dd ddd dddd
      ddddd dddddd ddddddd dddddddd h
  rw [hLTE_eq]
  set A : E := y7 - y0 - (7 * h) • d0
            - ((7 * h) ^ 2 / 2) • dd
            - ((7 * h) ^ 3 / 6) • ddd
            - ((7 * h) ^ 4 / 24) • dddd
            - ((7 * h) ^ 5 / 120) • ddddd
            - ((7 * h) ^ 6 / 720) • dddddd
            - ((7 * h) ^ 7 / 5040) • ddddddd
            - ((7 * h) ^ 8 / 40320) • dddddddd with hA_def
  set B : E := y6 - y0 - (6 * h) • d0
            - ((6 * h) ^ 2 / 2) • dd
            - ((6 * h) ^ 3 / 6) • ddd
            - ((6 * h) ^ 4 / 24) • dddd
            - ((6 * h) ^ 5 / 120) • ddddd
            - ((6 * h) ^ 6 / 720) • dddddd
            - ((6 * h) ^ 7 / 5040) • ddddddd
            - ((6 * h) ^ 8 / 40320) • dddddddd with hB_def
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
  set F : E := d5 - d0 - (5 * h) • dd
            - ((5 * h) ^ 2 / 2) • ddd
            - ((5 * h) ^ 3 / 6) • dddd
            - ((5 * h) ^ 4 / 24) • ddddd
            - ((5 * h) ^ 5 / 120) • dddddd
            - ((5 * h) ^ 6 / 720) • ddddddd
            - ((5 * h) ^ 7 / 5040) • dddddddd with hF_def
  set G : E := d4 - d0 - (4 * h) • dd
            - ((4 * h) ^ 2 / 2) • ddd
            - ((4 * h) ^ 3 / 6) • dddd
            - ((4 * h) ^ 4 / 24) • ddddd
            - ((4 * h) ^ 5 / 120) • dddddd
            - ((4 * h) ^ 6 / 720) • ddddddd
            - ((4 * h) ^ 7 / 5040) • dddddddd with hG_def
  set J : E := d3 - d0 - (3 * h) • dd
            - ((3 * h) ^ 2 / 2) • ddd
            - ((3 * h) ^ 3 / 6) • dddd
            - ((3 * h) ^ 4 / 24) • ddddd
            - ((3 * h) ^ 5 / 120) • dddddd
            - ((3 * h) ^ 6 / 720) • ddddddd
            - ((3 * h) ^ 7 / 5040) • dddddddd with hJ_def
  set K : E := d2 - d0 - (2 * h) • dd
            - ((2 * h) ^ 2 / 2) • ddd
            - ((2 * h) ^ 3 / 6) • dddd
            - ((2 * h) ^ 4 / 24) • ddddd
            - ((2 * h) ^ 5 / 120) • dddddd
            - ((2 * h) ^ 6 / 720) • ddddddd
            - ((2 * h) ^ 7 / 5040) • dddddddd with hK_def
  set R : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd
            - (h ^ 4 / 24) • ddddd
            - (h ^ 5 / 120) • dddddd
            - (h ^ 6 / 720) • ddddddd
            - (h ^ 7 / 5040) • dddddddd with hR_def
  have htri := am7Vec_residual_nine_term_triangle A B C D F G J K R h hh
  have hA_bd : ‖A‖ ≤ M / 362880 * (7 * h) ^ 9 := hRy7
  have hB_bd : ‖B‖ ≤ M / 362880 * (6 * h) ^ 9 := hRy6
  have hC_bd : ‖C‖ ≤ M / 40320 * (7 * h) ^ 8 := hRyp7
  have hD_bd : ‖D‖ ≤ M / 40320 * (6 * h) ^ 8 := hRyp6
  have hF_bd : ‖F‖ ≤ M / 40320 * (5 * h) ^ 8 := hRyp5
  have hG_bd : ‖G‖ ≤ M / 40320 * (4 * h) ^ 8 := hRyp4
  have hJ_bd : ‖J‖ ≤ M / 40320 * (3 * h) ^ 8 := hRyp3
  have hK_bd : ‖K‖ ≤ M / 40320 * (2 * h) ^ 8 := hRyp2
  have hR_bd : ‖R‖ ≤ M / 40320 * h ^ 8 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  exact am7Vec_residual_combine hh hMnn A B C D F G J K R htri
    hA_bd hB_bd hC_bd hD_bd hF_bd hG_bd hJ_bd hK_bd hR_bd

theorem am7Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 9 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 7) * h ≤ T →
        ‖am7VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 9 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_nine_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(243 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
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
  show ‖am7VecResidual h t y‖ ≤ 243 * M * h ^ 9
  unfold am7VecResidual
  exact am7Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem hh.le

theorem am7Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 9 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (36799 / 120960 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsAM7TrajectoryVec h f t₀ yseq →
      0 ≤ ε₀ →
      ‖yseq 0 - y t₀‖ ≤ ε₀ →
      ‖yseq 1 - y (t₀ + h)‖ ≤ ε₀ →
      ‖yseq 2 - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖yseq 3 - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖yseq 4 - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖yseq 5 - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖yseq 6 - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 6) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((10 * L) * T) * ε₀ + K * h ^ 8 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am7Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((10 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => ‖yseq k - y (t₀ + (k : ℝ) * h)‖ with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (max (max
        (eN k) (eN (k + 1))) (eN (k + 2)))
        (eN (k + 3))) (eN (k + 4))) (eN (k + 5))) (eN (k + 6))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => norm_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (heN_nn k))))))
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (max (max
        (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4)) (eN 5)) (eN 6)
        ≤ ε₀
    refine max_le (max_le (max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_) ?_) ?_
    · show ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀
      simpa using he0_bd
    · show ‖yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    · show ‖yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    · show ‖yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
    · show ‖yseq 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]; simpa using he4_bd
    · show ‖yseq 5 - y (t₀ + ((5 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((5 : ℕ) : ℝ) * h = 5 * h := by push_cast; ring
      rw [hcast]; simpa using he5_bd
    · show ‖yseq 6 - y (t₀ + ((6 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((6 : ℕ) : ℝ) * h = 6 * h := by push_cast; ring
      rw [hcast]; simpa using he6_bd
  have h10L_nn : (0 : ℝ) ≤ 10 * L := by linarith
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 7) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (10 * L)) * EN n + (2 * C) * h ^ 9 := by
    intro n hnh_le
    have honestep := am7Vec_one_step_error_pair_bound
      (E := E) (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by
      push_cast; ring
    have hcast4 : ((n + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 4 := by
      push_cast; ring
    have hcast5 : ((n + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 5 := by
      push_cast; ring
    have hcast6 : ((n + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 6 := by
      push_cast; ring
    have hcast7 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) =
        (n : ℝ) + 7 := by
      push_cast; ring
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
    have heq_eN_n3 : eN (n + 1 + 1 + 1)
        = ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast3]
    have heq_eN_n4 : eN (n + 1 + 1 + 1 + 1)
        = ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast4]
    have heq_eN_n5 : eN (n + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast5]
    have heq_eN_n6 : eN (n + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast6]
    have heq_eN_n7 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast7]
    show max (max (max (max (max (max (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * (10 * L))
            * max (max (max (max (max (max (eN n) (eN (n + 1)))
                  (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1))
          + (2 * C) * h ^ 9
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5,
      heq_eN_n6, heq_eN_n7]
    have h2τ : 2 * ‖am7VecResidual h (t₀ + (n : ℝ) * h) y‖
        ≤ (2 * C) * h ^ 9 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith [this]
    linarith [honestep, h2τ]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((10 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((10 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh8_nn : 0 ≤ h ^ 8 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((10 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((10 * L) * T) * ε₀
            + T * Real.exp ((10 * L) * T) * (2 * C) * h ^ 8 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((10 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((10 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh8_nn : 0 ≤ T * Real.exp ((10 * L) * T) * (2 * C) * h ^ 8 :=
      mul_nonneg hKnn hh8_nn
    linarith
  match N, hNh with
  | 0, _ =>
    have hbase : ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      simpa using he0_bd
    exact hbase_to_headline _ hbase
  | 1, _ =>
    have hbase : ‖yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    exact hbase_to_headline _ hbase
  | 2, _ =>
    have hbase : ‖yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    exact hbase_to_headline _ hbase
  | 3, _ =>
    have hbase : ‖yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
    exact hbase_to_headline _ hbase
  | 4, _ =>
    have hbase : ‖yseq 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]; simpa using he4_bd
    exact hbase_to_headline _ hbase
  | 5, _ =>
    have hbase : ‖yseq 5 - y (t₀ + ((5 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((5 : ℕ) : ℝ) * h = 5 * h := by push_cast; ring
      rw [hcast]; simpa using he5_bd
    exact hbase_to_headline _ hbase
  | 6, _ =>
    have hbase : ‖yseq 6 - y (t₀ + ((6 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((6 : ℕ) : ℝ) * h = 6 * h := by push_cast; ring
      rw [hcast]; simpa using he6_bd
    exact hbase_to_headline _ hbase
  | N' + 7, hNh =>
    have hcast : (((N' + 7 : ℕ) : ℝ) + 6) = (N' : ℝ) + 13 := by
      push_cast; ring
    have hN_hyp : ((N' : ℝ) + 13) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (10 * L)) * EN n + (2 * C) * h ^ (8 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (8 + 1) = (2 * C) * h ^ 9 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 7 ≤ (N' : ℝ) + 13 := by linarith
      have h_mul : ((n : ℝ) + 7) * h ≤ ((N' : ℝ) + 13) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have hle : (N' : ℝ) + 1 ≤ (N' : ℝ) + 13 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 10 * L) (C := 2 * C) (T := T) (p := 8)
        (e := EN) (N := N' + 1)
        hh.le h10L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 7) ≤ EN (N' + 1) := by
      show eN (N' + 7)
        ≤ max (max (max (max (max (max
              (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4)))
              (eN (N' + 1 + 5))) (eN (N' + 1 + 6))
      have heq : N' + 7 = N' + 1 + 6 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((10 * L) * T) * EN 0 ≤ Real.exp ((10 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show ‖yseq (N' + 7) - y (t₀ + ((N' + 7 : ℕ) : ℝ) * h)‖
        ≤ Real.exp ((10 * L) * T) * ε₀
          + T * Real.exp ((10 * L) * T) * (2 * C) * h ^ 8
    have heN_eq :
        eN (N' + 7)
          = ‖yseq (N' + 7) - y (t₀ + ((N' + 7 : ℕ) : ℝ) * h)‖ := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
