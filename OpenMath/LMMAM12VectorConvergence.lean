import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAM12Convergence
import OpenMath.LMMAM11VectorConvergence

/-! ## Adams--Moulton 12-step Vector Quantitative Convergence Chain (Iserles §1.2)

Finite-dimensional vector-valued analogue of the scalar AM12 quantitative
convergence chain in `OpenMath.LMMAM12Convergence`.
-/

namespace LMM

/-! ### Fourteenth-order vector Taylor helpers -/

/-- A `C^14` vector function has its fourteenth iterated derivative bounded on
every compact interval. -/
theorem iteratedDeriv_fourteen_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 14 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 14 y t‖ ≤ M := by
  have h_cont : Continuous (iteratedDeriv 14 y) :=
    hy.continuous_iteratedDeriv 14 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

/-- Pointwise thirteenth-order vector Taylor remainder bound for the derivative. -/
theorem derivY_thirteenth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 14 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 14 y t‖ ≤ M)
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
        - (r ^ 11 / 39916800) • iteratedDeriv 12 y t
        - (r ^ 12 / 479001600) • iteratedDeriv 13 y t‖
      ≤ M / 6227020800 * r ^ 13 := by
  have hdy : ContDiff ℝ 13 (deriv y) := hy.deriv'
  have hbnd_d :
      ∀ s ∈ Set.Icc a b, ‖iteratedDeriv 13 (deriv y) s‖ ≤ M := by
    intro s hs
    have hidd_eq : iteratedDeriv 13 (deriv y) = iteratedDeriv 14 y := by
      have : iteratedDeriv 14 y = iteratedDeriv 13 (deriv y) :=
        iteratedDeriv_succ' (n := 13) (f := y)
      exact this.symm
    simpa [hidd_eq] using hbnd s hs
  have hrem := y_thirteenth_order_taylor_remainder_vec hdy hbnd_d ht htr hr
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
  have hiter10 : iteratedDeriv 10 (deriv y) t = iteratedDeriv 11 y t := by
    have : iteratedDeriv 11 y = iteratedDeriv 10 (deriv y) :=
      iteratedDeriv_succ' (n := 10) (f := y)
    rw [this]
  have hiter11 : iteratedDeriv 11 (deriv y) t = iteratedDeriv 12 y t := by
    have : iteratedDeriv 12 y = iteratedDeriv 11 (deriv y) :=
      iteratedDeriv_succ' (n := 11) (f := y)
    rw [this]
  have hiter12 : iteratedDeriv 12 (deriv y) t = iteratedDeriv 13 y t := by
    have : iteratedDeriv 13 y = iteratedDeriv 12 (deriv y) :=
      iteratedDeriv_succ' (n := 12) (f := y)
    rw [this]
  simpa [hderiv2, hiter2, hiter3, hiter4, hiter5, hiter6, hiter7, hiter8,
    hiter9, hiter10, hiter11, hiter12] using hrem

/-- Pointwise fourteenth-order vector Taylor remainder bound. -/
theorem y_fourteenth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 14 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 14 y t‖ ≤ M)
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
        - (r ^ 12 / 479001600) • iteratedDeriv 12 y t
        - (r ^ 13 / 6227020800) • iteratedDeriv 13 y t‖
      ≤ M / 87178291200 * r ^ 14 := by
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
            - ((s - t) ^ 9 / 362880) • iteratedDeriv 10 y t
            - ((s - t) ^ 10 / 3628800) • iteratedDeriv 11 y t
            - ((s - t) ^ 11 / 39916800) • iteratedDeriv 12 y t
            - ((s - t) ^ 12 / 479001600) • iteratedDeriv 13 y t‖
          ≤ M / 6227020800 * (s - t) ^ 13 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have hrem :=
      derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht
        (by rw [hsplit]; exact hs_ab) hts
    rw [hsplit] at hrem
    simpa using hrem
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
  have h_decic_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 10 / 3628800) • iteratedDeriv 11 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_undec_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 11 / 39916800) • iteratedDeriv 12 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_duodec_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 12 / 479001600) • iteratedDeriv 13 y t)
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
  have h_decic_eval :
      ∫ s in t..t + r, ((s - t) ^ 10 / 3628800) • iteratedDeriv 11 y t
        = (r ^ 11 / 39916800) • iteratedDeriv 11 y t := by
    rw [intervalIntegral.integral_smul_const]
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
    have h_fun :
        (fun s : ℝ => (s - t) ^ 10 / 3628800)
          = fun s : ℝ => (1 / 3628800 : ℝ) * (s - t) ^ 10 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 10 / 3628800 = r ^ 11 / 39916800 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_undec_eval :
      ∫ s in t..t + r, ((s - t) ^ 11 / 39916800) • iteratedDeriv 12 y t
        = (r ^ 12 / 479001600) • iteratedDeriv 12 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 11 = r ^ 12 / 12 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 11
            = ∫ s in (t - t)..(t + r - t), s ^ 11 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 11) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 11 / 39916800)
          = fun s : ℝ => (1 / 39916800 : ℝ) * (s - t) ^ 11 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 11 / 39916800 = r ^ 12 / 479001600 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_duodec_eval :
      ∫ s in t..t + r, ((s - t) ^ 12 / 479001600) • iteratedDeriv 13 y t
        = (r ^ 13 / 6227020800) • iteratedDeriv 13 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 12 = r ^ 13 / 13 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 12
            = ∫ s in (t - t)..(t + r - t), s ^ 12 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 12) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 12 / 479001600)
          = fun s : ℝ => (1 / 479001600 : ℝ) * (s - t) ^ 12 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 12 / 479001600 = r ^ 13 / 6227020800 := by
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
          - (r ^ 11 / 39916800) • iteratedDeriv 11 y t
          - (r ^ 12 / 479001600) • iteratedDeriv 12 y t
          - (r ^ 13 / 6227020800) • iteratedDeriv 13 y t
        = ∫ s in t..t + r,
            (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
              - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
              - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
              - ((s - t) ^ 4 / 24) • iteratedDeriv 5 y t
              - ((s - t) ^ 5 / 120) • iteratedDeriv 6 y t
              - ((s - t) ^ 6 / 720) • iteratedDeriv 7 y t
              - ((s - t) ^ 7 / 5040) • iteratedDeriv 8 y t
              - ((s - t) ^ 8 / 40320) • iteratedDeriv 9 y t
              - ((s - t) ^ 9 / 362880) • iteratedDeriv 10 y t
              - ((s - t) ^ 10 / 3628800) • iteratedDeriv 11 y t
              - ((s - t) ^ 11 / 39916800) • iteratedDeriv 12 y t
              - ((s - t) ^ 12 / 479001600) • iteratedDeriv 13 y t) := by
    rw [intervalIntegral.integral_sub
        ((((((((((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int).sub h_quintic_int).sub
          h_sextic_int).sub h_septic_int).sub h_octic_int).sub h_nonic_int).sub
          h_decic_int).sub h_undec_int) h_duodec_int,
      intervalIntegral.integral_sub
        (((((((((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int).sub h_quintic_int).sub
          h_sextic_int).sub h_septic_int).sub h_octic_int).sub h_nonic_int).sub
          h_decic_int) h_undec_int,
      intervalIntegral.integral_sub
        ((((((((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int).sub h_quintic_int).sub
          h_sextic_int).sub h_septic_int).sub h_octic_int).sub h_nonic_int) h_decic_int,
      intervalIntegral.integral_sub
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
      h_quintic_eval, h_sextic_eval, h_septic_eval, h_octic_eval, h_nonic_eval,
      h_decic_eval, h_undec_eval, h_duodec_eval]
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
            - ((s - t) ^ 9 / 362880) • iteratedDeriv 10 y t
            - ((s - t) ^ 10 / 3628800) • iteratedDeriv 11 y t
            - ((s - t) ^ 11 / 39916800) • iteratedDeriv 12 y t
            - ((s - t) ^ 12 / 479001600) • iteratedDeriv 13 y t)‖
        ≤ ∫ s in t..t + r, M / 6227020800 * (s - t) ^ 13 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dy_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 6227020800 * (s - t) ^ 13).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 6227020800 * (s - t) ^ 13 =
        M / 87178291200 * r ^ 14 := by
    have h_inner : ∫ s in t..t + r, (s - t) ^ 13 = r ^ 14 / 14 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 13
            = ∫ s in (t - t)..(t + r - t), s ^ 13 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 13) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

/-! ### AM12 vector trajectory predicate and one-step infrastructure -/

/-- AM12 coefficient table, exposed under a vector-specific name. -/
noncomputable def am12VecCoeff : Fin 13 → ℝ := am12Coeff

/-- The twelve already-known AM12 coefficients, excluding the implicit new point. -/
noncomputable def am12VecExplicitCoeff (j : Fin 12) : ℝ :=
  am12VecCoeff ⟨j, by omega⟩

/-- Textbook AM12 vector residual. -/
noncomputable def am12VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 12 * h) - y (t + 11 * h)
    - h • ∑ j : Fin 13,
        (am12VecCoeff j) • deriv y (t + (j : ℕ) * h)

/-- AM12 vector trajectory predicate.  The new value appears inside `f`, so
existence of such a trajectory is a separate fixed-point problem. -/
structure IsAM12TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 12)
      = y (n + 11)
        + h • ∑ j : Fin 13,
            (am12VecCoeff j) • f (t₀ + (n : ℝ) * h + (j : ℕ) * h)
              (y (n + (j : ℕ)))

/-- Vector pointwise error at an index. -/
noncomputable def am12VecErr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t₀ : ℝ) (yseq : ℕ → E) (y : ℝ → E) (k : ℕ) : ℝ :=
  ‖yseq k - y (t₀ + (k : ℝ) * h)‖

/-- Rolling AM12 vector twelve-sample window max. -/
noncomputable def am12VecErrWindow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t₀ : ℝ) (yseq : ℕ → E) (y : ℝ → E) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin 12 => am12VecErr h t₀ yseq y (k + (j : ℕ)))

lemma am12VecErrWindow_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t₀ : ℝ) (yseq : ℕ → E) (y : ℝ → E) (k : ℕ) :
    0 ≤ am12VecErrWindow h t₀ yseq y k := by
  unfold am12VecErrWindow
  exact (norm_nonneg _).trans
    (Finset.le_sup' (b := (0 : Fin 12))
      (f := fun j : Fin 12 => am12VecErr h t₀ yseq y (k + (j : ℕ)))
      (Finset.mem_univ _))

/-- AM12 vector residual unfolds to the textbook local truncation expression. -/
theorem am12Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am12VecResidual h t y
      = y (t + 12 * h) - y (t + 11 * h)
          - h • ∑ j : Fin 13,
              (am12VecCoeff j) • deriv y (t + (j : ℕ) * h) := by
  rfl

theorem am12Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (_hL : 0 ≤ L)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM12TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
        * am12VecErr h t₀ yseq y (n + 12)
      ≤ am12VecErr h t₀ yseq y (n + 11)
        + h * L * ∑ j : Fin 12,
            |am12VecExplicitCoeff j| * am12VecErr h t₀ yseq y (n + (j : ℕ))
        + ‖am12VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  set τ : E := am12VecResidual h t y with hτ_def
  set Sa : E := ∑ j : Fin 13,
      (am12VecCoeff j) • f (t + (j : ℕ) * h) (yseq (n + (j : ℕ))) with hSa_def
  set Sy : E := ∑ j : Fin 13,
      (am12VecCoeff j) • f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)) with hSy_def
  have hstep : yseq (n + 12) = yseq (n + 11) + h • Sa := by
    simpa [hSa_def, ht_def, add_assoc] using hy.recurrence n
  have hτ_alt : τ = y (t + 12 * h) - y (t + 11 * h) - h • Sy := by
    show am12VecResidual h t y = _
    unfold am12VecResidual
    have hcong :
        (fun j : Fin 13 => (am12VecCoeff j) • deriv y (t + (j : ℕ) * h))
          = (fun j : Fin 13 =>
              (am12VecCoeff j) • f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))) := by
      funext j
      rw [hyf]
    rw [hcong, hSy_def]
  set Sd : E := ∑ j : Fin 13,
      (am12VecCoeff j) •
        (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
          - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))) with hSd_def
  have hSa_sub_Sy : Sa - Sy = Sd := by
    rw [hSa_def, hSy_def, hSd_def, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_sub]
  have halg :
      yseq (n + 12) - y (t + 12 * h)
        = (yseq (n + 11) - y (t + 11 * h)) + h • Sd - τ := by
    rw [hstep, hτ_alt, ← hSa_sub_Sy]
    module
  have hdiff_bound : ∀ j : Fin 13,
      ‖(am12VecCoeff j) •
          (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))‖
        ≤ |am12VecCoeff j| * L
            * ‖yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)‖ := by
    intro j
    have hLip := hf (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
      (y (t + (j : ℕ) * h))
    rw [norm_smul, Real.norm_eq_abs]
    have hcoeff_nn : 0 ≤ |am12VecCoeff j| := abs_nonneg _
    calc
      |am12VecCoeff j| *
          ‖f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))‖
          ≤ |am12VecCoeff j| *
              (L * ‖yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)‖) :=
            mul_le_mul_of_nonneg_left hLip hcoeff_nn
      _ = |am12VecCoeff j| * L
            * ‖yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)‖ := by ring
  have hSd_norm :
      ‖Sd‖ ≤ ∑ j : Fin 13, |am12VecCoeff j| * L
            * ‖yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)‖ := by
    rw [hSd_def]
    calc
      ‖∑ j : Fin 13, (am12VecCoeff j) •
          (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))‖
          ≤ ∑ j : Fin 13,
              ‖(am12VecCoeff j) •
                (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
                  - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))‖ :=
            norm_sum_le _ _
      _ ≤ ∑ j : Fin 13, |am12VecCoeff j| * L
            * ‖yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)‖ :=
            Finset.sum_le_sum (fun j _ => hdiff_bound j)
  have htri :
      ‖yseq (n + 12) - y (t + 12 * h)‖
        ≤ ‖yseq (n + 11) - y (t + 11 * h)‖ + ‖h • Sd‖ + ‖τ‖ := by
    rw [halg]
    have h1 :
        ‖(yseq (n + 11) - y (t + 11 * h)) + h • Sd - τ‖
          ≤ ‖(yseq (n + 11) - y (t + 11 * h)) + h • Sd‖ + ‖τ‖ :=
      norm_sub_le _ _
    have h2 :
        ‖(yseq (n + 11) - y (t + 11 * h)) + h • Sd‖
          ≤ ‖yseq (n + 11) - y (t + 11 * h)‖ + ‖h • Sd‖ :=
      norm_add_le _ _
    linarith
  have h_hSd :
      ‖h • Sd‖ ≤ h * ∑ j : Fin 13, |am12VecCoeff j| * L
            * ‖yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hSd_norm hh
  have hmain_local :
      ‖yseq (n + 12) - y (t + 12 * h)‖
        ≤ ‖yseq (n + 11) - y (t + 11 * h)‖
          + h * ∑ j : Fin 13, |am12VecCoeff j| * L
            * ‖yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)‖
          + ‖τ‖ := by
    linarith
  have hsplit :
      h * ∑ j : Fin 13, |am12VecCoeff j| * L
            * ‖yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)‖
        = h * L * ∑ j : Fin 12,
            |am12VecExplicitCoeff j| * am12VecErr h t₀ yseq y (n + (j : ℕ))
          + (703604254357 / 2615348736000 : ℝ) * h * L
              * am12VecErr h t₀ yseq y (n + 12) := by
    simp [am12VecCoeff, am12VecExplicitCoeff, am12Coeff, am12VecErr,
      Fin.sum_univ_succ, ht_def]
    ring_nf
  have hmain :
      am12VecErr h t₀ yseq y (n + 12)
        ≤ am12VecErr h t₀ yseq y (n + 11)
          + h * L * ∑ j : Fin 12,
            |am12VecExplicitCoeff j| * am12VecErr h t₀ yseq y (n + (j : ℕ))
          + (703604254357 / 2615348736000 : ℝ) * h * L
              * am12VecErr h t₀ yseq y (n + 12)
          + ‖am12VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
    have hmain_local' := hmain_local
    rw [hsplit] at hmain_local'
    simpa [am12VecErr, ht_def, Nat.cast_add, add_mul, add_assoc, add_left_comm,
      add_comm, hτ_def] using hmain_local'
  linarith [hmain]

theorem am12Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (703604254357 / 2615348736000 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM12TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    am12VecErr h t₀ yseq y (n + 12)
      ≤ (1 + h * (104 * L)) * am12VecErrWindow h t₀ yseq y n
        + 2 * ‖am12VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set Emax : ℝ := am12VecErrWindow h t₀ yseq y n with hE_def
  set τabs : ℝ :=
    ‖am12VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  have hE_nn : 0 ≤ Emax := by
    simpa [hE_def] using am12VecErrWindow_nonneg h t₀ yseq y n
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 1307674368000 / 703604254357 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (703604254357 / 2615348736000 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hwin : ∀ j : Fin 12,
      am12VecErr h t₀ yseq y (n + (j : ℕ)) ≤ Emax := by
    intro j
    show am12VecErr h t₀ yseq y (n + (j : ℕ))
        ≤ am12VecErrWindow h t₀ yseq y n
    unfold am12VecErrWindow
    exact Finset.le_sup' (b := j)
      (f := fun k : Fin 12 => am12VecErr h t₀ yseq y (n + (k : ℕ)))
      (Finset.mem_univ _)
  have he_last_le_E : am12VecErr h t₀ yseq y (n + 11) ≤ Emax :=
    hwin ⟨11, by norm_num⟩
  have hsum_le :
      ∑ j : Fin 12, |am12VecExplicitCoeff j| * am12VecErr h t₀ yseq y (n + (j : ℕ))
        ≤ (32759306603 / 638668800 : ℝ) * Emax := by
    calc
      ∑ j : Fin 12, |am12VecExplicitCoeff j| * am12VecErr h t₀ yseq y (n + (j : ℕ))
          ≤ ∑ j : Fin 12, |am12VecExplicitCoeff j| * Emax :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (hwin j) (abs_nonneg _))
      _ = (32759306603 / 638668800 : ℝ) * Emax := by
        simp [am12VecExplicitCoeff, am12VecCoeff, am12Coeff, Fin.sum_univ_succ]
        ring
  have hstep :=
    am12Vec_one_step_lipschitz (E := E) (h := h) (L := L) hh hL hf t₀ hy y hyf n
  have hR_le :
      am12VecErr h t₀ yseq y (n + 11)
        + h * L * ∑ j : Fin 12,
            |am12VecExplicitCoeff j| * am12VecErr h t₀ yseq y (n + (j : ℕ))
        + τabs
        ≤ (1 + (32759306603 / 638668800 : ℝ) * (h * L)) * Emax + τabs := by
    have hsum_scaled :
        h * L * ∑ j : Fin 12,
            |am12VecExplicitCoeff j| * am12VecErr h t₀ yseq y (n + (j : ℕ))
          ≤ h * L * ((32759306603 / 638668800 : ℝ) * Emax) :=
      mul_le_mul_of_nonneg_left hsum_le hx_nn
    have h_alg :
        Emax + h * L * ((32759306603 / 638668800 : ℝ) * Emax) + τabs
          = (1 + (32759306603 / 638668800 : ℝ) * (h * L)) * Emax + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (32759306603 / 638668800 : ℝ) * (h * L)
        ≤ (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
            * (1 + h * (104 * L)) := by
    have hxL_eq :
        (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
            * (1 + h * (104 * L))
          - (1 + (32759306603 / 638668800 : ℝ) * (h * L))
          = (h * L) / 2615348736000 * (137143303750358 - 73174842453128 * (h * L)) := by
      ring
    have hpos : 0 ≤ 137143303750358 - 73174842453128 * (h * L) := by
      have hbound :
          73174842453128 * (h * L)
            ≤ 73174842453128 * (1307674368000 / 703604254357 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hx_small (by norm_num)
      have hnum :
          (73174842453128 : ℝ) * (1307674368000 / 703604254357) ≤
            137143303750358 := by
        norm_num
      exact sub_nonneg.mpr (le_trans hbound hnum)
    have hprod : 0 ≤ (h * L) / 2615348736000 *
        (137143303750358 - 73174842453128 * (h * L)) := by
      exact mul_nonneg (by positivity) hpos
    apply sub_nonneg.mp
    rw [hxL_eq]
    exact hprod
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (703604254357 / 2615348736000 : ℝ) * h * L) * 2 := by
    set x : ℝ := (703604254357 / 2615348736000 : ℝ) * h * L with hx_def
    change (1 : ℝ) ≤ (1 - x) * 2
    have hxle : x ≤ 1 / 2 := by simpa [hx_def] using hsmall
    nlinarith
  have hE_part :
      (1 + (32759306603 / 638668800 : ℝ) * (h * L)) * Emax
        ≤ ((1 - (703604254357 / 2615348736000 : ℝ) * h * L)
            * (1 + h * (104 * L))) * Emax :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (703604254357 / 2615348736000 : ℝ) * h * L) * 2) * τabs := by
    have hraw := mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
    calc
      τabs = (1 : ℝ) * τabs := by ring
      _ ≤ ((1 - (703604254357 / 2615348736000 : ℝ) * h * L) * 2) * τabs := hraw
  have hfactor :
      (1 + (32759306603 / 638668800 : ℝ) * (h * L)) * Emax + τabs
        ≤ (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
            * ((1 + h * (104 * L)) * Emax + 2 * τabs) := by
    let A : ℝ := 1 - (703604254357 / 2615348736000 : ℝ) * h * L
    let B : ℝ := 1 + h * (104 * L)
    let Cg : ℝ := 1 + (32759306603 / 638668800 : ℝ) * (h * L)
    change Cg * Emax + τabs ≤ A * (B * Emax + 2 * τabs)
    have hE_part' : Cg * Emax ≤ (A * B) * Emax := hE_part
    have hτ_part' : τabs ≤ (A * 2) * τabs := hτ_part
    calc
      Cg * Emax + τabs ≤ (A * B) * Emax + (A * 2) * τabs :=
        add_le_add hE_part' hτ_part'
      _ = A * (B * Emax + 2 * τabs) := by ring
  have hprod :
      (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
          * am12VecErr h t₀ yseq y (n + 12)
        ≤ (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
            * ((1 + h * (104 * L)) * Emax + 2 * τabs) :=
    le_trans hstep (le_trans (by simpa [hτabs_def] using hR_le) hfactor)
  have hcancel :
      am12VecErr h t₀ yseq y (n + 12)
        ≤ (1 + h * (104 * L)) * Emax + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  simpa [hE_def, hτabs_def] using hcancel

theorem am12Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (703604254357 / 2615348736000 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM12TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    am12VecErrWindow h t₀ yseq y (n + 1)
      ≤ (1 + h * (104 * L)) * am12VecErrWindow h t₀ yseq y n
        + 2 * ‖am12VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set Emax : ℝ := am12VecErrWindow h t₀ yseq y n with hE_def
  set τabs : ℝ :=
    ‖am12VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set R : ℝ := (1 + h * (104 * L)) * Emax + 2 * τabs with hR_def
  have hE_nn : 0 ≤ Emax := by
    simpa [hE_def] using am12VecErrWindow_nonneg h t₀ yseq y n
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hGhL_nn : 0 ≤ h * (104 * L) := by positivity
  have hE_le_R : Emax ≤ R := by
    have hcoef : (1 : ℝ) ≤ 1 + h * (104 * L) :=
      le_add_of_nonneg_right hGhL_nn
    have hgrow : Emax ≤ (1 + h * (104 * L)) * Emax := by
      have := mul_le_mul_of_nonneg_right hcoef hE_nn
      simpa using this
    have hplus :
        (1 + h * (104 * L)) * Emax ≤ R := by
      rw [hR_def]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hτ_nn)
    exact le_trans hgrow hplus
  have hwin : ∀ j : Fin 12,
      am12VecErr h t₀ yseq y (n + (j : ℕ)) ≤ Emax := by
    intro j
    show am12VecErr h t₀ yseq y (n + (j : ℕ))
        ≤ am12VecErrWindow h t₀ yseq y n
    unfold am12VecErrWindow
    exact Finset.le_sup' (b := j)
      (f := fun k : Fin 12 => am12VecErr h t₀ yseq y (n + (k : ℕ)))
      (Finset.mem_univ _)
  have hnew :
      am12VecErr h t₀ yseq y (n + 12) ≤ R := by
    simpa [hE_def, hτabs_def, hR_def] using
      (am12Vec_one_step_error_bound (E := E) (h := h) (L := L) hh hL hsmall hf t₀ hy y hyf n)
  have h_per : ∀ j : Fin 12,
      am12VecErr h t₀ yseq y (n + 1 + (j : ℕ)) ≤ R := by
    intro j
    by_cases hj : (j : ℕ) + 1 < 12
    · have hprev := hwin ⟨(j : ℕ) + 1, hj⟩
      have hidx : n + 1 + (j : ℕ) = n + ((j : ℕ) + 1) := by omega
      rw [hidx]
      exact le_trans hprev hE_le_R
    · have hjeq : (j : ℕ) = 11 := by omega
      have hidx : n + 1 + (j : ℕ) = n + 12 := by omega
      rw [hidx]
      exact hnew
  unfold am12VecErrWindow
  exact Finset.sup'_le _ _ (fun j _ => by
    simpa [hE_def, hτabs_def, hR_def] using h_per j)

/-! ### Packed-polynomial AM12 vector residual algebra -/

private noncomputable def am12Vec_yPoly13
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m h : ℝ) (d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t : E) : E :=
  (m * h) • d0
    + ((m * h) ^ 2 / 2) • d2t
    + ((m * h) ^ 3 / 6) • d3t
    + ((m * h) ^ 4 / 24) • d4t
    + ((m * h) ^ 5 / 120) • d5t
    + ((m * h) ^ 6 / 720) • d6t
    + ((m * h) ^ 7 / 5040) • d7t
    + ((m * h) ^ 8 / 40320) • d8t
    + ((m * h) ^ 9 / 362880) • d9t
    + ((m * h) ^ 10 / 3628800) • d10t
    + ((m * h) ^ 11 / 39916800) • d11t
    + ((m * h) ^ 12 / 479001600) • d12t
    + ((m * h) ^ 13 / 6227020800) • d13t

private noncomputable def am12Vec_dPoly12
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m h : ℝ) (d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t : E) : E :=
  (m * h) • d2t
    + ((m * h) ^ 2 / 2) • d3t
    + ((m * h) ^ 3 / 6) • d4t
    + ((m * h) ^ 4 / 24) • d5t
    + ((m * h) ^ 5 / 120) • d6t
    + ((m * h) ^ 6 / 720) • d7t
    + ((m * h) ^ 7 / 5040) • d8t
    + ((m * h) ^ 8 / 40320) • d9t
    + ((m * h) ^ 9 / 362880) • d10t
    + ((m * h) ^ 10 / 3628800) • d11t
    + ((m * h) ^ 11 / 39916800) • d12t
    + ((m * h) ^ 12 / 479001600) • d13t

private lemma am12Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12
      d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t : E) (h : ℝ)
    (A B C D F G H I J K P Q R S : E)
    (hA : A = y12 - y0 - am12Vec_yPoly13 12 h d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hB : B = y11 - y0 - am12Vec_yPoly13 11 h d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hC : C = d12 - d0 - am12Vec_dPoly12 12 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hD : D = d11 - d0 - am12Vec_dPoly12 11 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hF : F = d10 - d0 - am12Vec_dPoly12 10 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hG : G = d9 - d0 - am12Vec_dPoly12 9 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hH : H = d8 - d0 - am12Vec_dPoly12 8 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hI : I = d7 - d0 - am12Vec_dPoly12 7 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hJ : J = d6 - d0 - am12Vec_dPoly12 6 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hK : K = d5 - d0 - am12Vec_dPoly12 5 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hP : P = d4 - d0 - am12Vec_dPoly12 4 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hQ : Q = d3 - d0 - am12Vec_dPoly12 3 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hR : R = d2 - d0 - am12Vec_dPoly12 2 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hS : S = d1 - d0 - am12Vec_dPoly12 1 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t) :
    y12 - y11 - h • ((703604254357 / 2615348736000 : ℝ) • d12
                  + (3917551216986 / 2615348736000 : ℝ) • d11
                  - (6616420957428 / 2615348736000 : ℝ) • d10
                  + (13465774256510 / 2615348736000 : ℝ) • d9
                  - (21847538039895 / 2615348736000 : ℝ) • d8
                  + (27345870698436 / 2615348736000 : ℝ) • d7
                  - (26204344465152 / 2615348736000 : ℝ) • d6
                  + (19058185652796 / 2615348736000 : ℝ) • d5
                  - (10344711794985 / 2615348736000 : ℝ) • d4
                  + (4063327863170 / 2615348736000 : ℝ) • d3
                  - (1092096992268 / 2615348736000 : ℝ) • d2
                  + (179842822566 / 2615348736000 : ℝ) • d1
                  - (13695779093 / 2615348736000 : ℝ) • d0)
      = A - B
        - (703604254357 * h / 2615348736000 : ℝ) • C
        - (3917551216986 * h / 2615348736000 : ℝ) • D
        + (6616420957428 * h / 2615348736000 : ℝ) • F
        - (13465774256510 * h / 2615348736000 : ℝ) • G
        + (21847538039895 * h / 2615348736000 : ℝ) • H
        - (27345870698436 * h / 2615348736000 : ℝ) • I
        + (26204344465152 * h / 2615348736000 : ℝ) • J
        - (19058185652796 * h / 2615348736000 : ℝ) • K
        + (10344711794985 * h / 2615348736000 : ℝ) • P
        - (4063327863170 * h / 2615348736000 : ℝ) • Q
        + (1092096992268 * h / 2615348736000 : ℝ) • R
        - (179842822566 * h / 2615348736000 : ℝ) • S := by
  simp +decide only [hA, am12Vec_yPoly13, hB, hC, am12Vec_dPoly12, hD, hF,
    hG, hH, hI, hJ, hK, hP, hQ, hR, hS]
  module

private lemma am12Vec_residual_bound_alg_identity (Mb h : ℝ) :
    Mb / 87178291200 * (12 * h) ^ 14
      + Mb / 87178291200 * (11 * h) ^ 14
      + (703604254357 * h / 2615348736000) * (Mb / 6227020800 * (12 * h) ^ 13)
      + (3917551216986 * h / 2615348736000) * (Mb / 6227020800 * (11 * h) ^ 13)
      + (6616420957428 * h / 2615348736000) * (Mb / 6227020800 * (10 * h) ^ 13)
      + (13465774256510 * h / 2615348736000) * (Mb / 6227020800 * (9 * h) ^ 13)
      + (21847538039895 * h / 2615348736000) * (Mb / 6227020800 * (8 * h) ^ 13)
      + (27345870698436 * h / 2615348736000) * (Mb / 6227020800 * (7 * h) ^ 13)
      + (26204344465152 * h / 2615348736000) * (Mb / 6227020800 * (6 * h) ^ 13)
      + (19058185652796 * h / 2615348736000) * (Mb / 6227020800 * (5 * h) ^ 13)
      + (10344711794985 * h / 2615348736000) * (Mb / 6227020800 * (4 * h) ^ 13)
      + (4063327863170 * h / 2615348736000) * (Mb / 6227020800 * (3 * h) ^ 13)
      + (1092096992268 * h / 2615348736000) * (Mb / 6227020800 * (2 * h) ^ 13)
      + (179842822566 * h / 2615348736000) * (Mb / 6227020800 * h ^ 13)
      = (414541158076267641095141 / 10602754543180800000 : ℝ) * Mb * h ^ 14 := by
  ring

private lemma am12Vec_triangle_aux
    {E : Type*} [NormedAddCommGroup E]
    (A B C D F G H I J K P Q R S : E) :
    ‖A - B - C - D + F - G + H - I + J - K + P - Q + R - S‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖F‖ + ‖G‖ + ‖H‖ + ‖I‖
          + ‖J‖ + ‖K‖ + ‖P‖ + ‖Q‖ + ‖R‖ + ‖S‖ := by
  have h1 : ‖A - B - C - D + F - G + H - I + J - K + P - Q + R - S‖
      ≤ ‖A - B - C - D + F - G + H - I + J - K + P - Q + R‖ + ‖S‖ :=
    norm_sub_le _ _
  have h2 : ‖A - B - C - D + F - G + H - I + J - K + P - Q + R‖
      ≤ ‖A - B - C - D + F - G + H - I + J - K + P - Q‖ + ‖R‖ :=
    norm_add_le _ _
  have h3 : ‖A - B - C - D + F - G + H - I + J - K + P - Q‖
      ≤ ‖A - B - C - D + F - G + H - I + J - K + P‖ + ‖Q‖ :=
    norm_sub_le _ _
  have h4 : ‖A - B - C - D + F - G + H - I + J - K + P‖
      ≤ ‖A - B - C - D + F - G + H - I + J - K‖ + ‖P‖ :=
    norm_add_le _ _
  have h5 : ‖A - B - C - D + F - G + H - I + J - K‖
      ≤ ‖A - B - C - D + F - G + H - I + J‖ + ‖K‖ :=
    norm_sub_le _ _
  have h6 : ‖A - B - C - D + F - G + H - I + J‖
      ≤ ‖A - B - C - D + F - G + H - I‖ + ‖J‖ :=
    norm_add_le _ _
  have h7 : ‖A - B - C - D + F - G + H - I‖
      ≤ ‖A - B - C - D + F - G + H‖ + ‖I‖ :=
    norm_sub_le _ _
  have h8 : ‖A - B - C - D + F - G + H‖
      ≤ ‖A - B - C - D + F - G‖ + ‖H‖ :=
    norm_add_le _ _
  have h9 : ‖A - B - C - D + F - G‖
      ≤ ‖A - B - C - D + F‖ + ‖G‖ := norm_sub_le _ _
  have h10 : ‖A - B - C - D + F‖
      ≤ ‖A - B - C - D‖ + ‖F‖ := norm_add_le _ _
  have h11 : ‖A - B - C - D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_sub_le _ _
  have h12 : ‖A - B - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le _ _
  have h13 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith

private lemma am12Vec_residual_fourteen_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G H I J K P Q R S : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (703604254357 * h / 2615348736000 : ℝ) • C
        - (3917551216986 * h / 2615348736000 : ℝ) • D
        + (6616420957428 * h / 2615348736000 : ℝ) • F
        - (13465774256510 * h / 2615348736000 : ℝ) • G
        + (21847538039895 * h / 2615348736000 : ℝ) • H
        - (27345870698436 * h / 2615348736000 : ℝ) • I
        + (26204344465152 * h / 2615348736000 : ℝ) • J
        - (19058185652796 * h / 2615348736000 : ℝ) • K
        + (10344711794985 * h / 2615348736000 : ℝ) • P
        - (4063327863170 * h / 2615348736000 : ℝ) • Q
        + (1092096992268 * h / 2615348736000 : ℝ) • R
        - (179842822566 * h / 2615348736000 : ℝ) • S‖
      ≤ ‖A‖ + ‖B‖ + (703604254357 * h / 2615348736000) * ‖C‖
          + (3917551216986 * h / 2615348736000) * ‖D‖
          + (6616420957428 * h / 2615348736000) * ‖F‖
          + (13465774256510 * h / 2615348736000) * ‖G‖
          + (21847538039895 * h / 2615348736000) * ‖H‖
          + (27345870698436 * h / 2615348736000) * ‖I‖
          + (26204344465152 * h / 2615348736000) * ‖J‖
          + (19058185652796 * h / 2615348736000) * ‖K‖
          + (10344711794985 * h / 2615348736000) * ‖P‖
          + (4063327863170 * h / 2615348736000) * ‖Q‖
          + (1092096992268 * h / 2615348736000) * ‖R‖
          + (179842822566 * h / 2615348736000) * ‖S‖ := by
  have hcC_nn : 0 ≤ (703604254357 * h / 2615348736000 : ℝ) := by positivity
  have hcD_nn : 0 ≤ (3917551216986 * h / 2615348736000 : ℝ) := by positivity
  have hcF_nn : 0 ≤ (6616420957428 * h / 2615348736000 : ℝ) := by positivity
  have hcG_nn : 0 ≤ (13465774256510 * h / 2615348736000 : ℝ) := by positivity
  have hcH_nn : 0 ≤ (21847538039895 * h / 2615348736000 : ℝ) := by positivity
  have hcI_nn : 0 ≤ (27345870698436 * h / 2615348736000 : ℝ) := by positivity
  have hcJ_nn : 0 ≤ (26204344465152 * h / 2615348736000 : ℝ) := by positivity
  have hcK_nn : 0 ≤ (19058185652796 * h / 2615348736000 : ℝ) := by positivity
  have hcP_nn : 0 ≤ (10344711794985 * h / 2615348736000 : ℝ) := by positivity
  have hcQ_nn : 0 ≤ (4063327863170 * h / 2615348736000 : ℝ) := by positivity
  have hcR_nn : 0 ≤ (1092096992268 * h / 2615348736000 : ℝ) := by positivity
  have hcS_nn : 0 ≤ (179842822566 * h / 2615348736000 : ℝ) := by positivity
  have hC_norm :
      ‖(703604254357 * h / 2615348736000 : ℝ) • C‖
        = (703604254357 * h / 2615348736000) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcC_nn]
  have hD_norm :
      ‖(3917551216986 * h / 2615348736000 : ℝ) • D‖
        = (3917551216986 * h / 2615348736000) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcD_nn]
  have hF_norm :
      ‖(6616420957428 * h / 2615348736000 : ℝ) • F‖
        = (6616420957428 * h / 2615348736000) * ‖F‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcF_nn]
  have hG_norm :
      ‖(13465774256510 * h / 2615348736000 : ℝ) • G‖
        = (13465774256510 * h / 2615348736000) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcG_nn]
  have hH_norm :
      ‖(21847538039895 * h / 2615348736000 : ℝ) • H‖
        = (21847538039895 * h / 2615348736000) * ‖H‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcH_nn]
  have hI_norm :
      ‖(27345870698436 * h / 2615348736000 : ℝ) • I‖
        = (27345870698436 * h / 2615348736000) * ‖I‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcI_nn]
  have hJ_norm :
      ‖(26204344465152 * h / 2615348736000 : ℝ) • J‖
        = (26204344465152 * h / 2615348736000) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcJ_nn]
  have hK_norm :
      ‖(19058185652796 * h / 2615348736000 : ℝ) • K‖
        = (19058185652796 * h / 2615348736000) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcK_nn]
  have hP_norm :
      ‖(10344711794985 * h / 2615348736000 : ℝ) • P‖
        = (10344711794985 * h / 2615348736000) * ‖P‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcP_nn]
  have hQ_norm :
      ‖(4063327863170 * h / 2615348736000 : ℝ) • Q‖
        = (4063327863170 * h / 2615348736000) * ‖Q‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcQ_nn]
  have hR_norm :
      ‖(1092096992268 * h / 2615348736000 : ℝ) • R‖
        = (1092096992268 * h / 2615348736000) * ‖R‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcR_nn]
  have hS_norm :
      ‖(179842822566 * h / 2615348736000 : ℝ) • S‖
        = (179842822566 * h / 2615348736000) * ‖S‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcS_nn]
  have htri := am12Vec_triangle_aux A B
    ((703604254357 * h / 2615348736000 : ℝ) • C)
    ((3917551216986 * h / 2615348736000 : ℝ) • D)
    ((6616420957428 * h / 2615348736000 : ℝ) • F)
    ((13465774256510 * h / 2615348736000 : ℝ) • G)
    ((21847538039895 * h / 2615348736000 : ℝ) • H)
    ((27345870698436 * h / 2615348736000 : ℝ) • I)
    ((26204344465152 * h / 2615348736000 : ℝ) • J)
    ((19058185652796 * h / 2615348736000 : ℝ) • K)
    ((10344711794985 * h / 2615348736000 : ℝ) • P)
    ((4063327863170 * h / 2615348736000 : ℝ) • Q)
    ((1092096992268 * h / 2615348736000 : ℝ) • R)
    ((179842822566 * h / 2615348736000 : ℝ) • S)
  rw [hC_norm, hD_norm, hF_norm, hG_norm, hH_norm, hI_norm, hJ_norm, hK_norm,
    hP_norm, hQ_norm, hR_norm, hS_norm] at htri
  exact htri

private lemma am12Vec_residual_combine_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G H I J K P Q R S : E) {Mb h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ Mb)
    (hA_bd : ‖A‖ ≤ Mb / 87178291200 * (12 * h) ^ 14)
    (hB_bd : ‖B‖ ≤ Mb / 87178291200 * (11 * h) ^ 14)
    (hC_bd : ‖C‖ ≤ Mb / 6227020800 * (12 * h) ^ 13)
    (hD_bd : ‖D‖ ≤ Mb / 6227020800 * (11 * h) ^ 13)
    (hF_bd : ‖F‖ ≤ Mb / 6227020800 * (10 * h) ^ 13)
    (hG_bd : ‖G‖ ≤ Mb / 6227020800 * (9 * h) ^ 13)
    (hH_bd : ‖H‖ ≤ Mb / 6227020800 * (8 * h) ^ 13)
    (hI_bd : ‖I‖ ≤ Mb / 6227020800 * (7 * h) ^ 13)
    (hJ_bd : ‖J‖ ≤ Mb / 6227020800 * (6 * h) ^ 13)
    (hK_bd : ‖K‖ ≤ Mb / 6227020800 * (5 * h) ^ 13)
    (hP_bd : ‖P‖ ≤ Mb / 6227020800 * (4 * h) ^ 13)
    (hQ_bd : ‖Q‖ ≤ Mb / 6227020800 * (3 * h) ^ 13)
    (hR_bd : ‖R‖ ≤ Mb / 6227020800 * (2 * h) ^ 13)
    (hS_bd : ‖S‖ ≤ Mb / 6227020800 * h ^ 13) :
    ‖A - B - (703604254357 * h / 2615348736000 : ℝ) • C
        - (3917551216986 * h / 2615348736000 : ℝ) • D
        + (6616420957428 * h / 2615348736000 : ℝ) • F
        - (13465774256510 * h / 2615348736000 : ℝ) • G
        + (21847538039895 * h / 2615348736000 : ℝ) • H
        - (27345870698436 * h / 2615348736000 : ℝ) • I
        + (26204344465152 * h / 2615348736000 : ℝ) • J
        - (19058185652796 * h / 2615348736000 : ℝ) • K
        + (10344711794985 * h / 2615348736000 : ℝ) • P
        - (4063327863170 * h / 2615348736000 : ℝ) • Q
        + (1092096992268 * h / 2615348736000 : ℝ) • R
        - (179842822566 * h / 2615348736000 : ℝ) • S‖
      ≤ (39099 : ℝ) * Mb * h ^ 14 := by
  have htri := am12Vec_residual_fourteen_term_triangle A B C D F G H I J K P Q R S h hh
  have hcC_nn : 0 ≤ 703604254357 * h / 2615348736000 := by positivity
  have hcD_nn : 0 ≤ 3917551216986 * h / 2615348736000 := by positivity
  have hcF_nn : 0 ≤ 6616420957428 * h / 2615348736000 := by positivity
  have hcG_nn : 0 ≤ 13465774256510 * h / 2615348736000 := by positivity
  have hcH_nn : 0 ≤ 21847538039895 * h / 2615348736000 := by positivity
  have hcI_nn : 0 ≤ 27345870698436 * h / 2615348736000 := by positivity
  have hcJ_nn : 0 ≤ 26204344465152 * h / 2615348736000 := by positivity
  have hcK_nn : 0 ≤ 19058185652796 * h / 2615348736000 := by positivity
  have hcP_nn : 0 ≤ 10344711794985 * h / 2615348736000 := by positivity
  have hcQ_nn : 0 ≤ 4063327863170 * h / 2615348736000 := by positivity
  have hcR_nn : 0 ≤ 1092096992268 * h / 2615348736000 := by positivity
  have hcS_nn : 0 ≤ 179842822566 * h / 2615348736000 := by positivity
  have hCbd_s : (703604254357 * h / 2615348736000) * ‖C‖
      ≤ (703604254357 * h / 2615348736000) * (Mb / 6227020800 * (12 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hC_bd hcC_nn
  have hDbd_s : (3917551216986 * h / 2615348736000) * ‖D‖
      ≤ (3917551216986 * h / 2615348736000) * (Mb / 6227020800 * (11 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hD_bd hcD_nn
  have hFbd_s : (6616420957428 * h / 2615348736000) * ‖F‖
      ≤ (6616420957428 * h / 2615348736000) * (Mb / 6227020800 * (10 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hF_bd hcF_nn
  have hGbd_s : (13465774256510 * h / 2615348736000) * ‖G‖
      ≤ (13465774256510 * h / 2615348736000) * (Mb / 6227020800 * (9 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hG_bd hcG_nn
  have hHbd_s : (21847538039895 * h / 2615348736000) * ‖H‖
      ≤ (21847538039895 * h / 2615348736000) * (Mb / 6227020800 * (8 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hH_bd hcH_nn
  have hIbd_s : (27345870698436 * h / 2615348736000) * ‖I‖
      ≤ (27345870698436 * h / 2615348736000) * (Mb / 6227020800 * (7 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hI_bd hcI_nn
  have hJbd_s : (26204344465152 * h / 2615348736000) * ‖J‖
      ≤ (26204344465152 * h / 2615348736000) * (Mb / 6227020800 * (6 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hJ_bd hcJ_nn
  have hKbd_s : (19058185652796 * h / 2615348736000) * ‖K‖
      ≤ (19058185652796 * h / 2615348736000) * (Mb / 6227020800 * (5 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hK_bd hcK_nn
  have hPbd_s : (10344711794985 * h / 2615348736000) * ‖P‖
      ≤ (10344711794985 * h / 2615348736000) * (Mb / 6227020800 * (4 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hP_bd hcP_nn
  have hQbd_s : (4063327863170 * h / 2615348736000) * ‖Q‖
      ≤ (4063327863170 * h / 2615348736000) * (Mb / 6227020800 * (3 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hQ_bd hcQ_nn
  have hRbd_s : (1092096992268 * h / 2615348736000) * ‖R‖
      ≤ (1092096992268 * h / 2615348736000) * (Mb / 6227020800 * (2 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hR_bd hcR_nn
  have hSbd_s : (179842822566 * h / 2615348736000) * ‖S‖
      ≤ (179842822566 * h / 2615348736000) * (Mb / 6227020800 * h ^ 13) :=
    mul_le_mul_of_nonneg_left hS_bd hcS_nn
  have hbound_alg := am12Vec_residual_bound_alg_identity Mb h
  have hh14_nn : 0 ≤ h ^ 14 := by positivity
  have hMh14_nn : 0 ≤ Mb * h ^ 14 := mul_nonneg hMnn hh14_nn
  have hslack : (414541158076267641095141 / 10602754543180800000 : ℝ) * Mb * h ^ 14
      ≤ 39099 * Mb * h ^ 14 := by
    rw [mul_assoc, mul_assoc (39099 : ℝ)]
    have hle : (414541158076267641095141 / 10602754543180800000 : ℝ) ≤ 39099 := by
      norm_num
    exact mul_le_mul_of_nonneg_right hle hMh14_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hFbd_s,
    hGbd_s, hHbd_s, hIbd_s, hJbd_s, hKbd_s, hPbd_s, hQbd_s, hRbd_s, hSbd_s]

/-- Pointwise AM12 vector truncation residual bound. -/
theorem am12Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 14 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 14 y t‖ ≤ M)
    {t h : ℝ}
    (ht : t ∈ Set.Icc a b)
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
    ‖am12VecResidual h t y‖ ≤ (39099 : ℝ) * M * h ^ 14 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have h9h : 0 ≤ 9 * h := by linarith
  have h10h : 0 ≤ 10 * h := by linarith
  have h11h : 0 ≤ 11 * h := by linarith
  have h12h : 0 ≤ 12 * h := by linarith
  have hRy11 :=
    y_fourteenth_order_taylor_remainder_vec hy hbnd ht ht11h h11h
  have hRy12 :=
    y_fourteenth_order_taylor_remainder_vec hy hbnd ht ht12h h12h
  have hRyp1 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht9h h9h
  have hRyp10 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht10h h10h
  have hRyp11 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht11h h11h
  have hRyp12 :=
    derivY_thirteenth_order_taylor_remainder_vec hy hbnd ht ht12h h12h
  unfold am12VecResidual
  set y0 : E := y t with hy0_def
  set y11 : E := y (t + 11 * h) with hy11_def
  set y12 : E := y (t + 12 * h) with hy12_def
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
  set d10 : E := deriv y (t + 10 * h) with hd10_def
  set d11 : E := deriv y (t + 11 * h) with hd11_def
  set d12 : E := deriv y (t + 12 * h) with hd12_def
  set d2t : E := iteratedDeriv 2 y t with hd2t_def
  set d3t : E := iteratedDeriv 3 y t with hd3t_def
  set d4t : E := iteratedDeriv 4 y t with hd4t_def
  set d5t : E := iteratedDeriv 5 y t with hd5t_def
  set d6t : E := iteratedDeriv 6 y t with hd6t_def
  set d7t : E := iteratedDeriv 7 y t with hd7t_def
  set d8t : E := iteratedDeriv 8 y t with hd8t_def
  set d9t : E := iteratedDeriv 9 y t with hd9t_def
  set d10t : E := iteratedDeriv 10 y t with hd10t_def
  set d11t : E := iteratedDeriv 11 y t with hd11t_def
  set d12t : E := iteratedDeriv 12 y t with hd12t_def
  set d13t : E := iteratedDeriv 13 y t with hd13t_def
  clear_value y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12
    d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t
  set A : E := y12 - y0 - am12Vec_yPoly13 12 h d0 d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hA_def
  set B : E := y11 - y0 - am12Vec_yPoly13 11 h d0 d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hB_def
  set C : E := d12 - d0 - am12Vec_dPoly12 12 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hC_def
  set D : E := d11 - d0 - am12Vec_dPoly12 11 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hD_def
  set F : E := d10 - d0 - am12Vec_dPoly12 10 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hF_def
  set G : E := d9 - d0 - am12Vec_dPoly12 9 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hG_def
  set H : E := d8 - d0 - am12Vec_dPoly12 8 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hH_def
  set I : E := d7 - d0 - am12Vec_dPoly12 7 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hI_def
  set J : E := d6 - d0 - am12Vec_dPoly12 6 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hJ_def
  set K : E := d5 - d0 - am12Vec_dPoly12 5 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hK_def
  set P : E := d4 - d0 - am12Vec_dPoly12 4 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hP_def
  set Q : E := d3 - d0 - am12Vec_dPoly12 3 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hQ_def
  set R : E := d2 - d0 - am12Vec_dPoly12 2 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hR_def
  set S : E := d1 - d0 - am12Vec_dPoly12 1 h d2t d3t d4t d5t d6t d7t
    d8t d9t d10t d11t d12t d13t with hS_def
  have hLTE_eq :=
    am12Vec_residual_alg_identity y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
      d11 d12 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t h
      A B C D F G H I J K P Q R S hA_def hB_def hC_def hD_def hF_def hG_def
      hH_def hI_def hJ_def hK_def hP_def hQ_def hR_def hS_def
  have hres_eq :
      y12 - y11 - h • (∑ j : Fin 13,
          (am12VecCoeff j) • deriv y (t + (j : ℕ) * h))
        =
          y12 - y11
            - h • ((703604254357 / 2615348736000 : ℝ) • d12
                  + (3917551216986 / 2615348736000 : ℝ) • d11
                  - (6616420957428 / 2615348736000 : ℝ) • d10
                  + (13465774256510 / 2615348736000 : ℝ) • d9
                  - (21847538039895 / 2615348736000 : ℝ) • d8
                  + (27345870698436 / 2615348736000 : ℝ) • d7
                  - (26204344465152 / 2615348736000 : ℝ) • d6
                  + (19058185652796 / 2615348736000 : ℝ) • d5
                  - (10344711794985 / 2615348736000 : ℝ) • d4
                  + (4063327863170 / 2615348736000 : ℝ) • d3
                  - (1092096992268 / 2615348736000 : ℝ) • d2
                  + (179842822566 / 2615348736000 : ℝ) • d1
                  - (13695779093 / 2615348736000 : ℝ) • d0) := by
    simp [am12VecCoeff, am12Coeff, Fin.sum_univ_succ, hd0_def, hd1_def, hd2_def,
      hd3_def, hd4_def, hd5_def, hd6_def, hd7_def, hd8_def, hd9_def, hd10_def,
      hd11_def, hd12_def]
    norm_num
    module
  rw [hres_eq, hLTE_eq]
  have hA_bd : ‖A‖ ≤ M / 87178291200 * (12 * h) ^ 14 := by
    rw [hA_def]; unfold am12Vec_yPoly13
    convert hRy12 using 2; module
  have hB_bd : ‖B‖ ≤ M / 87178291200 * (11 * h) ^ 14 := by
    rw [hB_def]; unfold am12Vec_yPoly13
    convert hRy11 using 2; module
  have hC_bd : ‖C‖ ≤ M / 6227020800 * (12 * h) ^ 13 := by
    rw [hC_def]; unfold am12Vec_dPoly12
    convert hRyp12 using 2; module
  have hD_bd : ‖D‖ ≤ M / 6227020800 * (11 * h) ^ 13 := by
    rw [hD_def]; unfold am12Vec_dPoly12
    convert hRyp11 using 2; module
  have hF_bd : ‖F‖ ≤ M / 6227020800 * (10 * h) ^ 13 := by
    rw [hF_def]; unfold am12Vec_dPoly12
    convert hRyp10 using 2; module
  have hG_bd : ‖G‖ ≤ M / 6227020800 * (9 * h) ^ 13 := by
    rw [hG_def]; unfold am12Vec_dPoly12
    convert hRyp9 using 2; module
  have hH_bd : ‖H‖ ≤ M / 6227020800 * (8 * h) ^ 13 := by
    rw [hH_def]; unfold am12Vec_dPoly12
    convert hRyp8 using 2; module
  have hI_bd : ‖I‖ ≤ M / 6227020800 * (7 * h) ^ 13 := by
    rw [hI_def]; unfold am12Vec_dPoly12
    convert hRyp7 using 2; module
  have hJ_bd : ‖J‖ ≤ M / 6227020800 * (6 * h) ^ 13 := by
    rw [hJ_def]; unfold am12Vec_dPoly12
    convert hRyp6 using 2; module
  have hK_bd : ‖K‖ ≤ M / 6227020800 * (5 * h) ^ 13 := by
    rw [hK_def]; unfold am12Vec_dPoly12
    convert hRyp5 using 2; module
  have hP_bd : ‖P‖ ≤ M / 6227020800 * (4 * h) ^ 13 := by
    rw [hP_def]; unfold am12Vec_dPoly12
    convert hRyp4 using 2; module
  have hQ_bd : ‖Q‖ ≤ M / 6227020800 * (3 * h) ^ 13 := by
    rw [hQ_def]; unfold am12Vec_dPoly12
    convert hRyp3 using 2; module
  have hR_bd : ‖R‖ ≤ M / 6227020800 * (2 * h) ^ 13 := by
    rw [hR_def]; unfold am12Vec_dPoly12
    convert hRyp2 using 2; module
  have hS_bd : ‖S‖ ≤ M / 6227020800 * h ^ 13 := by
    rw [hS_def]; unfold am12Vec_dPoly12
    convert hRyp1 using 2; module
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  clear_value A B C D F G H I J K P Q R S
  exact am12Vec_residual_combine_aux A B C D F G H I J K P Q R S hh hMnn
    hA_bd hB_bd hC_bd hD_bd hF_bd hG_bd hH_bd hI_bd hJ_bd hK_bd hP_bd hQ_bd
    hR_bd hS_bd

/-- Uniform bound on the AM12 vector one-step truncation residual on a finite
horizon, given a `C^14` exact solution. -/
theorem am12Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 14 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 12) * h ≤ T →
        ‖am12VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 14 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_fourteen_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(39099 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 12) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 9 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht10h_mem : t + 10 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 10 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht11h_mem : t + 11 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 11 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  have ht12h_mem : t + 12 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 12 * h ≤ ((n : ℝ) + 12) * h := by nlinarith
    linarith
  show ‖am12VecResidual h t y‖ ≤ 39099 * M * h ^ 14
  exact am12Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem
    ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem ht10h_mem ht11h_mem
    ht12h_mem hh.le

/-- **Adams--Moulton 12-step vector global error bound.** -/
theorem am12Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 14 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (703604254357 / 2615348736000 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsAM12TrajectoryVec h f t₀ yseq →
      0 ≤ ε₀ →
      ‖yseq 0 - y t₀‖ ≤ ε₀ →
      ‖yseq 1 - y (t₀ + h)‖ ≤ ε₀ →
      ‖yseq 2 - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖yseq 3 - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ‖yseq 4 - y (t₀ + 4 * h)‖ ≤ ε₀ →
      ‖yseq 5 - y (t₀ + 5 * h)‖ ≤ ε₀ →
      ‖yseq 6 - y (t₀ + 6 * h)‖ ≤ ε₀ →
      ‖yseq 7 - y (t₀ + 7 * h)‖ ≤ ε₀ →
      ‖yseq 8 - y (t₀ + 8 * h)‖ ≤ ε₀ →
      ‖yseq 9 - y (t₀ + 9 * h)‖ ≤ ε₀ →
      ‖yseq 10 - y (t₀ + 10 * h)‖ ≤ ε₀ →
      ‖yseq 11 - y (t₀ + 11 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 11) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((104 * L) * T) * ε₀ + K * h ^ 12 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am12Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((104 * L) * T) * (2 * C), min δ 1, ?_,
    lt_min hδ_pos (by norm_num), ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδg_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd he10_bd he11_bd N hNh
  have hδ_le : h ≤ δ := le_trans hδg_le (min_le_left δ 1)
  have h_le_one : h ≤ 1 := le_trans hδg_le (min_le_right δ 1)
  set EN : ℕ → ℝ := fun k => am12VecErrWindow h t₀ yseq y k with hEN_def
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k => by
    simpa [hEN_def] using am12VecErrWindow_nonneg h t₀ yseq y k
  have hEN0_le : EN 0 ≤ ε₀ := by
    unfold EN
    unfold am12VecErrWindow
    apply Finset.sup'_le
    intro j _
    fin_cases j
    · simpa [am12VecErr] using he0_bd
    · simpa [am12VecErr] using he1_bd
    · simpa [am12VecErr] using he2_bd
    · simpa [am12VecErr] using he3_bd
    · simpa [am12VecErr] using he4_bd
    · simpa [am12VecErr] using he5_bd
    · simpa [am12VecErr] using he6_bd
    · simpa [am12VecErr] using he7_bd
    · simpa [am12VecErr] using he8_bd
    · simpa [am12VecErr] using he9_bd
    · simpa [am12VecErr] using he10_bd
    · simpa [am12VecErr] using he11_bd
  have h104L_nn : (0 : ℝ) ≤ 104 * L := by linarith
  have hh14_le_hh13 : h ^ 14 ≤ h ^ 13 := by
    calc
      h ^ 14 = h ^ 13 * h := by ring
      _ ≤ h ^ 13 * 1 :=
        mul_le_mul_of_nonneg_left h_le_one (by positivity)
      _ = h ^ 13 := by ring
  have hstep_general : ∀ n : ℕ, n < N →
      EN (n + 1) ≤ (1 + h * (104 * L)) * EN n + (2 * C) * h ^ 13 := by
    intro n hn_lt
    have hres_arg : ((n : ℝ) + 12) * h ≤ T := by
      have hnat : n + 12 ≤ N + 11 := by omega
      have hreal : (n : ℝ) + 12 ≤ (N : ℝ) + 11 := by
        exact_mod_cast hnat
      have hle : ((n : ℝ) + 12) * h ≤ ((N : ℝ) + 11) * h :=
        mul_le_mul_of_nonneg_right hreal hh.le
      exact le_trans hle hNh
    have honestep :=
      am12Vec_one_step_error_pair_bound (E := E) (h := h) (L := L) hh.le hL hsmall
        hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hres_arg
    have h2τ : 2 * ‖am12VecResidual h
        (t₀ + (n : ℝ) * h) y‖ ≤ (2 * C) * h ^ 13 := by
      have h2res : 2 * ‖am12VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ 2 * (C * h ^ 14) :=
        mul_le_mul_of_nonneg_left hres (by norm_num)
      have hweak : 2 * (C * h ^ 14) ≤ (2 * C) * h ^ 13 := by
        have hC2_nn : 0 ≤ 2 * C := by positivity
        have := mul_le_mul_of_nonneg_left hh14_le_hh13 hC2_nn
        linarith
      exact le_trans h2res hweak
    show EN (n + 1) ≤ (1 + h * (104 * L)) * EN n + (2 * C) * h ^ 13
    simpa [hEN_def] using le_trans honestep (by linarith)
  have hNh_base : (N : ℝ) * h ≤ T := by
    have hle : (N : ℝ) * h ≤ ((N : ℝ) + 11) * h :=
      mul_le_mul_of_nonneg_right (by linarith) hh.le
    exact le_trans hle hNh
  have hgronwall :=
    lmm_error_bound_from_local_truncation
      (h := h) (L := 104 * L) (C := 2 * C) (T := T) (p := 12) (e := EN)
      (N := N) hh.le h104L_nn (by positivity) (hEN_nn 0) hstep_general
      N le_rfl hNh_base
  have hexp_nn : 0 ≤ Real.exp ((104 * L) * T) := Real.exp_nonneg _
  have hstart_chain :
      Real.exp ((104 * L) * T) * EN 0
        ≤ Real.exp ((104 * L) * T) * ε₀ :=
    mul_le_mul_of_nonneg_left hEN0_le hexp_nn
  have hEN_bound :
      EN N ≤ Real.exp ((104 * L) * T) * ε₀
        + T * Real.exp ((104 * L) * T) * (2 * C) * h ^ 12 := by
    linarith
  have hpoint_le_window : am12VecErr h t₀ yseq y N ≤ EN N := by
    show am12VecErr h t₀ yseq y N ≤ am12VecErrWindow h t₀ yseq y N
    unfold am12VecErrWindow
    have hsup := Finset.le_sup' (b := (0 : Fin 12))
      (f := fun j : Fin 12 => am12VecErr h t₀ yseq y (N + (j : ℕ)))
      (Finset.mem_univ _)
    simpa using hsup
  calc
    ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        = am12VecErr h t₀ yseq y N := rfl
    _ ≤ EN N := hpoint_le_window
    _ ≤ Real.exp ((104 * L) * T) * ε₀
        + T * Real.exp ((104 * L) * T) * (2 * C) * h ^ 12 := hEN_bound

end LMM
