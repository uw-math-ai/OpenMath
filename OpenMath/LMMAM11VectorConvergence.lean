import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB11VectorConvergence
import OpenMath.LMMAB12Convergence

/-! ## Adams--Moulton 11-step Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the AM11 scalar quantitative convergence chain in
`OpenMath/LMMAM11Convergence.lean`.  The implicit AM11 update is parameterised
by a supplied trajectory; existence of such a trajectory is a separate
fixed-point problem and is not part of this chain.

The AM11 coefficients are obtained by integrating the Lagrange basis on
nodes `0,…,11` over `[10, 11]`; over the common denominator `958003200` they
are `[5675265, -68928781, 384709327, -1305971115, 3007739418, -4963166514,
6043521486, -5519460582, 3828828885, -2092490673, 1374799219, 262747265]`,
summing to `958003200`.

The absolute-weight sum of the explicit eleven coefficients is
`635450917/21288960`, so after division by the implicit new-point factor the
growth is slackened to `61L`.  The exact thirteenth-order residual coefficient
is approximately `14002.02`, slackened to `14003`.

This file also adds public thirteenth-order vector Taylor helpers reusable
by AB12-vector and any future thirteenth-order vector chain.
-/

namespace LMM

/-! ### Thirteenth-order vector Taylor helpers (public, for AB12-vector reuse) -/

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

/-- Pointwise thirteenth-order vector Taylor (integral) remainder bound. -/
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
            - ((s - t) ^ 11 / 39916800) • iteratedDeriv 12 y t‖
          ≤ M / 479001600 * (s - t) ^ 12 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have hdy : ContDiff ℝ 12 (deriv y) := hy.deriv'
    have hbnd_d :
        ∀ u ∈ Set.Icc a b, ‖iteratedDeriv 12 (deriv y) u‖ ≤ M := by
      intro u hu
      have hidd_eq : iteratedDeriv 12 (deriv y) = iteratedDeriv 13 y := by
        have : iteratedDeriv 13 y = iteratedDeriv 12 (deriv y) :=
          iteratedDeriv_succ' (n := 12) (f := y)
        exact this.symm
      simpa [hidd_eq] using hbnd u hu
    have hrem :=
      y_twelfth_order_taylor_remainder_vec hdy hbnd_d ht
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
    have hiter10 : iteratedDeriv 10 (deriv y) t = iteratedDeriv 11 y t := by
      have : iteratedDeriv 11 y = iteratedDeriv 10 (deriv y) :=
        iteratedDeriv_succ' (n := 10) (f := y)
      rw [this]
    have hiter11 : iteratedDeriv 11 (deriv y) t = iteratedDeriv 12 y t := by
      have : iteratedDeriv 12 y = iteratedDeriv 11 (deriv y) :=
        iteratedDeriv_succ' (n := 11) (f := y)
      rw [this]
    rw [hsplit] at hrem
    simpa [hderiv2, hiter2, hiter3, hiter4, hiter5, hiter6, hiter7, hiter8,
      hiter9, hiter10, hiter11] using hrem
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
              - ((s - t) ^ 11 / 39916800) • iteratedDeriv 12 y t) := by
    rw [intervalIntegral.integral_sub
        (((((((((((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int).sub
          h_cubic_int).sub h_quartic_int).sub h_quintic_int).sub
          h_sextic_int).sub h_septic_int).sub h_octic_int).sub h_nonic_int).sub h_decic_int) h_undec_int,
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
      h_decic_eval, h_undec_eval]
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
            - ((s - t) ^ 11 / 39916800) • iteratedDeriv 12 y t)‖
        ≤ ∫ s in t..t + r, M / 479001600 * (s - t) ^ 12 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dy_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 479001600 * (s - t) ^ 12).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 479001600 * (s - t) ^ 12 = M / 6227020800 * r ^ 13 := by
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
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

/-- Pointwise twelfth-order vector Taylor (integral) remainder bound for the
derivative. -/
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
  have hdy : ContDiff ℝ 12 (deriv y) := hy.deriv'
  have hbnd_d :
      ∀ s ∈ Set.Icc a b, ‖iteratedDeriv 12 (deriv y) s‖ ≤ M := by
    intro s hs
    have hidd_eq : iteratedDeriv 12 (deriv y) = iteratedDeriv 13 y := by
      have : iteratedDeriv 13 y = iteratedDeriv 12 (deriv y) :=
        iteratedDeriv_succ' (n := 12) (f := y)
      exact this.symm
    simpa [hidd_eq] using hbnd s hs
  have hrem := y_twelfth_order_taylor_remainder_vec hdy hbnd_d ht htr hr
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
  simpa [hderiv2, hiter2, hiter3, hiter4, hiter5, hiter6, hiter7, hiter8,
    hiter9, hiter10, hiter11] using hrem

/-! ### AM11 vector trajectory predicate and residual -/

/-- AM11 vector trajectory predicate.  The new value appears inside `f`, so
existence of such a trajectory is a separate fixed-point problem. -/
structure IsAM11TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 11)
      = y (n + 10)
        + h • ((262747265 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 11) * h) (y (n + 11))
             + (1374799219 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 10) * h) (y (n + 10))
             - (2092490673 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 9) * h) (y (n + 9))
             + (3828828885 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 8) * h) (y (n + 8))
             - (5519460582 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 7) * h) (y (n + 7))
             + (6043521486 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             - (4963166514 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             + (3007739418 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             - (1305971115 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             + (384709327 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             - (68928781 / 958003200 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             + (5675265 / 958003200 : ℝ) • f (t₀ + (n : ℝ) * h) (y n))

/-- Textbook AM11 vector residual: the value of the local truncation error of
the AM11 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def am11VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 11 * h) - y (t + 10 * h)
    - h • ((262747265 / 958003200 : ℝ) • deriv y (t + 11 * h)
          + (1374799219 / 958003200 : ℝ) • deriv y (t + 10 * h)
          - (2092490673 / 958003200 : ℝ) • deriv y (t + 9 * h)
          + (3828828885 / 958003200 : ℝ) • deriv y (t + 8 * h)
          - (5519460582 / 958003200 : ℝ) • deriv y (t + 7 * h)
          + (6043521486 / 958003200 : ℝ) • deriv y (t + 6 * h)
          - (4963166514 / 958003200 : ℝ) • deriv y (t + 5 * h)
          + (3007739418 / 958003200 : ℝ) • deriv y (t + 4 * h)
          - (1305971115 / 958003200 : ℝ) • deriv y (t + 3 * h)
          + (384709327 / 958003200 : ℝ) • deriv y (t + 2 * h)
          - (68928781 / 958003200 : ℝ) • deriv y (t + h)
          + (5675265 / 958003200 : ℝ) • deriv y t)

theorem am11Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am11VecResidual h t y
      = y (t + 11 * h) - y (t + 10 * h)
          - h • ((262747265 / 958003200 : ℝ) • deriv y (t + 11 * h)
                + (1374799219 / 958003200 : ℝ) • deriv y (t + 10 * h)
                - (2092490673 / 958003200 : ℝ) • deriv y (t + 9 * h)
                + (3828828885 / 958003200 : ℝ) • deriv y (t + 8 * h)
                - (5519460582 / 958003200 : ℝ) • deriv y (t + 7 * h)
                + (6043521486 / 958003200 : ℝ) • deriv y (t + 6 * h)
                - (4963166514 / 958003200 : ℝ) • deriv y (t + 5 * h)
                + (3007739418 / 958003200 : ℝ) • deriv y (t + 4 * h)
                - (1305971115 / 958003200 : ℝ) • deriv y (t + 3 * h)
                + (384709327 / 958003200 : ℝ) • deriv y (t + 2 * h)
                - (68928781 / 958003200 : ℝ) • deriv y (t + h)
                + (5675265 / 958003200 : ℝ) • deriv y t) := by
  rfl

theorem am11Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (262747265 / 958003200 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM11TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (262747265 / 958003200 : ℝ) * h * L)
        * ‖yseq (n + 11) - y (t₀ + ((n : ℝ) + 11) * h)‖
      ≤ ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖
        + (1374799219 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖
        + (2092490673 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖
        + (3828828885 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖
        + (5519460582 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖
        + (6043521486 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
        + (4963166514 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖
        + (3007739418 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖
        + (1305971115 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (384709327 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (68928781 / 958003200 : ℝ) * h * L
            * ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (5675265 / 958003200 : ℝ) * h * L
            * ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + ‖am11VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set yn2 : E := yseq (n + 2) with hyn2_def
  set yn3 : E := yseq (n + 3) with hyn3_def
  set yn4 : E := yseq (n + 4) with hyn4_def
  set yn5 : E := yseq (n + 5) with hyn5_def
  set yn6 : E := yseq (n + 6) with hyn6_def
  set yn7 : E := yseq (n + 7) with hyn7_def
  set yn8 : E := yseq (n + 8) with hyn8_def
  set yn9 : E := yseq (n + 9) with hyn9_def
  set yn10 : E := yseq (n + 10) with hyn10_def
  set yn11 : E := yseq (n + 11) with hyn11_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set tn8 : ℝ := t₀ + ((n : ℝ) + 8) * h with htn8_def
  set tn9 : ℝ := t₀ + ((n : ℝ) + 9) * h with htn9_def
  set tn10 : ℝ := t₀ + ((n : ℝ) + 10) * h with htn10_def
  set tn11 : ℝ := t₀ + ((n : ℝ) + 11) * h with htn11_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set zn3 : E := y tn3 with hzn3_def
  set zn4 : E := y tn4 with hzn4_def
  set zn5 : E := y tn5 with hzn5_def
  set zn6 : E := y tn6 with hzn6_def
  set zn7 : E := y tn7 with hzn7_def
  set zn8 : E := y tn8 with hzn8_def
  set zn9 : E := y tn9 with hzn9_def
  set zn10 : E := y tn10 with hzn10_def
  set zn11 : E := y tn11 with hzn11_def
  set τ : E := am11VecResidual h tn y with hτ_def
  have _hsmall_record : (262747265 / 958003200 : ℝ) * h * L ≤ 1 / 2 := hsmall
  have hstep : yn11
      = yn10
        + h • ((262747265 / 958003200 : ℝ) • f tn11 yn11
             + (1374799219 / 958003200 : ℝ) • f tn10 yn10
             - (2092490673 / 958003200 : ℝ) • f tn9 yn9
             + (3828828885 / 958003200 : ℝ) • f tn8 yn8
             - (5519460582 / 958003200 : ℝ) • f tn7 yn7
             + (6043521486 / 958003200 : ℝ) • f tn6 yn6
             - (4963166514 / 958003200 : ℝ) • f tn5 yn5
             + (3007739418 / 958003200 : ℝ) • f tn4 yn4
             - (1305971115 / 958003200 : ℝ) • f tn3 yn3
             + (384709327 / 958003200 : ℝ) • f tn2 yn2
             - (68928781 / 958003200 : ℝ) • f tn1 yn1
             + (5675265 / 958003200 : ℝ) • f tn yn) := by
    simpa [hyn11_def, hyn10_def, hyn9_def, hyn8_def, hyn7_def, hyn6_def, hyn5_def,
      hyn4_def, hyn3_def, hyn2_def, hyn1_def, hyn_def, htn11_def, htn10_def,
      htn9_def, htn8_def, htn7_def, htn6_def, htn5_def, htn4_def, htn3_def,
      htn2_def, htn1_def, htn_def] using hy.recurrence n
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
  have htn_8h : tn + 8 * h = tn8 := by
    simp [htn_def, htn8_def]; ring
  have htn_9h : tn + 9 * h = tn9 := by
    simp [htn_def, htn9_def]; ring
  have htn_10h : tn + 10 * h = tn10 := by
    simp [htn_def, htn10_def]; ring
  have htn_11h : tn + 11 * h = tn11 := by
    simp [htn_def, htn11_def]; ring
  have hτ_eq : τ = zn11 - zn10
      - h • ((262747265 / 958003200 : ℝ) • f tn11 zn11
             + (1374799219 / 958003200 : ℝ) • f tn10 zn10
             - (2092490673 / 958003200 : ℝ) • f tn9 zn9
             + (3828828885 / 958003200 : ℝ) • f tn8 zn8
             - (5519460582 / 958003200 : ℝ) • f tn7 zn7
             + (6043521486 / 958003200 : ℝ) • f tn6 zn6
             - (4963166514 / 958003200 : ℝ) • f tn5 zn5
             + (3007739418 / 958003200 : ℝ) • f tn4 zn4
             - (1305971115 / 958003200 : ℝ) • f tn3 zn3
             + (384709327 / 958003200 : ℝ) • f tn2 zn2
             - (68928781 / 958003200 : ℝ) • f tn1 zn1
             + (5675265 / 958003200 : ℝ) • f tn zn) := by
    show am11VecResidual h tn y = _
    unfold am11VecResidual
    rw [htn1_h, htn_2h, htn_3h, htn_4h, htn_5h, htn_6h, htn_7h, htn_8h, htn_9h,
      htn_10h, htn_11h, hyf tn11, hyf tn10, hyf tn9, hyf tn8, hyf tn7, hyf tn6,
      hyf tn5, hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  have halg : yn11 - zn11
      = (yn10 - zn10)
        + h • ((262747265 / 958003200 : ℝ) • (f tn11 yn11 - f tn11 zn11))
        + h • ((1374799219 / 958003200 : ℝ) • (f tn10 yn10 - f tn10 zn10))
        - h • ((2092490673 / 958003200 : ℝ) • (f tn9 yn9 - f tn9 zn9))
        + h • ((3828828885 / 958003200 : ℝ) • (f tn8 yn8 - f tn8 zn8))
        - h • ((5519460582 / 958003200 : ℝ) • (f tn7 yn7 - f tn7 zn7))
        + h • ((6043521486 / 958003200 : ℝ) • (f tn6 yn6 - f tn6 zn6))
        - h • ((4963166514 / 958003200 : ℝ) • (f tn5 yn5 - f tn5 zn5))
        + h • ((3007739418 / 958003200 : ℝ) • (f tn4 yn4 - f tn4 zn4))
        - h • ((1305971115 / 958003200 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        + h • ((384709327 / 958003200 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        - h • ((68928781 / 958003200 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        + h • ((5675265 / 958003200 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_add]
    abel
  have hLip11 : ‖f tn11 yn11 - f tn11 zn11‖ ≤ L * ‖yn11 - zn11‖ := hf tn11 yn11 zn11
  have hLip10 : ‖f tn10 yn10 - f tn10 zn10‖ ≤ L * ‖yn10 - zn10‖ := hf tn10 yn10 zn10
  have hLip9 : ‖f tn9 yn9 - f tn9 zn9‖ ≤ L * ‖yn9 - zn9‖ := hf tn9 yn9 zn9
  have hLip8 : ‖f tn8 yn8 - f tn8 zn8‖ ≤ L * ‖yn8 - zn8‖ := hf tn8 yn8 zn8
  have hLip7 : ‖f tn7 yn7 - f tn7 zn7‖ ≤ L * ‖yn7 - zn7‖ := hf tn7 yn7 zn7
  have hLip6 : ‖f tn6 yn6 - f tn6 zn6‖ ≤ L * ‖yn6 - zn6‖ := hf tn6 yn6 zn6
  have hLip5 : ‖f tn5 yn5 - f tn5 zn5‖ ≤ L * ‖yn5 - zn5‖ := hf tn5 yn5 zn5
  have hLip4 : ‖f tn4 yn4 - f tn4 zn4‖ ≤ L * ‖yn4 - zn4‖ := hf tn4 yn4 zn4
  have hLip3 : ‖f tn3 yn3 - f tn3 zn3‖ ≤ L * ‖yn3 - zn3‖ := hf tn3 yn3 zn3
  have hLip2 : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ := hf tn2 yn2 zn2
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ := hf tn1 yn1 zn1
  have hLip0 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ := hf tn yn zn
  have hc11_nn : (0 : ℝ) ≤ 262747265 / 958003200 := by norm_num
  have hc10_nn : (0 : ℝ) ≤ 1374799219 / 958003200 := by norm_num
  have hc9_nn : (0 : ℝ) ≤ 2092490673 / 958003200 := by norm_num
  have hc8_nn : (0 : ℝ) ≤ 3828828885 / 958003200 := by norm_num
  have hc7_nn : (0 : ℝ) ≤ 5519460582 / 958003200 := by norm_num
  have hc6_nn : (0 : ℝ) ≤ 6043521486 / 958003200 := by norm_num
  have hc5_nn : (0 : ℝ) ≤ 4963166514 / 958003200 := by norm_num
  have hc4_nn : (0 : ℝ) ≤ 3007739418 / 958003200 := by norm_num
  have hc3_nn : (0 : ℝ) ≤ 1305971115 / 958003200 := by norm_num
  have hc2_nn : (0 : ℝ) ≤ 384709327 / 958003200 := by norm_num
  have hc1_nn : (0 : ℝ) ≤ 68928781 / 958003200 := by norm_num
  have hc0_nn : (0 : ℝ) ≤ 5675265 / 958003200 := by norm_num
  set A : E := yn10 - zn10 with hA_def
  set B11 : E := h • ((262747265 / 958003200 : ℝ) • (f tn11 yn11 - f tn11 zn11))
    with hB11_def
  set B10 : E := h • ((1374799219 / 958003200 : ℝ) • (f tn10 yn10 - f tn10 zn10))
    with hB10_def
  set B9 : E := h • ((2092490673 / 958003200 : ℝ) • (f tn9 yn9 - f tn9 zn9))
    with hB9_def
  set B8 : E := h • ((3828828885 / 958003200 : ℝ) • (f tn8 yn8 - f tn8 zn8))
    with hB8_def
  set B7 : E := h • ((5519460582 / 958003200 : ℝ) • (f tn7 yn7 - f tn7 zn7))
    with hB7_def
  set B6 : E := h • ((6043521486 / 958003200 : ℝ) • (f tn6 yn6 - f tn6 zn6))
    with hB6_def
  set B5 : E := h • ((4963166514 / 958003200 : ℝ) • (f tn5 yn5 - f tn5 zn5))
    with hB5_def
  set B4 : E := h • ((3007739418 / 958003200 : ℝ) • (f tn4 yn4 - f tn4 zn4))
    with hB4_def
  set B3 : E := h • ((1305971115 / 958003200 : ℝ) • (f tn3 yn3 - f tn3 zn3))
    with hB3_def
  set B2 : E := h • ((384709327 / 958003200 : ℝ) • (f tn2 yn2 - f tn2 zn2))
    with hB2_def
  set B1 : E := h • ((68928781 / 958003200 : ℝ) • (f tn1 yn1 - f tn1 zn1))
    with hB1_def
  set B0 : E := h • ((5675265 / 958003200 : ℝ) • (f tn yn - f tn zn))
    with hB0_def
  have halg' :
      yn11 - zn11
        = A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2 - B1 + B0 - τ := by
    simpa [hA_def, hB11_def, hB10_def, hB9_def, hB8_def, hB7_def, hB6_def, hB5_def,
      hB4_def, hB3_def, hB2_def, hB1_def, hB0_def] using halg
  have h11_norm :
      ‖B11‖ ≤ (262747265 / 958003200 : ℝ) * h * L * ‖yn11 - zn11‖ := by
    rw [hB11_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc11_nn]
    have : h * ((262747265 / 958003200 : ℝ) * ‖f tn11 yn11 - f tn11 zn11‖)
        ≤ h * ((262747265 / 958003200 : ℝ) * (L * ‖yn11 - zn11‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip11 hc11_nn
    calc h * ((262747265 / 958003200 : ℝ) * ‖f tn11 yn11 - f tn11 zn11‖)
        ≤ h * ((262747265 / 958003200 : ℝ) * (L * ‖yn11 - zn11‖)) := this
      _ = (262747265 / 958003200 : ℝ) * h * L * ‖yn11 - zn11‖ := by ring
  have h10_norm :
      ‖B10‖ ≤ (1374799219 / 958003200 : ℝ) * h * L * ‖yn10 - zn10‖ := by
    rw [hB10_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc10_nn]
    have : h * ((1374799219 / 958003200 : ℝ) * ‖f tn10 yn10 - f tn10 zn10‖)
        ≤ h * ((1374799219 / 958003200 : ℝ) * (L * ‖yn10 - zn10‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip10 hc10_nn
    calc h * ((1374799219 / 958003200 : ℝ) * ‖f tn10 yn10 - f tn10 zn10‖)
        ≤ h * ((1374799219 / 958003200 : ℝ) * (L * ‖yn10 - zn10‖)) := this
      _ = (1374799219 / 958003200 : ℝ) * h * L * ‖yn10 - zn10‖ := by ring
  have h9_norm :
      ‖B9‖ ≤ (2092490673 / 958003200 : ℝ) * h * L * ‖yn9 - zn9‖ := by
    rw [hB9_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc9_nn]
    have : h * ((2092490673 / 958003200 : ℝ) * ‖f tn9 yn9 - f tn9 zn9‖)
        ≤ h * ((2092490673 / 958003200 : ℝ) * (L * ‖yn9 - zn9‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip9 hc9_nn
    calc h * ((2092490673 / 958003200 : ℝ) * ‖f tn9 yn9 - f tn9 zn9‖)
        ≤ h * ((2092490673 / 958003200 : ℝ) * (L * ‖yn9 - zn9‖)) := this
      _ = (2092490673 / 958003200 : ℝ) * h * L * ‖yn9 - zn9‖ := by ring
  have h8_norm :
      ‖B8‖ ≤ (3828828885 / 958003200 : ℝ) * h * L * ‖yn8 - zn8‖ := by
    rw [hB8_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc8_nn]
    have : h * ((3828828885 / 958003200 : ℝ) * ‖f tn8 yn8 - f tn8 zn8‖)
        ≤ h * ((3828828885 / 958003200 : ℝ) * (L * ‖yn8 - zn8‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip8 hc8_nn
    calc h * ((3828828885 / 958003200 : ℝ) * ‖f tn8 yn8 - f tn8 zn8‖)
        ≤ h * ((3828828885 / 958003200 : ℝ) * (L * ‖yn8 - zn8‖)) := this
      _ = (3828828885 / 958003200 : ℝ) * h * L * ‖yn8 - zn8‖ := by ring
  have h7_norm :
      ‖B7‖ ≤ (5519460582 / 958003200 : ℝ) * h * L * ‖yn7 - zn7‖ := by
    rw [hB7_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc7_nn]
    have : h * ((5519460582 / 958003200 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((5519460582 / 958003200 : ℝ) * (L * ‖yn7 - zn7‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip7 hc7_nn
    calc h * ((5519460582 / 958003200 : ℝ) * ‖f tn7 yn7 - f tn7 zn7‖)
        ≤ h * ((5519460582 / 958003200 : ℝ) * (L * ‖yn7 - zn7‖)) := this
      _ = (5519460582 / 958003200 : ℝ) * h * L * ‖yn7 - zn7‖ := by ring
  have h6_norm :
      ‖B6‖ ≤ (6043521486 / 958003200 : ℝ) * h * L * ‖yn6 - zn6‖ := by
    rw [hB6_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc6_nn]
    have : h * ((6043521486 / 958003200 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((6043521486 / 958003200 : ℝ) * (L * ‖yn6 - zn6‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip6 hc6_nn
    calc h * ((6043521486 / 958003200 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((6043521486 / 958003200 : ℝ) * (L * ‖yn6 - zn6‖)) := this
      _ = (6043521486 / 958003200 : ℝ) * h * L * ‖yn6 - zn6‖ := by ring
  have h5_norm :
      ‖B5‖ ≤ (4963166514 / 958003200 : ℝ) * h * L * ‖yn5 - zn5‖ := by
    rw [hB5_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc5_nn]
    have : h * ((4963166514 / 958003200 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((4963166514 / 958003200 : ℝ) * (L * ‖yn5 - zn5‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip5 hc5_nn
    calc h * ((4963166514 / 958003200 : ℝ) * ‖f tn5 yn5 - f tn5 zn5‖)
        ≤ h * ((4963166514 / 958003200 : ℝ) * (L * ‖yn5 - zn5‖)) := this
      _ = (4963166514 / 958003200 : ℝ) * h * L * ‖yn5 - zn5‖ := by ring
  have h4_norm :
      ‖B4‖ ≤ (3007739418 / 958003200 : ℝ) * h * L * ‖yn4 - zn4‖ := by
    rw [hB4_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc4_nn]
    have : h * ((3007739418 / 958003200 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((3007739418 / 958003200 : ℝ) * (L * ‖yn4 - zn4‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip4 hc4_nn
    calc h * ((3007739418 / 958003200 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((3007739418 / 958003200 : ℝ) * (L * ‖yn4 - zn4‖)) := this
      _ = (3007739418 / 958003200 : ℝ) * h * L * ‖yn4 - zn4‖ := by ring
  have h3_norm :
      ‖B3‖ ≤ (1305971115 / 958003200 : ℝ) * h * L * ‖yn3 - zn3‖ := by
    rw [hB3_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc3_nn]
    have : h * ((1305971115 / 958003200 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((1305971115 / 958003200 : ℝ) * (L * ‖yn3 - zn3‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip3 hc3_nn
    calc h * ((1305971115 / 958003200 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((1305971115 / 958003200 : ℝ) * (L * ‖yn3 - zn3‖)) := this
      _ = (1305971115 / 958003200 : ℝ) * h * L * ‖yn3 - zn3‖ := by ring
  have h2_norm :
      ‖B2‖ ≤ (384709327 / 958003200 : ℝ) * h * L * ‖yn2 - zn2‖ := by
    rw [hB2_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc2_nn]
    have : h * ((384709327 / 958003200 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((384709327 / 958003200 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 hc2_nn
    calc h * ((384709327 / 958003200 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((384709327 / 958003200 : ℝ) * (L * ‖yn2 - zn2‖)) := this
      _ = (384709327 / 958003200 : ℝ) * h * L * ‖yn2 - zn2‖ := by ring
  have h1_norm :
      ‖B1‖ ≤ (68928781 / 958003200 : ℝ) * h * L * ‖yn1 - zn1‖ := by
    rw [hB1_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc1_nn]
    have : h * ((68928781 / 958003200 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((68928781 / 958003200 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 hc1_nn
    calc h * ((68928781 / 958003200 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((68928781 / 958003200 : ℝ) * (L * ‖yn1 - zn1‖)) := this
      _ = (68928781 / 958003200 : ℝ) * h * L * ‖yn1 - zn1‖ := by ring
  have h0_norm :
      ‖B0‖ ≤ (5675265 / 958003200 : ℝ) * h * L * ‖yn - zn‖ := by
    rw [hB0_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg hc0_nn]
    have : h * ((5675265 / 958003200 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((5675265 / 958003200 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 hc0_nn
    calc h * ((5675265 / 958003200 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((5675265 / 958003200 : ℝ) * (L * ‖yn - zn‖)) := this
      _ = (5675265 / 958003200 : ℝ) * h * L * ‖yn - zn‖ := by ring
  have htri :
      ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2 - B1 + B0 - τ‖
        ≤ ‖A‖ + ‖B11‖ + ‖B10‖ + ‖B9‖ + ‖B8‖ + ‖B7‖ + ‖B6‖ + ‖B5‖ + ‖B4‖
            + ‖B3‖ + ‖B2‖ + ‖B1‖ + ‖B0‖ + ‖τ‖ := by
    have h1 : ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2 - B1 + B0 - τ‖
        ≤ ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2 - B1 + B0‖ + ‖τ‖ :=
      norm_sub_le _ _
    have h2 : ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2 - B1 + B0‖
        ≤ ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2 - B1‖ + ‖B0‖ :=
      norm_add_le _ _
    have h3 : ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2 - B1‖
        ≤ ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2‖ + ‖B1‖ :=
      norm_sub_le _ _
    have h4 : ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2‖
        ≤ ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3‖ + ‖B2‖ :=
      norm_add_le _ _
    have h5 : ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3‖
        ≤ ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4‖ + ‖B3‖ :=
      norm_sub_le _ _
    have h6 : ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4‖
        ≤ ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5‖ + ‖B4‖ :=
      norm_add_le _ _
    have h7 : ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5‖
        ≤ ‖A + B11 + B10 - B9 + B8 - B7 + B6‖ + ‖B5‖ :=
      norm_sub_le _ _
    have h8 : ‖A + B11 + B10 - B9 + B8 - B7 + B6‖
        ≤ ‖A + B11 + B10 - B9 + B8 - B7‖ + ‖B6‖ :=
      norm_add_le _ _
    have h9 : ‖A + B11 + B10 - B9 + B8 - B7‖
        ≤ ‖A + B11 + B10 - B9 + B8‖ + ‖B7‖ :=
      norm_sub_le _ _
    have h10 : ‖A + B11 + B10 - B9 + B8‖
        ≤ ‖A + B11 + B10 - B9‖ + ‖B8‖ :=
      norm_add_le _ _
    have h11 : ‖A + B11 + B10 - B9‖
        ≤ ‖A + B11 + B10‖ + ‖B9‖ :=
      norm_sub_le _ _
    have h12 : ‖A + B11 + B10‖
        ≤ ‖A + B11‖ + ‖B10‖ := norm_add_le _ _
    have h13 : ‖A + B11‖ ≤ ‖A‖ + ‖B11‖ := norm_add_le _ _
    linarith
  have hmain :
      ‖yn11 - zn11‖
        ≤ ‖yn10 - zn10‖
          + (262747265 / 958003200 : ℝ) * h * L * ‖yn11 - zn11‖
          + (1374799219 / 958003200 : ℝ) * h * L * ‖yn10 - zn10‖
          + (2092490673 / 958003200 : ℝ) * h * L * ‖yn9 - zn9‖
          + (3828828885 / 958003200 : ℝ) * h * L * ‖yn8 - zn8‖
          + (5519460582 / 958003200 : ℝ) * h * L * ‖yn7 - zn7‖
          + (6043521486 / 958003200 : ℝ) * h * L * ‖yn6 - zn6‖
          + (4963166514 / 958003200 : ℝ) * h * L * ‖yn5 - zn5‖
          + (3007739418 / 958003200 : ℝ) * h * L * ‖yn4 - zn4‖
          + (1305971115 / 958003200 : ℝ) * h * L * ‖yn3 - zn3‖
          + (384709327 / 958003200 : ℝ) * h * L * ‖yn2 - zn2‖
          + (68928781 / 958003200 : ℝ) * h * L * ‖yn1 - zn1‖
          + (5675265 / 958003200 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    calc ‖yn11 - zn11‖
        = ‖A + B11 + B10 - B9 + B8 - B7 + B6 - B5 + B4 - B3 + B2 - B1 + B0 - τ‖ := by
            rw [halg']
      _ ≤ ‖A‖ + ‖B11‖ + ‖B10‖ + ‖B9‖ + ‖B8‖ + ‖B7‖ + ‖B6‖ + ‖B5‖ + ‖B4‖
          + ‖B3‖ + ‖B2‖ + ‖B1‖ + ‖B0‖ + ‖τ‖ := htri
      _ ≤ ‖yn10 - zn10‖
          + (262747265 / 958003200 : ℝ) * h * L * ‖yn11 - zn11‖
          + (1374799219 / 958003200 : ℝ) * h * L * ‖yn10 - zn10‖
          + (2092490673 / 958003200 : ℝ) * h * L * ‖yn9 - zn9‖
          + (3828828885 / 958003200 : ℝ) * h * L * ‖yn8 - zn8‖
          + (5519460582 / 958003200 : ℝ) * h * L * ‖yn7 - zn7‖
          + (6043521486 / 958003200 : ℝ) * h * L * ‖yn6 - zn6‖
          + (4963166514 / 958003200 : ℝ) * h * L * ‖yn5 - zn5‖
          + (3007739418 / 958003200 : ℝ) * h * L * ‖yn4 - zn4‖
          + (1305971115 / 958003200 : ℝ) * h * L * ‖yn3 - zn3‖
          + (384709327 / 958003200 : ℝ) * h * L * ‖yn2 - zn2‖
          + (68928781 / 958003200 : ℝ) * h * L * ‖yn1 - zn1‖
          + (5675265 / 958003200 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
        rw [hA_def]
        linarith [h11_norm, h10_norm, h9_norm, h8_norm, h7_norm, h6_norm, h5_norm,
          h4_norm, h3_norm, h2_norm, h1_norm, h0_norm]
  linarith [hmain]

/-- Auxiliary: each of eleven nonneg reals is ≤ their nested max (left-associated 11-fold max). -/
private lemma am11Vec_max11_bounds
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℝ) :
    let M := max (max (max (max (max (max (max (max (max (max
                a0 a1) a2) a3) a4) a5) a6) a7) a8) a9) a10
    a0 ≤ M ∧ a1 ≤ M ∧ a2 ≤ M ∧ a3 ≤ M ∧ a4 ≤ M ∧ a5 ≤ M ∧ a6 ≤ M ∧
    a7 ≤ M ∧ a8 ≤ M ∧ a9 ≤ M ∧ a10 ≤ M := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _)
                  (le_trans (le_max_left _ _)
                    (le_trans (le_max_left _ _) (le_max_left _ _)))))))))
  · exact le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _)
                  (le_trans (le_max_left _ _)
                    (le_trans (le_max_left _ _) (le_max_left _ _)))))))))
  · exact le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _)
                  (le_trans (le_max_left _ _) (le_max_left _ _))))))))
  · exact le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _)
                (le_trans (le_max_left _ _) (le_max_left _ _)))))))
  · exact le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  · exact le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  · exact le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  · exact le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  · exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

/-- Auxiliary: slack-bound algebraic identity for AM11 vector smallness condition. -/
private lemma am11Vec_slack_aux
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (262747265 / 958003200 : ℝ) * h * L ≤ 1 / 2) :
    (1 + (635450917 / 21288960 : ℝ) * (h * L)
      ≤ (1 - (262747265 / 958003200 : ℝ) * h * L) * (1 + h * (61 * L)))
    ∧ ((1 : ℝ) ≤ (1 - (262747265 / 958003200 : ℝ) * h * L) * 2)
    ∧ (0 < 1 - (262747265 / 958003200 : ℝ) * h * L) := by
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 479001600 / 262747265 := by nlinarith [hsmall]
  refine ⟨?_, ?_, ?_⟩
  · have hxL_eq :
        (1 - (262747265 / 958003200 : ℝ) * h * L) * (1 + h * (61 * L))
          - (1 + (635450917 / 21288960 : ℝ) * (h * L))
          = (h * L) / 958003200 * (29580156670 - 16027583165 * (h * L)) := by ring
    have hpos : 0 ≤ 29580156670 - 16027583165 * (h * L) := by
      have hbound :
          16027583165 * (h * L) ≤ 16027583165 * (479001600 / 262747265 : ℝ) :=
        mul_le_mul_of_nonneg_left hx_small (by norm_num)
      have hnum : (16027583165 : ℝ) * (479001600 / 262747265) ≤ 29580156670 := by
        norm_num
      linarith
    have hprod : 0 ≤ (h * L) / 958003200 * (29580156670 - 16027583165 * (h * L)) :=
      mul_nonneg (by positivity) hpos
    linarith
  · nlinarith [hsmall]
  · nlinarith [hsmall]

/-- Divided AM11 one-step error bound at the new point (vector). -/
theorem am11Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (262747265 / 958003200 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM11TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖yseq (n + 11) - y (t₀ + ((n : ℝ) + 11) * h)‖
      ≤ (1 + h * (61 * L))
            * max (max (max (max (max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
                ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
                ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖)
                ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖)
                ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖
        + 2 * ‖am11VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
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
  set en8 : ℝ :=
    ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖ with hen8_def
  set en9 : ℝ :=
    ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖ with hen9_def
  set en10 : ℝ :=
    ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖ with hen10_def
  set en11 : ℝ :=
    ‖yseq (n + 11) - y (t₀ + ((n : ℝ) + 11) * h)‖ with hen11_def
  set τabs : ℝ :=
    ‖am11VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max (max (max (max (max en en1) en2) en3) en4) en5)
      en6) en7) en8) en9) en10
    with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hen4_nn : 0 ≤ en4 := norm_nonneg _
  have hen5_nn : 0 ≤ en5 := norm_nonneg _
  have hen6_nn : 0 ≤ en6 := norm_nonneg _
  have hen7_nn : 0 ≤ en7 := norm_nonneg _
  have hen8_nn : 0 ≤ en8 := norm_nonneg _
  have hen9_nn : 0 ≤ en9 := norm_nonneg _
  have hen10_nn : 0 ≤ en10 := norm_nonneg _
  have hen11_nn : 0 ≤ en11 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  obtain ⟨hen_le_E0, hen1_le_E0, hen2_le_E0, hen3_le_E0, hen4_le_E0, hen5_le_E0, hen6_le_E0,
    hen7_le_E0, hen8_le_E0, hen9_le_E0, hen10_le_E0⟩ :=
    am11Vec_max11_bounds en en1 en2 en3 en4 en5 en6 en7 en8 en9 en10
  have hen_le_E : en ≤ Emax := hen_le_E0
  have hen1_le_E : en1 ≤ Emax := hen1_le_E0
  have hen2_le_E : en2 ≤ Emax := hen2_le_E0
  have hen3_le_E : en3 ≤ Emax := hen3_le_E0
  have hen4_le_E : en4 ≤ Emax := hen4_le_E0
  have hen5_le_E : en5 ≤ Emax := hen5_le_E0
  have hen6_le_E : en6 ≤ Emax := hen6_le_E0
  have hen7_le_E : en7 ≤ Emax := hen7_le_E0
  have hen8_le_E : en8 ≤ Emax := hen8_le_E0
  have hen9_le_E : en9 ≤ Emax := hen9_le_E0
  have hen10_le_E : en10 ≤ Emax := hen10_le_E0
  have hE_nn : 0 ≤ Emax := le_trans hen_nn hen_le_E
  clear hen_le_E0 hen1_le_E0 hen2_le_E0 hen3_le_E0 hen4_le_E0 hen5_le_E0
    hen6_le_E0 hen7_le_E0 hen8_le_E0 hen9_le_E0 hen10_le_E0
  clear_value en en1 en2 en3 en4 en5 en6 en7 en8 en9 en10 en11 τabs Emax
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  obtain ⟨hcoeffE_le, hcoeffτ_le, hA_pos⟩ := am11Vec_slack_aux hh hL hsmall
  have hstep :
      (1 - (262747265 / 958003200 : ℝ) * h * L) * en11
        ≤ en10
          + (1374799219 / 958003200 : ℝ) * h * L * en10
          + (2092490673 / 958003200 : ℝ) * h * L * en9
          + (3828828885 / 958003200 : ℝ) * h * L * en8
          + (5519460582 / 958003200 : ℝ) * h * L * en7
          + (6043521486 / 958003200 : ℝ) * h * L * en6
          + (4963166514 / 958003200 : ℝ) * h * L * en5
          + (3007739418 / 958003200 : ℝ) * h * L * en4
          + (1305971115 / 958003200 : ℝ) * h * L * en3
          + (384709327 / 958003200 : ℝ) * h * L * en2
          + (68928781 / 958003200 : ℝ) * h * L * en1
          + (5675265 / 958003200 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hen9_def, hen10_def, hen11_def, hτabs_def]
      using
      (am11Vec_one_step_lipschitz (E := E) (h := h) (L := L)
        hh hsmall hf t₀ hy y hyf n)
  have hc1_nn : 0 ≤ (1374799219 / 958003200 : ℝ) * h * L := by positivity
  have hc2_nn : 0 ≤ (2092490673 / 958003200 : ℝ) * h * L := by positivity
  have hc3_nn : 0 ≤ (3828828885 / 958003200 : ℝ) * h * L := by positivity
  have hc4_nn : 0 ≤ (5519460582 / 958003200 : ℝ) * h * L := by positivity
  have hc5_nn : 0 ≤ (6043521486 / 958003200 : ℝ) * h * L := by positivity
  have hc6_nn : 0 ≤ (4963166514 / 958003200 : ℝ) * h * L := by positivity
  have hc7_nn : 0 ≤ (3007739418 / 958003200 : ℝ) * h * L := by positivity
  have hc8_nn : 0 ≤ (1305971115 / 958003200 : ℝ) * h * L := by positivity
  have hc9_nn : 0 ≤ (384709327 / 958003200 : ℝ) * h * L := by positivity
  have hc10_nn : 0 ≤ (68928781 / 958003200 : ℝ) * h * L := by positivity
  have hc11_nn : 0 ≤ (5675265 / 958003200 : ℝ) * h * L := by positivity
  have h1_le :
      (1374799219 / 958003200 : ℝ) * h * L * en10
        ≤ (1374799219 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen10_le_E hc1_nn
  have h2_le :
      (2092490673 / 958003200 : ℝ) * h * L * en9
        ≤ (2092490673 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen9_le_E hc2_nn
  have h3_le :
      (3828828885 / 958003200 : ℝ) * h * L * en8
        ≤ (3828828885 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen8_le_E hc3_nn
  have h4_le :
      (5519460582 / 958003200 : ℝ) * h * L * en7
        ≤ (5519460582 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen7_le_E hc4_nn
  have h5_le :
      (6043521486 / 958003200 : ℝ) * h * L * en6
        ≤ (6043521486 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen6_le_E hc5_nn
  have h6_le :
      (4963166514 / 958003200 : ℝ) * h * L * en5
        ≤ (4963166514 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen5_le_E hc6_nn
  have h7_le :
      (3007739418 / 958003200 : ℝ) * h * L * en4
        ≤ (3007739418 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen4_le_E hc7_nn
  have h8_le :
      (1305971115 / 958003200 : ℝ) * h * L * en3
        ≤ (1305971115 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen3_le_E hc8_nn
  have h9_le :
      (384709327 / 958003200 : ℝ) * h * L * en2
        ≤ (384709327 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen2_le_E hc9_nn
  have h10_le :
      (68928781 / 958003200 : ℝ) * h * L * en1
        ≤ (68928781 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen1_le_E hc10_nn
  have h11_le :
      (5675265 / 958003200 : ℝ) * h * L * en
        ≤ (5675265 / 958003200 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen_le_E hc11_nn
  have hR_le :
      en10
          + (1374799219 / 958003200 : ℝ) * h * L * en10
          + (2092490673 / 958003200 : ℝ) * h * L * en9
          + (3828828885 / 958003200 : ℝ) * h * L * en8
          + (5519460582 / 958003200 : ℝ) * h * L * en7
          + (6043521486 / 958003200 : ℝ) * h * L * en6
          + (4963166514 / 958003200 : ℝ) * h * L * en5
          + (3007739418 / 958003200 : ℝ) * h * L * en4
          + (1305971115 / 958003200 : ℝ) * h * L * en3
          + (384709327 / 958003200 : ℝ) * h * L * en2
          + (68928781 / 958003200 : ℝ) * h * L * en1
          + (5675265 / 958003200 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (635450917 / 21288960 : ℝ) * (h * L)) * Emax + τabs := by
    have h_alg :
        Emax + (1374799219 / 958003200 : ℝ) * h * L * Emax
            + (2092490673 / 958003200 : ℝ) * h * L * Emax
            + (3828828885 / 958003200 : ℝ) * h * L * Emax
            + (5519460582 / 958003200 : ℝ) * h * L * Emax
            + (6043521486 / 958003200 : ℝ) * h * L * Emax
            + (4963166514 / 958003200 : ℝ) * h * L * Emax
            + (3007739418 / 958003200 : ℝ) * h * L * Emax
            + (1305971115 / 958003200 : ℝ) * h * L * Emax
            + (384709327 / 958003200 : ℝ) * h * L * Emax
            + (68928781 / 958003200 : ℝ) * h * L * Emax
            + (5675265 / 958003200 : ℝ) * h * L * Emax + τabs
          = (1 + (635450917 / 21288960 : ℝ) * (h * L)) * Emax + τabs := by
      ring
    linarith [hen10_le_E]
  have hE_part :
      (1 + (635450917 / 21288960 : ℝ) * (h * L)) * Emax
        ≤ ((1 - (262747265 / 958003200 : ℝ) * h * L) * (1 + h * (61 * L))) * Emax :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (262747265 / 958003200 : ℝ) * h * L) * 2) * τabs := by
    have hraw := mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
    calc
      τabs = (1 : ℝ) * τabs := by ring
      _ ≤ ((1 - (262747265 / 958003200 : ℝ) * h * L) * 2) * τabs := hraw
  have hfactor :
      (1 + (635450917 / 21288960 : ℝ) * (h * L)) * Emax + τabs
        ≤ (1 - (262747265 / 958003200 : ℝ) * h * L)
            * ((1 + h * (61 * L)) * Emax + 2 * τabs) := by
    let A : ℝ := 1 - (262747265 / 958003200 : ℝ) * h * L
    let B : ℝ := 1 + h * (61 * L)
    let Cg : ℝ := 1 + (635450917 / 21288960 : ℝ) * (h * L)
    change Cg * Emax + τabs ≤ A * (B * Emax + 2 * τabs)
    have hE_part' : Cg * Emax ≤ (A * B) * Emax := hE_part
    have hτ_part' : τabs ≤ (A * 2) * τabs := hτ_part
    calc
      Cg * Emax + τabs ≤ (A * B) * Emax + (A * 2) * τabs :=
        add_le_add hE_part' hτ_part'
      _ = A * (B * Emax + 2 * τabs) := by ring
  have hprod :
      (1 - (262747265 / 958003200 : ℝ) * h * L) * en11
        ≤ (1 - (262747265 / 958003200 : ℝ) * h * L)
            * ((1 + h * (61 * L)) * Emax + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  exact le_of_mul_le_mul_left hprod hA_pos

/-- Max-norm AM11 one-step recurrence on the rolling 11-window (vector). -/
theorem am11Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (262747265 / 958003200 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM11TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max (max (max (max
          ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
          ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
          ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
          ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
          ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
          ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖)
          ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖)
          ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖)
          ‖yseq (n + 11) - y (t₀ + ((n : ℝ) + 11) * h)‖
      ≤ (1 + h * (61 * L))
            * max (max (max (max (max (max (max (max (max (max
                ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖)
                ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
                ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖)
                ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖)
                ‖yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)‖)
                ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖)
                ‖yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)‖)
                ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖)
                ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖)
                ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖
        + 2 * ‖am11VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
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
  set en8 : ℝ :=
    ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖ with hen8_def
  set en9 : ℝ :=
    ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖ with hen9_def
  set en10 : ℝ :=
    ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖ with hen10_def
  set en11 : ℝ :=
    ‖yseq (n + 11) - y (t₀ + ((n : ℝ) + 11) * h)‖ with hen11_def
  set τabs : ℝ :=
    ‖am11VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ :=
    max (max (max (max (max (max (max (max (max (max en en1) en2) en3) en4) en5)
      en6) en7) en8) en9) en10
    with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  obtain ⟨_hen_le_E, hen1_le_E, hen2_le_E, hen3_le_E, hen4_le_E, hen5_le_E, hen6_le_E,
    hen7_le_E, hen8_le_E, hen9_le_E, hen10_le_E⟩ :=
    am11Vec_max11_bounds en en1 en2 en3 en4 en5 en6 en7 en8 en9 en10
  have hE_nn : 0 ≤ Emax := le_trans hen_nn _hen_le_E
  clear_value en en1 en2 en3 en4 en5 en6 en7 en8 en9 en10 en11 τabs Emax
  have h61hL_nn : 0 ≤ h * (61 * L) := by positivity
  have hen11_bd :
      en11 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hen9_def, hen10_def, hen11_def, hτabs_def, hE_def]
      using
      (am11Vec_one_step_error_bound (E := E) (h := h) (L := L)
        hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : Emax ≤ (1 + h * (61 * L)) * Emax := by
    have hone : (1 : ℝ) * Emax ≤ (1 + h * (61 * L)) * Emax :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hτ_2nn : 0 ≤ 2 * τabs := by positivity
  have hen1_bd : en1 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  have hen4_bd : en4 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen4_le_E, hE_le_grow]
  have hen5_bd : en5 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen5_le_E, hE_le_grow]
  have hen6_bd : en6 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen6_le_E, hE_le_grow]
  have hen7_bd : en7 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen7_le_E, hE_le_grow]
  have hen8_bd : en8 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen8_le_E, hE_le_grow]
  have hen9_bd : en9 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen9_le_E, hE_le_grow]
  have hen10_bd : en10 ≤ (1 + h * (61 * L)) * Emax + 2 * τabs := by
    linarith [hen10_le_E, hE_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le
    hen1_bd hen2_bd) hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd) hen9_bd)
    hen10_bd) hen11_bd

/-- Helper: 12-term Taylor polynomial in `h` for the y-remainder pattern,
representing `(m*h)•d0 + ((m*h)^2/2)•d2t + … + ((m*h)^12/479001600)•d12t`
without `d1t` (since the standard form skips the `1!` term). -/
private noncomputable def am11Vec_yPoly12
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m h : ℝ) (d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t : E) : E :=
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

/-- Helper: 11-term Taylor polynomial in `h` for the deriv-remainder pattern,
representing `(m*h)•d2t + ((m*h)^2/2)•d3t + … + ((m*h)^11/39916800)•d12t`. -/
private noncomputable def am11Vec_dPoly11
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m h : ℝ) (d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t : E) : E :=
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

/-- Param-style residual algebra identity for AM11 vector, using the packed
helpers `am11Vec_yPoly12` and `am11Vec_dPoly11` to keep witness signatures small.
Takes the thirteen Taylor-remainder structures `A B C D F G I J K L P Q R` as
abstract parameters (skipping `E` since it's the ambient module type). -/
private lemma am11Vec_residual_alg_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y0 y10 y11 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
        d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t : E) (h : ℝ)
    (A B C D F G I J K L P Q R : E)
    (hA : A = y11 - y0 - am11Vec_yPoly12 11 h d0 d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hB : B = y10 - y0 - am11Vec_yPoly12 10 h d0 d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hC : C = d11 - d0 - am11Vec_dPoly11 11 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hD : D = d10 - d0 - am11Vec_dPoly11 10 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hF : F = d9 - d0 - am11Vec_dPoly11 9 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hG : G = d8 - d0 - am11Vec_dPoly11 8 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hI : I = d7 - d0 - am11Vec_dPoly11 7 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hJ : J = d6 - d0 - am11Vec_dPoly11 6 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hK : K = d5 - d0 - am11Vec_dPoly11 5 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hL : L = d4 - d0 - am11Vec_dPoly11 4 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hP : P = d3 - d0 - am11Vec_dPoly11 3 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hQ : Q = d2 - d0 - am11Vec_dPoly11 2 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t)
    (hR : R = d1 - d0 - am11Vec_dPoly11 1 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t) :
    y11 - y10 - h • ((262747265 / 958003200 : ℝ) • d11
                  + (1374799219 / 958003200 : ℝ) • d10
                  - (2092490673 / 958003200 : ℝ) • d9
                  + (3828828885 / 958003200 : ℝ) • d8
                  - (5519460582 / 958003200 : ℝ) • d7
                  + (6043521486 / 958003200 : ℝ) • d6
                  - (4963166514 / 958003200 : ℝ) • d5
                  + (3007739418 / 958003200 : ℝ) • d4
                  - (1305971115 / 958003200 : ℝ) • d3
                  + (384709327 / 958003200 : ℝ) • d2
                  - (68928781 / 958003200 : ℝ) • d1
                  + (5675265 / 958003200 : ℝ) • d0)
      = A - B
        - (262747265 * h / 958003200 : ℝ) • C
        - (1374799219 * h / 958003200 : ℝ) • D
        + (2092490673 * h / 958003200 : ℝ) • F
        - (3828828885 * h / 958003200 : ℝ) • G
        + (5519460582 * h / 958003200 : ℝ) • I
        - (6043521486 * h / 958003200 : ℝ) • J
        + (4963166514 * h / 958003200 : ℝ) • K
        - (3007739418 * h / 958003200 : ℝ) • L
        + (1305971115 * h / 958003200 : ℝ) • P
        - (384709327 * h / 958003200 : ℝ) • Q
        + (68928781 * h / 958003200 : ℝ) • R := by
  subst hA; subst hB; subst hC; subst hD; subst hF; subst hG; subst hI
  subst hJ; subst hK; subst hL; subst hP; subst hQ; subst hR
  unfold am11Vec_yPoly12 am11Vec_dPoly11
  module

private lemma am11Vec_residual_bound_alg_identity (M h : ℝ) :
    M / 6227020800 * (11 * h) ^ 13
      + M / 6227020800 * (10 * h) ^ 13
      + (262747265 * h / 958003200) * (M / 479001600 * (11 * h) ^ 12)
      + (1374799219 * h / 958003200) * (M / 479001600 * (10 * h) ^ 12)
      + (2092490673 * h / 958003200) * (M / 479001600 * (9 * h) ^ 12)
      + (3828828885 * h / 958003200) * (M / 479001600 * (8 * h) ^ 12)
      + (5519460582 * h / 958003200) * (M / 479001600 * (7 * h) ^ 12)
      + (6043521486 * h / 958003200) * (M / 479001600 * (6 * h) ^ 12)
      + (4963166514 * h / 958003200) * (M / 479001600 * (5 * h) ^ 12)
      + (3007739418 * h / 958003200) * (M / 479001600 * (4 * h) ^ 12)
      + (1305971115 * h / 958003200) * (M / 479001600 * (3 * h) ^ 12)
      + (384709327 * h / 958003200) * (M / 479001600 * (2 * h) ^ 12)
      + (68928781 * h / 958003200) * (M / 479001600 * h ^ 12)
      = (345161607571042875013 / 24650850631680000 : ℝ) * M * h ^ 13 := by
  ring

private lemma am11Vec_triangle_aux
    {E : Type*} [NormedAddCommGroup E]
    (A B C D F G I J K L P Q R : E) :
    ‖A - B - C - D + F - G + I - J + K - L + P - Q + R‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖F‖ + ‖G‖ + ‖I‖ + ‖J‖
          + ‖K‖ + ‖L‖ + ‖P‖ + ‖Q‖ + ‖R‖ := by
  have h1 : ‖A - B - C - D + F - G + I - J + K - L + P - Q + R‖
      ≤ ‖A - B - C - D + F - G + I - J + K - L + P - Q‖ + ‖R‖ := norm_add_le _ _
  have h2 : ‖A - B - C - D + F - G + I - J + K - L + P - Q‖
      ≤ ‖A - B - C - D + F - G + I - J + K - L + P‖ + ‖Q‖ := norm_sub_le _ _
  have h3 : ‖A - B - C - D + F - G + I - J + K - L + P‖
      ≤ ‖A - B - C - D + F - G + I - J + K - L‖ + ‖P‖ := norm_add_le _ _
  have h4 : ‖A - B - C - D + F - G + I - J + K - L‖
      ≤ ‖A - B - C - D + F - G + I - J + K‖ + ‖L‖ := norm_sub_le _ _
  have h5 : ‖A - B - C - D + F - G + I - J + K‖
      ≤ ‖A - B - C - D + F - G + I - J‖ + ‖K‖ := norm_add_le _ _
  have h6 : ‖A - B - C - D + F - G + I - J‖
      ≤ ‖A - B - C - D + F - G + I‖ + ‖J‖ := norm_sub_le _ _
  have h7 : ‖A - B - C - D + F - G + I‖
      ≤ ‖A - B - C - D + F - G‖ + ‖I‖ := norm_add_le _ _
  have h8 : ‖A - B - C - D + F - G‖
      ≤ ‖A - B - C - D + F‖ + ‖G‖ := norm_sub_le _ _
  have h9 : ‖A - B - C - D + F‖ ≤ ‖A - B - C - D‖ + ‖F‖ := norm_add_le _ _
  have h10 : ‖A - B - C - D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_sub_le _ _
  have h11 : ‖A - B - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le _ _
  have h12 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith

private lemma am11Vec_residual_thirteen_term_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G I J K L P Q R : E) (h : ℝ) (hh : 0 ≤ h) :
    ‖A - B - (262747265 * h / 958003200 : ℝ) • C
        - (1374799219 * h / 958003200 : ℝ) • D
        + (2092490673 * h / 958003200 : ℝ) • F
        - (3828828885 * h / 958003200 : ℝ) • G
        + (5519460582 * h / 958003200 : ℝ) • I
        - (6043521486 * h / 958003200 : ℝ) • J
        + (4963166514 * h / 958003200 : ℝ) • K
        - (3007739418 * h / 958003200 : ℝ) • L
        + (1305971115 * h / 958003200 : ℝ) • P
        - (384709327 * h / 958003200 : ℝ) • Q
        + (68928781 * h / 958003200 : ℝ) • R‖
      ≤ ‖A‖ + ‖B‖ + (262747265 * h / 958003200) * ‖C‖
          + (1374799219 * h / 958003200) * ‖D‖
          + (2092490673 * h / 958003200) * ‖F‖
          + (3828828885 * h / 958003200) * ‖G‖
          + (5519460582 * h / 958003200) * ‖I‖
          + (6043521486 * h / 958003200) * ‖J‖
          + (4963166514 * h / 958003200) * ‖K‖
          + (3007739418 * h / 958003200) * ‖L‖
          + (1305971115 * h / 958003200) * ‖P‖
          + (384709327 * h / 958003200) * ‖Q‖
          + (68928781 * h / 958003200) * ‖R‖ := by
  have hcC_nn : 0 ≤ (262747265 * h / 958003200 : ℝ) := by linarith
  have hcD_nn : 0 ≤ (1374799219 * h / 958003200 : ℝ) := by linarith
  have hcF_nn : 0 ≤ (2092490673 * h / 958003200 : ℝ) := by linarith
  have hcG_nn : 0 ≤ (3828828885 * h / 958003200 : ℝ) := by linarith
  have hcI_nn : 0 ≤ (5519460582 * h / 958003200 : ℝ) := by linarith
  have hcJ_nn : 0 ≤ (6043521486 * h / 958003200 : ℝ) := by linarith
  have hcK_nn : 0 ≤ (4963166514 * h / 958003200 : ℝ) := by linarith
  have hcL_nn : 0 ≤ (3007739418 * h / 958003200 : ℝ) := by linarith
  have hcP_nn : 0 ≤ (1305971115 * h / 958003200 : ℝ) := by linarith
  have hcQ_nn : 0 ≤ (384709327 * h / 958003200 : ℝ) := by linarith
  have hcR_nn : 0 ≤ (68928781 * h / 958003200 : ℝ) := by linarith
  have hC_norm :
      ‖(262747265 * h / 958003200 : ℝ) • C‖
        = (262747265 * h / 958003200) * ‖C‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcC_nn]
  have hD_norm :
      ‖(1374799219 * h / 958003200 : ℝ) • D‖
        = (1374799219 * h / 958003200) * ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcD_nn]
  have hF_norm :
      ‖(2092490673 * h / 958003200 : ℝ) • F‖
        = (2092490673 * h / 958003200) * ‖F‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcF_nn]
  have hG_norm :
      ‖(3828828885 * h / 958003200 : ℝ) • G‖
        = (3828828885 * h / 958003200) * ‖G‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcG_nn]
  have hI_norm :
      ‖(5519460582 * h / 958003200 : ℝ) • I‖
        = (5519460582 * h / 958003200) * ‖I‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcI_nn]
  have hJ_norm :
      ‖(6043521486 * h / 958003200 : ℝ) • J‖
        = (6043521486 * h / 958003200) * ‖J‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcJ_nn]
  have hK_norm :
      ‖(4963166514 * h / 958003200 : ℝ) • K‖
        = (4963166514 * h / 958003200) * ‖K‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcK_nn]
  have hL_norm :
      ‖(3007739418 * h / 958003200 : ℝ) • L‖
        = (3007739418 * h / 958003200) * ‖L‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcL_nn]
  have hP_norm :
      ‖(1305971115 * h / 958003200 : ℝ) • P‖
        = (1305971115 * h / 958003200) * ‖P‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcP_nn]
  have hQ_norm :
      ‖(384709327 * h / 958003200 : ℝ) • Q‖
        = (384709327 * h / 958003200) * ‖Q‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcQ_nn]
  have hR_norm :
      ‖(68928781 * h / 958003200 : ℝ) • R‖
        = (68928781 * h / 958003200) * ‖R‖ := by
    rw [norm_smul, Real.norm_of_nonneg hcR_nn]
  have htri := am11Vec_triangle_aux A B
    ((262747265 * h / 958003200 : ℝ) • C)
    ((1374799219 * h / 958003200 : ℝ) • D)
    ((2092490673 * h / 958003200 : ℝ) • F)
    ((3828828885 * h / 958003200 : ℝ) • G)
    ((5519460582 * h / 958003200 : ℝ) • I)
    ((6043521486 * h / 958003200 : ℝ) • J)
    ((4963166514 * h / 958003200 : ℝ) • K)
    ((3007739418 * h / 958003200 : ℝ) • L)
    ((1305971115 * h / 958003200 : ℝ) • P)
    ((384709327 * h / 958003200 : ℝ) • Q)
    ((68928781 * h / 958003200 : ℝ) • R)
  rw [hC_norm, hD_norm, hF_norm, hG_norm, hI_norm, hJ_norm, hK_norm, hL_norm,
    hP_norm, hQ_norm, hR_norm] at htri
  exact htri

private lemma am11Vec_residual_combine_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B C D F G I J K L P Q R : E) (Mb h : ℝ) (hh : 0 ≤ h) (hMnn : 0 ≤ Mb)
    (hA_bd : ‖A‖ ≤ Mb / 6227020800 * (11 * h) ^ 13)
    (hB_bd : ‖B‖ ≤ Mb / 6227020800 * (10 * h) ^ 13)
    (hC_bd : ‖C‖ ≤ Mb / 479001600 * (11 * h) ^ 12)
    (hD_bd : ‖D‖ ≤ Mb / 479001600 * (10 * h) ^ 12)
    (hF_bd : ‖F‖ ≤ Mb / 479001600 * (9 * h) ^ 12)
    (hG_bd : ‖G‖ ≤ Mb / 479001600 * (8 * h) ^ 12)
    (hI_bd : ‖I‖ ≤ Mb / 479001600 * (7 * h) ^ 12)
    (hJ_bd : ‖J‖ ≤ Mb / 479001600 * (6 * h) ^ 12)
    (hK_bd : ‖K‖ ≤ Mb / 479001600 * (5 * h) ^ 12)
    (hL_bd : ‖L‖ ≤ Mb / 479001600 * (4 * h) ^ 12)
    (hP_bd : ‖P‖ ≤ Mb / 479001600 * (3 * h) ^ 12)
    (hQ_bd : ‖Q‖ ≤ Mb / 479001600 * (2 * h) ^ 12)
    (hR_bd : ‖R‖ ≤ Mb / 479001600 * h ^ 12) :
    ‖A - B - (262747265 * h / 958003200 : ℝ) • C
        - (1374799219 * h / 958003200 : ℝ) • D
        + (2092490673 * h / 958003200 : ℝ) • F
        - (3828828885 * h / 958003200 : ℝ) • G
        + (5519460582 * h / 958003200 : ℝ) • I
        - (6043521486 * h / 958003200 : ℝ) • J
        + (4963166514 * h / 958003200 : ℝ) • K
        - (3007739418 * h / 958003200 : ℝ) • L
        + (1305971115 * h / 958003200 : ℝ) • P
        - (384709327 * h / 958003200 : ℝ) • Q
        + (68928781 * h / 958003200 : ℝ) • R‖
      ≤ 14003 * Mb * h ^ 13 := by
  have htri := am11Vec_residual_thirteen_term_triangle A B C D F G I J K L P Q R h hh
  have hcC_nn : 0 ≤ 262747265 * h / 958003200 := by linarith
  have hcD_nn : 0 ≤ 1374799219 * h / 958003200 := by linarith
  have hcF_nn : 0 ≤ 2092490673 * h / 958003200 := by linarith
  have hcG_nn : 0 ≤ 3828828885 * h / 958003200 := by linarith
  have hcI_nn : 0 ≤ 5519460582 * h / 958003200 := by linarith
  have hcJ_nn : 0 ≤ 6043521486 * h / 958003200 := by linarith
  have hcK_nn : 0 ≤ 4963166514 * h / 958003200 := by linarith
  have hcL_nn : 0 ≤ 3007739418 * h / 958003200 := by linarith
  have hcP_nn : 0 ≤ 1305971115 * h / 958003200 := by linarith
  have hcQ_nn : 0 ≤ 384709327 * h / 958003200 := by linarith
  have hcR_nn : 0 ≤ 68928781 * h / 958003200 := by linarith
  have hCbd_s : (262747265 * h / 958003200) * ‖C‖
      ≤ (262747265 * h / 958003200) * (Mb / 479001600 * (11 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hC_bd hcC_nn
  have hDbd_s : (1374799219 * h / 958003200) * ‖D‖
      ≤ (1374799219 * h / 958003200) * (Mb / 479001600 * (10 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hD_bd hcD_nn
  have hFbd_s : (2092490673 * h / 958003200) * ‖F‖
      ≤ (2092490673 * h / 958003200) * (Mb / 479001600 * (9 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hF_bd hcF_nn
  have hGbd_s : (3828828885 * h / 958003200) * ‖G‖
      ≤ (3828828885 * h / 958003200) * (Mb / 479001600 * (8 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hG_bd hcG_nn
  have hIbd_s : (5519460582 * h / 958003200) * ‖I‖
      ≤ (5519460582 * h / 958003200) * (Mb / 479001600 * (7 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hI_bd hcI_nn
  have hJbd_s : (6043521486 * h / 958003200) * ‖J‖
      ≤ (6043521486 * h / 958003200) * (Mb / 479001600 * (6 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hJ_bd hcJ_nn
  have hKbd_s : (4963166514 * h / 958003200) * ‖K‖
      ≤ (4963166514 * h / 958003200) * (Mb / 479001600 * (5 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hK_bd hcK_nn
  have hLbd_s : (3007739418 * h / 958003200) * ‖L‖
      ≤ (3007739418 * h / 958003200) * (Mb / 479001600 * (4 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hL_bd hcL_nn
  have hPbd_s : (1305971115 * h / 958003200) * ‖P‖
      ≤ (1305971115 * h / 958003200) * (Mb / 479001600 * (3 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hP_bd hcP_nn
  have hQbd_s : (384709327 * h / 958003200) * ‖Q‖
      ≤ (384709327 * h / 958003200) * (Mb / 479001600 * (2 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hQ_bd hcQ_nn
  have hRbd_s : (68928781 * h / 958003200) * ‖R‖
      ≤ (68928781 * h / 958003200) * (Mb / 479001600 * h ^ 12) :=
    mul_le_mul_of_nonneg_left hR_bd hcR_nn
  have hbound_alg := am11Vec_residual_bound_alg_identity Mb h
  have hh13_nn : 0 ≤ h ^ 13 := by positivity
  have hMh13_nn : 0 ≤ Mb * h ^ 13 := mul_nonneg hMnn hh13_nn
  have hslack : (345161607571042875013 / 24650850631680000 : ℝ) * Mb * h ^ 13
      ≤ 14003 * Mb * h ^ 13 := by
    rw [mul_assoc, mul_assoc (14003 : ℝ)]
    have hle : (345161607571042875013 / 24650850631680000 : ℝ) ≤ 14003 := by
      norm_num
    exact mul_le_mul_of_nonneg_right hle hMh13_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hFbd_s,
    hGbd_s, hIbd_s, hJbd_s, hKbd_s, hLbd_s, hPbd_s, hQbd_s, hRbd_s]

theorem am11Vec_pointwise_residual_bound
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
    (hh : 0 ≤ h) :
    ‖am11VecResidual h t y‖ ≤ (14003 : ℝ) * M * h ^ 13 := by
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
  have hRy10 :=
    y_thirteenth_order_taylor_remainder_vec hy hbnd ht ht10h h10h
  have hRy11 :=
    y_thirteenth_order_taylor_remainder_vec hy hbnd ht ht11h h11h
  have hRyp1 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht9h h9h
  have hRyp10 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht10h h10h
  have hRyp11 :=
    derivY_twelfth_order_taylor_remainder_vec hy hbnd ht ht11h h11h
  unfold am11VecResidual
  set y0 : E := y t with hy0_def
  set y10 : E := y (t + 10 * h) with hy10_def
  set y11 : E := y (t + 11 * h) with hy11_def
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
  clear_value y0 y10 y11 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
    d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t
  set A : E := y11 - y0 - am11Vec_yPoly12 11 h d0 d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hA_def
  set B : E := y10 - y0 - am11Vec_yPoly12 10 h d0 d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hB_def
  set C : E := d11 - d0 - am11Vec_dPoly11 11 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hC_def
  set D : E := d10 - d0 - am11Vec_dPoly11 10 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hD_def
  set F : E := d9 - d0 - am11Vec_dPoly11 9 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hF_def
  set G : E := d8 - d0 - am11Vec_dPoly11 8 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hG_def
  set I : E := d7 - d0 - am11Vec_dPoly11 7 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hI_def
  set J : E := d6 - d0 - am11Vec_dPoly11 6 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hJ_def
  set K : E := d5 - d0 - am11Vec_dPoly11 5 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hK_def
  set L : E := d4 - d0 - am11Vec_dPoly11 4 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hL_def
  set P : E := d3 - d0 - am11Vec_dPoly11 3 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hP_def
  set Q : E := d2 - d0 - am11Vec_dPoly11 2 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hQ_def
  set R : E := d1 - d0 - am11Vec_dPoly11 1 h d2t d3t d4t d5t d6t d7t d8t
                          d9t d10t d11t d12t with hR_def
  have hLTE_eq :=
    am11Vec_residual_alg_identity y0 y10 y11 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
      d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t h A B C D F G I J K L P Q R
      hA_def hB_def hC_def hD_def hF_def hG_def hI_def hJ_def hK_def hL_def
      hP_def hQ_def hR_def
  rw [hLTE_eq]
  have hA_bd : ‖A‖ ≤ M / 6227020800 * (11 * h) ^ 13 := by
    rw [hA_def]; unfold am11Vec_yPoly12
    convert hRy11 using 2; module
  have hB_bd : ‖B‖ ≤ M / 6227020800 * (10 * h) ^ 13 := by
    rw [hB_def]; unfold am11Vec_yPoly12
    convert hRy10 using 2; module
  have hC_bd : ‖C‖ ≤ M / 479001600 * (11 * h) ^ 12 := by
    rw [hC_def]; unfold am11Vec_dPoly11
    convert hRyp11 using 2; module
  have hD_bd : ‖D‖ ≤ M / 479001600 * (10 * h) ^ 12 := by
    rw [hD_def]; unfold am11Vec_dPoly11
    convert hRyp10 using 2; module
  have hF_bd : ‖F‖ ≤ M / 479001600 * (9 * h) ^ 12 := by
    rw [hF_def]; unfold am11Vec_dPoly11
    convert hRyp9 using 2; module
  have hG_bd : ‖G‖ ≤ M / 479001600 * (8 * h) ^ 12 := by
    rw [hG_def]; unfold am11Vec_dPoly11
    convert hRyp8 using 2; module
  have hI_bd : ‖I‖ ≤ M / 479001600 * (7 * h) ^ 12 := by
    rw [hI_def]; unfold am11Vec_dPoly11
    convert hRyp7 using 2; module
  have hJ_bd : ‖J‖ ≤ M / 479001600 * (6 * h) ^ 12 := by
    rw [hJ_def]; unfold am11Vec_dPoly11
    convert hRyp6 using 2; module
  have hK_bd : ‖K‖ ≤ M / 479001600 * (5 * h) ^ 12 := by
    rw [hK_def]; unfold am11Vec_dPoly11
    convert hRyp5 using 2; module
  have hL_bd : ‖L‖ ≤ M / 479001600 * (4 * h) ^ 12 := by
    rw [hL_def]; unfold am11Vec_dPoly11
    convert hRyp4 using 2; module
  have hP_bd : ‖P‖ ≤ M / 479001600 * (3 * h) ^ 12 := by
    rw [hP_def]; unfold am11Vec_dPoly11
    convert hRyp3 using 2; module
  have hQ_bd : ‖Q‖ ≤ M / 479001600 * (2 * h) ^ 12 := by
    rw [hQ_def]; unfold am11Vec_dPoly11
    convert hRyp2 using 2; module
  have hR_bd : ‖R‖ ≤ M / 479001600 * h ^ 12 := by
    rw [hR_def]; unfold am11Vec_dPoly11
    convert hRyp1 using 2; module
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  clear_value A B C D F G I J K L P Q R
  exact am11Vec_residual_combine_aux A B C D F G I J K L P Q R M h hh hMnn
    hA_bd hB_bd hC_bd hD_bd hF_bd hG_bd hI_bd hJ_bd hK_bd hL_bd hP_bd hQ_bd hR_bd

theorem am11Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 13 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 11) * h ≤ T →
        ‖am11VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 13 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_thirteen_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(14003 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 11) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 9 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht10h_mem : t + 10 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 10 * h ≤ ((n : ℝ) + 11) * h := by nlinarith
    linarith
  have ht11h_mem : t + 11 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 11 * h = ((n : ℝ) + 11) * h := by ring
    linarith
  show ‖am11VecResidual h t y‖ ≤ 14003 * M * h ^ 13
  exact am11Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem
    ht10h_mem ht11h_mem hh.le

/-- **Adams–Moulton 11-step vector global error bound.**
For a `ContDiff ℝ 13` reference solution `y` with `deriv y t = f t (y t)`
and any AM11 trajectory `yseq` satisfying the implicit recurrence with
`(262747265/958003200)·h·L ≤ 1/2`, eleven initial errors at most `ε₀`,
and `(N+10)·h ≤ T`, the global error satisfies
`‖yseq N - y(t₀ + N·h)‖ ≤ exp(61·L·T) · ε₀ + K · h^11`. -/
theorem am11Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 13 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (262747265 / 958003200 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsAM11TrajectoryVec h f t₀ yseq →
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
      ∀ N : ℕ, ((N : ℝ) + 10) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((61 * L) * T) * ε₀ + K * h ^ 11 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am11Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((61 * L) * T) * (2 * C), min δ 1, ?_,
    lt_min hδ_pos (by norm_num), ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδg_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd he10_bd N hNh
  have hδ_le : h ≤ δ := le_trans hδg_le (min_le_left δ 1)
  have h_le_one : h ≤ 1 := le_trans hδg_le (min_le_right δ 1)
  have hh13_le_h12 : h ^ 13 ≤ h ^ 12 := by
    calc
      h ^ 13 = h ^ 12 * h := by ring
      _ ≤ h ^ 12 * 1 :=
        mul_le_mul_of_nonneg_left h_le_one (by positivity)
      _ = h ^ 12 := by ring
  set eN : ℕ → ℝ :=
    fun k => ‖yseq k - y (t₀ + (k : ℝ) * h)‖ with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (max (max (max (max (max (max
        (eN k) (eN (k + 1))) (eN (k + 2))) (eN (k + 3))) (eN (k + 4)))
        (eN (k + 5))) (eN (k + 6))) (eN (k + 7))) (eN (k + 8))) (eN (k + 9)))
        (eN (k + 10))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => norm_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
        (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
          (le_max_of_le_left (heN_nn k))))))))))
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (max (max (max (max (max (max
        (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4)) (eN 5)) (eN 6)) (eN 7)) (eN 8)) (eN 9))
        (eN 10) ≤ ε₀
    refine max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
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
    · show ‖yseq 7 - y (t₀ + ((7 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((7 : ℕ) : ℝ) * h = 7 * h := by push_cast; ring
      rw [hcast]; simpa using he7_bd
    · show ‖yseq 8 - y (t₀ + ((8 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((8 : ℕ) : ℝ) * h = 8 * h := by push_cast; ring
      rw [hcast]; simpa using he8_bd
    · show ‖yseq 9 - y (t₀ + ((9 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((9 : ℕ) : ℝ) * h = 9 * h := by push_cast; ring
      rw [hcast]; simpa using he9_bd
    · show ‖yseq 10 - y (t₀ + ((10 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((10 : ℕ) : ℝ) * h = 10 * h := by push_cast; ring
      rw [hcast]; simpa using he10_bd
  have h61L_nn : (0 : ℝ) ≤ 61 * L := by linarith
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 11) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (61 * L)) * EN n + (2 * C) * h ^ 12 := by
    intro n hnh_le
    have honestep := am11Vec_one_step_error_pair_bound
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
    have hcast8 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) =
        (n : ℝ) + 8 := by
      push_cast; ring
    have hcast9 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) =
        (n : ℝ) + 9 := by
      push_cast; ring
    have hcast10 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) =
        (n : ℝ) + 10 := by
      push_cast; ring
    have hcast11 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) =
        (n : ℝ) + 11 := by
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
    have heq_eN_n8 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast8]
    have heq_eN_n9 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast9]
    have heq_eN_n10 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast10]
    have heq_eN_n11 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = ‖yseq (n + 11) - y (t₀ + ((n : ℝ) + 11) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast11]
    show max (max (max (max (max (max (max (max (max (max
            (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * (61 * L))
            * max (max (max (max (max (max (max (max (max (max
                  (eN n) (eN (n + 1)))
                  (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
          + (2 * C) * h ^ 12
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5,
      heq_eN_n6, heq_eN_n7, heq_eN_n8, heq_eN_n9, heq_eN_n10, heq_eN_n11]
    have h2τ : 2 * ‖am11VecResidual h (t₀ + (n : ℝ) * h) y‖
        ≤ (2 * C) * h ^ 12 := by
      have h2res : 2 * ‖am11VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ 2 * (C * h ^ 13) :=
        mul_le_mul_of_nonneg_left hres (by norm_num)
      have hC2_nn : (0 : ℝ) ≤ 2 * C := by positivity
      have hweak : 2 * (C * h ^ 13) ≤ (2 * C) * h ^ 12 := by
        have := mul_le_mul_of_nonneg_left hh13_le_h12 hC2_nn
        linarith
      linarith
    linarith [honestep, h2τ]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((61 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((61 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh11_nn : 0 ≤ h ^ 11 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((61 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((61 * L) * T) * ε₀
            + T * Real.exp ((61 * L) * T) * (2 * C) * h ^ 11 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((61 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((61 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh11_nn : 0 ≤ T * Real.exp ((61 * L) * T) * (2 * C) * h ^ 11 :=
      mul_nonneg hKnn hh11_nn
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
  | 7, _ =>
    have hbase : ‖yseq 7 - y (t₀ + ((7 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((7 : ℕ) : ℝ) * h = 7 * h := by push_cast; ring
      rw [hcast]; simpa using he7_bd
    exact hbase_to_headline _ hbase
  | 8, _ =>
    have hbase : ‖yseq 8 - y (t₀ + ((8 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((8 : ℕ) : ℝ) * h = 8 * h := by push_cast; ring
      rw [hcast]; simpa using he8_bd
    exact hbase_to_headline _ hbase
  | 9, _ =>
    have hbase : ‖yseq 9 - y (t₀ + ((9 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((9 : ℕ) : ℝ) * h = 9 * h := by push_cast; ring
      rw [hcast]; simpa using he9_bd
    exact hbase_to_headline _ hbase
  | 10, _ =>
    have hbase : ‖yseq 10 - y (t₀ + ((10 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((10 : ℕ) : ℝ) * h = 10 * h := by push_cast; ring
      rw [hcast]; simpa using he10_bd
    exact hbase_to_headline _ hbase
  | N' + 11, hNh =>
    have hcast : (((N' + 11 : ℕ) : ℝ) + 10) = (N' : ℝ) + 21 := by
      push_cast; ring
    have hN_hyp : ((N' : ℝ) + 21) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (61 * L)) * EN n + (2 * C) * h ^ (11 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (11 + 1) = (2 * C) * h ^ 12 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 11 ≤ (N' : ℝ) + 21 := by linarith
      have h_mul : ((n : ℝ) + 11) * h ≤ ((N' : ℝ) + 21) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have hle : (N' : ℝ) + 1 ≤ (N' : ℝ) + 21 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 61 * L) (C := 2 * C) (T := T) (p := 11)
        (e := EN) (N := N' + 1)
        hh.le h61L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 11) ≤ EN (N' + 1) := by
      show eN (N' + 11)
        ≤ max (max (max (max (max (max (max (max (max (max
              (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4)))
              (eN (N' + 1 + 5))) (eN (N' + 1 + 6))) (eN (N' + 1 + 7)))
              (eN (N' + 1 + 8))) (eN (N' + 1 + 9))) (eN (N' + 1 + 10))
      have heq : N' + 11 = N' + 1 + 10 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((61 * L) * T) * EN 0 ≤ Real.exp ((61 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show ‖yseq (N' + 11) - y (t₀ + ((N' + 11 : ℕ) : ℝ) * h)‖
        ≤ Real.exp ((61 * L) * T) * ε₀
          + T * Real.exp ((61 * L) * T) * (2 * C) * h ^ 11
    have heN_eq :
        eN (N' + 11)
          = ‖yseq (N' + 11) - y (t₀ + ((N' + 11 : ℕ) : ℝ) * h)‖ := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
