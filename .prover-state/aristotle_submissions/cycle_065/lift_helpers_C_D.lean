import Mathlib

open scoped NNReal Topology

/-! # Cycle 065 §406B helpers C and D — non-autonomous lift

This file is a standalone Aristotle submission for second-opinion
proofs of `residual_bound_nonauto` (helper C) and
`deriv_diff_bound_nonauto` (helper D), the cycle 065 non-autonomous
lifts of the Butcher §406B sub-lemmas C and D. Both are proved
manually in `OpenMath/Chapter4/Section404.lean` (cycle 065 commit);
this submission asks Aristotle for alternative proofs.

The full chain depends on three helpers, which are included with
their manual proofs:
* `joint_lipschitz_pair_bound` (cycle 065).
* `exact_solution_norm_bound_nonauto` (cycle 064).
* `residual_integral_form_nonauto` (cycle 064).

Targets (cycle 065): `residual_bound_nonauto`,
`deriv_diff_bound_nonauto`. -/

/-- **Joint-Lipschitz product-distance bound (cycle 065 helper).**
For a jointly Lipschitz `f : ℝ → ℝ → ℝ`, bound `|f t₁ y₁ − f t₂ y₂|`
by `L_joint · (|t₁ − t₂| + |y₁ − y₂|)`. -/
private lemma joint_lipschitz_pair_bound
    {f : ℝ → ℝ → ℝ} {L_joint : ℝ}
    (hL_joint : 0 ≤ L_joint)
    (hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f))
    (t₁ y₁ t₂ y₂ : ℝ) :
    |f t₁ y₁ - f t₂ y₂| ≤ L_joint * (|t₁ - t₂| + |y₁ - y₂|) := by
  have hd := hf_lip_joint.dist_le_mul (t₁, y₁) (t₂, y₂)
  simp only [Function.uncurry_apply_pair] at hd
  rw [Real.dist_eq] at hd
  rw [show ((Real.toNNReal L_joint : ℝ≥0) : ℝ) = L_joint from
        Real.coe_toNNReal L_joint hL_joint] at hd
  have hprod : dist ((t₁, y₁) : ℝ × ℝ) (t₂, y₂)
                ≤ |t₁ - t₂| + |y₁ - y₂| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _))
                 (le_add_of_nonneg_left (abs_nonneg _))
  exact hd.trans (mul_le_mul_of_nonneg_left hprod hL_joint)

/-- **Sub-lemma A non-autonomous lift (cycle 064)**. -/
private lemma exact_solution_norm_bound_nonauto
    {f : ℝ → ℝ → ℝ} {M_bound : ℝ} (_hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f t (y t))
    (hf_y_bound : ∀ t, |f t (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h)
    (ξ : ℝ) (hξ : ξ ≤ 0) :
    |y (x + h * ξ) - y x| ≤ h * (-ξ) * M_bound := by
  have hfy_cont : Continuous (fun t => f t (y t)) := by
    have heq : (fun t => f t (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]
    exact hy_C1.continuous_deriv le_rfl
  have hderiv : ∀ t, HasDerivAt y (f t (y t)) t := by
    intro t
    have hdiff := (hy_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) t
    have ht := hdiff.hasDerivAt
    rw [hy_ode t] at ht
    exact ht
  have hint : IntervalIntegrable (fun t => f t (y t)) MeasureTheory.volume
                x (x + h * ξ) := hfy_cont.intervalIntegrable _ _
  have hFTC : ∫ t in x..(x + h * ξ), f t (y t) = y (x + h * ξ) - y x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
  have hC : ∀ t ∈ Set.uIoc x (x + h * ξ), ‖f t (y t)‖ ≤ M_bound := by
    intro t _
    rw [Real.norm_eq_abs]
    exact hf_y_bound t
  have hbound :
      |∫ t in x..(x + h * ξ), f t (y t)| ≤ M_bound * |h * ξ| := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hC
    rw [Real.norm_eq_abs] at hb
    have hsub : (x + h * ξ) - x = h * ξ := by ring
    rw [hsub] at hb
    exact hb
  rw [hFTC] at hbound
  have habs : |h * ξ| = h * (-ξ) := by
    rw [abs_mul, abs_of_nonneg hh, abs_of_nonpos hξ]
  rw [habs] at hbound
  calc |y (x + h * ξ) - y x|
      ≤ M_bound * (h * (-ξ)) := hbound
    _ = h * (-ξ) * M_bound := by ring

/-- **Sub-lemma B non-autonomous lift (cycle 064)**. -/
private lemma residual_integral_form_nonauto
    {f : ℝ → ℝ → ℝ} {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f t (y t))
    (i : ℕ) (x h : ℝ) (_hh : 0 ≤ h) :
    y x - y (x - (i : ℝ) * h) - ((i : ℝ) * h) * deriv y x
      = h * ∫ ξ in (-(i : ℝ))..0,
                (f (x + h*ξ) (y (x + h*ξ)) - f x (y x)) := by
  have hfy_cont : Continuous (fun t => f t (y t)) := by
    have heq : (fun t => f t (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]
    exact hy_C1.continuous_deriv le_rfl
  have hderiv : ∀ t, HasDerivAt y (f t (y t)) t := by
    intro t
    have hdiff := (hy_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) t
    have ht := hdiff.hasDerivAt
    rw [hy_ode t] at ht
    exact ht
  have hfy_int : ∀ a b : ℝ,
      IntervalIntegrable (fun t => f t (y t)) MeasureTheory.volume a b :=
    fun a b => hfy_cont.intervalIntegrable a b
  have hfyhx_cont : Continuous (fun ξ : ℝ => f (x + h * ξ) (y (x + h * ξ))) := by
    have hlin : Continuous (fun ξ : ℝ => x + h * ξ) := by fun_prop
    exact hfy_cont.comp hlin
  have hfyhx_int : IntervalIntegrable
                     (fun ξ : ℝ => f (x + h * ξ) (y (x + h * ξ)))
                     MeasureTheory.volume (-(i : ℝ)) 0 :=
    hfyhx_cont.intervalIntegrable _ _
  have hfyx_int : IntervalIntegrable (fun _ : ℝ => f x (y x))
                     MeasureTheory.volume (-(i : ℝ)) 0 :=
    continuous_const.intervalIntegrable _ _
  have hFTC : ∫ t in (x - (i : ℝ) * h)..x, f t (y t)
                = y x - y (x - (i : ℝ) * h) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) (hfy_int _ _)
  have hCV : h * ∫ ξ in (-(i : ℝ))..0, f (x + h * ξ) (y (x + h * ξ))
              = ∫ t in (x - (i : ℝ) * h)..x, f t (y t) := by
    have hCV0 := intervalIntegral.smul_integral_comp_mul_add
                    (fun t => f t (y t)) (a := -(i : ℝ)) (b := 0)
                    h x
    have heq_l : h * (-(i : ℝ)) + x = x - (i : ℝ) * h := by ring
    have heq_r : h * (0 : ℝ) + x = x := by ring
    have hbody : (fun ξ : ℝ => f (h * ξ + x) (y (h * ξ + x)))
                  = (fun ξ : ℝ => f (x + h * ξ) (y (x + h * ξ))) := by
      funext ξ; rw [add_comm (h * ξ) x]
    rw [smul_eq_mul, hbody, heq_l, heq_r] at hCV0
    exact hCV0
  have hConst : ∫ _ in (-(i : ℝ))..(0 : ℝ), f x (y x) = (i : ℝ) * f x (y x) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [intervalIntegral.integral_sub hfyhx_int hfyx_int]
  rw [hConst, mul_sub, hCV, hFTC, hy_ode x]
  ring

/-- **TARGET (cycle 065): residual_bound_nonauto.**

Sub-lemma C, non-autonomous lift: bound on
`|y(x) − y(x − i*h) − i*h*y'(x)|` under non-autonomous IVP
hypotheses, using joint-Lipschitz on `Function.uncurry f`. -/
theorem residual_bound_nonauto
    {f : ℝ → ℝ → ℝ} {L_joint M_bound : ℝ}
    (hL_joint : 0 ≤ L_joint) (hM : 0 ≤ M_bound)
    (hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f))
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f t (y t))
    (hf_y_bound : ∀ t, |f t (y t)| ≤ M_bound)
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    |y x - y (x - (i : ℝ) * h) - ((i : ℝ) * h) * deriv y x|
      ≤ (1/2) * (i : ℝ)^2 * h^2 * L_joint * (1 + M_bound) := by
  sorry

/-- **TARGET (cycle 065): deriv_diff_bound_nonauto.**

Sub-lemma D, non-autonomous lift: Lipschitz bound on
`|y'(x) − y'(x − i*h)|`, using joint-Lipschitz on
`Function.uncurry f`. -/
theorem deriv_diff_bound_nonauto
    {f : ℝ → ℝ → ℝ} {L_joint M_bound : ℝ}
    (hL_joint : 0 ≤ L_joint) (hM : 0 ≤ M_bound)
    (hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f))
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f t (y t))
    (hf_y_bound : ∀ t, |f t (y t)| ≤ M_bound)
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    |deriv y x - deriv y (x - (i : ℝ) * h)|
      ≤ (i : ℝ) * h * L_joint * (1 + M_bound) := by
  sorry
