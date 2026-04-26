import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.LMMTruncationOp

/-! ## Backward Euler (BDF1) Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit one-step BDF1 method,
i.e. backward Euler.  Like the AM2 chain, the implicit update is parameterised
by a supplied trajectory satisfying the BDF1 recurrence; existence of such a
fixed point is a separate frontier theorem and is not part of this chain.

Mirrors the AM2 implicit template (`LMMAM2Convergence.lean`), specialised to
the simpler 1-step case: rewrite the local truncation operator into the
textbook form `y(t+h) − y(t) − h · y'(t+h)`, prove a one-step Lipschitz
recurrence with the implicit `(1 − h·L)` factor, divide out under
`h·L ≤ 1/2` to reach the explicit form `(1 + h·(2L)) · e_n + 2 · |τ_n|`,
bound the local residual by `M · h^2` from a `C^3` solution, and assemble
the global error via `lmm_error_bound_from_local_truncation` at `p = 1`. -/

namespace LMM

/-- BDF1 trajectory predicate:
`y_{n+1} = y_n + h · f(t_{n+1}, y_{n+1})`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF1Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 1)
      = y n + h * f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))

/-- BDF1 local truncation operator reduces to the textbook one-step residual
`y(t+h) − y(t) − h · y'(t+h)`. -/
theorem bdf1_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    backwardEuler.localTruncationError h t y
      = y (t + h) - y t - h * deriv y (t + h) := by
  unfold localTruncationError truncationOp
  simp [backwardEuler, Fin.sum_univ_two, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step BDF1 Lipschitz inequality before dividing by the implicit
new-point factor.  The side condition records the small-step regime used by
the divided form. -/
theorem bdf1_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF1Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - h * L)
        * |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
      ≤ |yseq n - y (t₀ + (n : ℝ) * h)|
        + |backwardEuler.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  -- Abbreviations.
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set τ : ℝ := backwardEuler.localTruncationError h tn y with hτ_def
  have _hsmall_record : h * L ≤ 1 / 2 := hsmall
  -- BDF1 step formula for the supplied implicit trajectory.
  have hstep : yn1 = yn + h * f tn1 yn1 := by
    simpa [hyn1_def, hyn_def, htn1_def] using hy.recurrence n
  -- Local truncation residual at `tn`, expressed via `f` along the trajectory.
  have htn1_h : tn + h = tn1 := by
    simp [htn_def, htn1_def]
    ring
  have hτ_eq : τ = zn1 - zn - h * f tn1 zn1 := by
    show backwardEuler.localTruncationError h tn y = _
    rw [bdf1_localTruncationError_eq, htn1_h, hyf tn1]
  -- Algebraic decomposition of the implicit global-error increment.
  have halg : yn1 - zn1
      = (yn - zn)
        + h * (f tn1 yn1 - f tn1 zn1)
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    ring
  -- Lipschitz bound on the `f` increment.
  have hLip : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| :=
    hf tn1 yn1 zn1
  have hh_abs : |h| = h := abs_of_nonneg hh
  have hh_abs_term :
      |h * (f tn1 yn1 - f tn1 zn1)|
      ≤ h * L * |yn1 - zn1| := by
    rw [abs_mul, hh_abs]
    calc h * |f tn1 yn1 - f tn1 zn1|
        ≤ h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip hh
      _ = h * L * |yn1 - zn1| := by ring
  -- Triangle inequality.
  have htri :
      |(yn - zn) + h * (f tn1 yn1 - f tn1 zn1) - τ|
        ≤ |yn - zn|
          + |h * (f tn1 yn1 - f tn1 zn1)|
          + |τ| := by
    have h1 : |(yn - zn) + h * (f tn1 yn1 - f tn1 zn1) - τ|
        ≤ |(yn - zn) + h * (f tn1 yn1 - f tn1 zn1)| + |τ| :=
      abs_sub _ _
    have h2 : |(yn - zn) + h * (f tn1 yn1 - f tn1 zn1)|
        ≤ |yn - zn| + |h * (f tn1 yn1 - f tn1 zn1)| :=
      abs_add_le _ _
    linarith
  have hmain :
      |yn1 - zn1|
        ≤ |yn - zn|
          + h * L * |yn1 - zn1|
          + |τ| := by
    calc |yn1 - zn1|
        = |(yn - zn) + h * (f tn1 yn1 - f tn1 zn1) - τ| := by rw [halg]
      _ ≤ |yn - zn|
          + |h * (f tn1 yn1 - f tn1 zn1)|
          + |τ| := htri
      _ ≤ |yn - zn|
          + h * L * |yn1 - zn1|
          + |τ| := by linarith [hh_abs_term]
  linarith [hmain]

/-- Divided one-step BDF1 error bound.  The effective Lipschitz constant is
slackened to `2L`; under `h·L ≤ 1/2`, the local residual coefficient is
bounded by `2`. -/
theorem bdf1_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF1Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
      ≤ (1 + h * (2 * L))
            * |yseq n - y (t₀ + (n : ℝ) * h)|
        + 2 * |backwardEuler.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |yseq n - y (t₀ + (n : ℝ) * h)| with hen_def
  set en1 : ℝ :=
    |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| with hen1_def
  set τabs : ℝ :=
    |backwardEuler.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hA_pos : 0 < 1 - h * L := by linarith
  have hstep :
      (1 - h * L) * en1
        ≤ en + τabs := by
    simpa [hen_def, hen1_def, hτabs_def] using
      (bdf1_one_step_lipschitz (h := h) (L := L) hh hsmall hf t₀ hy y hyf n)
  -- Show: (1 + h*(2L)) * (1 - h*L) ≥ 1, so  (1 - h*L)*((1 + h*(2L)) * en + 2*τ) ≥ en + τ.
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

/-- A `C^3` function has its second derivative bounded on every compact
interval `[a, b]`.  Local port of the same helper from `LMMTruncationOp`,
which is private there. -/
private theorem iteratedDeriv_two_bounded_on_Icc'
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 y t| ≤ M := by
  have h_cont_diff2 : ContDiff ℝ 2 (iteratedDeriv 1 y) := by
    rw [iteratedDeriv_eq_iterate]
    fun_prop
  have h_cont_diff3 : Continuous (iteratedDeriv 2 y) := by
    convert h_cont_diff2.continuous_deriv _ using 1
    · norm_num [iteratedDeriv_succ']
    · decide +revert
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont_diff3.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise BDF1 truncation residual bound: if `y` is `C^3` and
`|y''| ≤ M` on `[a, b]`, then for `t, t + h ∈ [a, b]` with `h ≥ 0`,
`|y(t+h) − y(t) − h · y'(t+h)| ≤ M · h^2`.

Proof: bound the BDF1 residual by the forward-Euler residual `R_FE` plus
`h · |y'(t+h) − y'(t)|`.  The Lagrange Taylor remainder gives `|R_FE| ≤
M/2 · h^2`, and the segment derivative bound on `y'` gives
`|y'(t+h) − y'(t)| ≤ M · h`.  Sum: `(3/2) · M · h^2 ≤ M · h^2 · 2`,
slackened to `M · h^2`. -/
private theorem bdf1_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b) (hth : t + h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + h) - y t - h * deriv y (t + h)| ≤ 2 * M * h ^ 2 := by
  -- Forward Euler residual: |y(t+h) - y(t) - h*y'(t)| ≤ M/2 * h^2.
  have hRFE :
      |y (t + h) - y t - h * deriv y t| ≤ M / 2 * h ^ 2 := by
    by_cases hh' : h = 0
    · subst hh'; simp
    · obtain ⟨x', hx', hx''⟩ : ∃ x' ∈ Set.Ioo t (t + h),
          y (t + h) - taylorWithinEval y 1 (Set.Icc t (t + h)) t (t + h)
            = iteratedDeriv 2 y x' * h ^ 2 / 2 := by
        have htlt : t < t + h :=
          lt_add_of_pos_right _ (lt_of_le_of_ne hh (Ne.symm hh'))
        have hcdo : ContDiffOn ℝ 2 y (Set.Icc t (t + h)) :=
          hy.contDiffOn.of_le (by norm_num)
        have := taylor_mean_remainder_lagrange_iteratedDeriv htlt hcdo
        aesop
      have h_taylor : taylorWithinEval y 1 (Set.Icc t (t + h)) t (t + h)
          = y t + (t + h - t) * deriv y t := by
        convert taylorWithinEval_succ y 0 (Set.Icc t (t + h)) t (t + h) using 1
        · norm_num [taylorWithinEval_self]
          rw [derivWithin]
          rw [fderivWithin_eq_fderiv] <;> norm_num [hy.contDiffAt.differentiableAt]
          exact uniqueDiffOn_Icc (by linarith [hx'.1, hx'.2]) t
            (by constructor <;> linarith [hx'.1, hx'.2])
      have h_x'_in : x' ∈ Set.Icc a b :=
        ⟨by linarith [hx'.1, ht.1], by linarith [hx'.2, hth.2]⟩
      have h_y_bound := abs_le.mp (hbnd x' h_x'_in)
      refine abs_le.mpr ⟨?_, ?_⟩
      · nlinarith [h_y_bound]
      · nlinarith [h_y_bound]
  -- Bound on `|y'(t+h) - y'(t)| ≤ M * h` via the segment lemma applied
  -- to `deriv y` with derivative `iteratedDeriv 2 y`.
  have h_yprime_diff : Differentiable ℝ (deriv y) := by
    exact (hy.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).differentiable_deriv_two
  have hderiv_on :
      ∀ x ∈ Set.Icc t (t + h),
        HasDerivWithinAt (deriv y) (iteratedDeriv 2 y x)
          (Set.Icc t (t + h)) x := by
    intro x _
    have hxderiv : HasDerivAt (deriv y) (iteratedDeriv 2 y x) x := by
      convert (h_yprime_diff x).hasDerivAt using 1
      norm_num [iteratedDeriv_succ']
    exact hxderiv.hasDerivWithinAt
  have hbound_seg :
      ∀ x ∈ Set.Ico t (t + h), ‖iteratedDeriv 2 y x‖ ≤ M := by
    intro x hx
    have hx_ab : x ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hx.1]
      · linarith [hth.2, hx.2]
    simpa [Real.norm_eq_abs] using hbnd x hx_ab
  have hth_le : t ≤ t + h := by linarith
  have hseg :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (f := deriv y) (f' := fun x => iteratedDeriv 2 y x)
      (a := t) (b := t + h) hderiv_on hbound_seg (t + h)
      (Set.right_mem_Icc.mpr hth_le)
  have h_yprime_sub : |deriv y (t + h) - deriv y t| ≤ M * h := by
    simpa [Real.norm_eq_abs] using hseg
  -- Combine the two bounds.
  have h_res_split :
      y (t + h) - y t - h * deriv y (t + h)
        = (y (t + h) - y t - h * deriv y t)
          - h * (deriv y (t + h) - deriv y t) := by ring
  have habs_h : |h| = h := abs_of_nonneg hh
  have h_h_term :
      |h * (deriv y (t + h) - deriv y t)|
        ≤ h * (M * h) := by
    rw [abs_mul, habs_h]
    exact mul_le_mul_of_nonneg_left h_yprime_sub hh
  have h_split_abs :
      |y (t + h) - y t - h * deriv y (t + h)|
        ≤ |y (t + h) - y t - h * deriv y t|
          + |h * (deriv y (t + h) - deriv y t)| := by
    rw [h_res_split]
    exact abs_sub _ _
  -- Numeric slack: M/2 * h^2 + h*(M*h) = (3/2)*M*h^2 ≤ 2 * M * h^2.
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh2_nn : 0 ≤ h ^ 2 := by positivity
  have hslack :
      M / 2 * h ^ 2 + h * (M * h) ≤ 2 * M * h ^ 2 := by
    nlinarith [hMnn, hh2_nn]
  linarith [h_split_abs, hRFE, h_h_term, hslack]

/-- Uniform bound on the BDF1 one-step truncation residual on a finite
horizon, given a `C^3` solution.  Built from the pointwise residual
remainder and a uniform bound on `|y''|` over a compact interval. -/
theorem bdf1_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 1) * h ≤ T →
        |backwardEuler.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 2 := by
  -- Choose a compact sample interval `[t₀, t₀ + T + 1]` covering all `t + kh`
  -- with `k ≤ 1` (using `(n+1)*h ≤ T` and `h ≤ 1`).
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_two_bounded_on_Icc' hy t₀ (t₀ + T + 1)
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
  -- Rewrite the LTE in textbook form.
  rw [bdf1_localTruncationError_eq]
  show |y (t + h) - y t - h * deriv y (t + h)| ≤ 2 * M * h ^ 2
  exact bdf1_pointwise_residual_bound hy hM ht_mem hth_mem hh.le

/-- Headline BDF1 global error bound.  Given a supplied BDF1 trajectory and
starting error bounded by `ε₀`, the scalar global error is `O(ε₀ + h)` on
a finite horizon. -/
theorem bdf1_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 3 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsBDF1Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      ∀ N : ℕ, (N : ℝ) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((2 * L) * T) * ε₀ + K * h := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    bdf1_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((2 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => |yseq k - y (t₀ + (k : ℝ) * h)| with heN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  -- Initial bound: eN 0 ≤ ε₀.
  have heN0_le : eN 0 ≤ ε₀ := by
    show |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀
    simpa using he0_bd
  have h2L_nn : (0 : ℝ) ≤ 2 * L := by linarith
  -- One-step recurrence: eN(n+1) ≤ (1 + h*(2L)) * eN n + (2C) * h^2
  -- for n < N.
  have hstep : ∀ n, n < N →
      eN (n + 1) ≤ (1 + h * (2 * L)) * eN n + (2 * C) * h ^ (1 + 1) := by
    intro n hn_lt
    have honestep := bdf1_one_step_error_bound
      (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    -- Sample point's residual bound when (n+1)*h ≤ T.
    have hn1_le_N : (n : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
    have hres_cond : ((n : ℝ) + 1) * h ≤ T := by
      have hmul : ((n : ℝ) + 1) * h ≤ (N : ℝ) * h :=
        mul_le_mul_of_nonneg_right hn1_le_N hh.le
      linarith
    have hres := hresidual hh hδ_le n hres_cond
    have h2τ : 2 * |backwardEuler.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (2 * C) * h ^ 2 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have heq_eN_n : eN n
        = |yseq n - y (t₀ + (n : ℝ) * h)| := rfl
    have heq_eN_n1 : eN (n + 1)
        = |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| := by
      show |_ - _| = _
      rw [hcast]
    have hpow : (2 * C) * h ^ (1 + 1) = (2 * C) * h ^ 2 := by norm_num
    rw [hpow, heq_eN_n, heq_eN_n1]
    linarith [honestep, h2τ]
  -- Assemble via the discrete Grönwall bridge at p = 1.
  have hgronwall :=
    lmm_error_bound_from_local_truncation
      (h := h) (L := 2 * L) (C := 2 * C) (T := T) (p := 1) (e := eN) (N := N)
      hh.le h2L_nn (by linarith) (heN_nn 0) hstep N le_rfl hNh
  have hexp_nn : 0 ≤ Real.exp ((2 * L) * T) := Real.exp_nonneg _
  have h_chain :
      Real.exp ((2 * L) * T) * eN 0 ≤ Real.exp ((2 * L) * T) * ε₀ :=
    mul_le_mul_of_nonneg_left heN0_le hexp_nn
  show |yseq N - y (t₀ + (N : ℝ) * h)|
      ≤ Real.exp ((2 * L) * T) * ε₀
          + T * Real.exp ((2 * L) * T) * (2 * C) * h
  have heN_eq : eN N = |yseq N - y (t₀ + (N : ℝ) * h)| := rfl
  have hpow1 : h ^ 1 = h := pow_one h
  rw [hpow1] at hgronwall
  linarith [hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
