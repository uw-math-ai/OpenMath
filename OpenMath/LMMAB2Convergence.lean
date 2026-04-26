import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence

/-! ## Adams–Bashforth 2-step Convergence Chain (Iserles §1.2)

Order-2 explicit 2-step LMM convergence. Mirrors the forward-Euler chain
in `OpenMath.LMMTruncationOp`: defines the iteration with two starting
samples, rewrites the local truncation operator in textbook form, proves
a max-norm Lipschitz one-step recurrence, bounds the local residual, and
assembles the global error via `lmm_error_bound_from_local_truncation`.

This file was extracted from `OpenMath/LMMTruncationOp.lean` in cycle 414
to keep the per-file size under the 3000-line cap. No proofs were
modified during the move. -/

namespace LMM

variable {s : ℕ}

/-! ### Adams–Bashforth 2-step convergence chain (Iserles §1.2)

Order-2 explicit 2-step LMM. We mirror the forward-Euler chain: define
the iteration with two starting samples, rewrite the local truncation
operator in textbook form, prove a max-norm Lipschitz one-step
recurrence, bound the local residual, and assemble the global error via
`lmm_error_bound_from_local_truncation`. -/

/-- AB2 iteration with two starting samples `y₀, y₁`:
`y_{n+2} = y_{n+1} + h · (3/2 · f(t_{n+1}, y_{n+1}) − 1/2 · f(t_n, y_n))`. -/
noncomputable def ab2Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | n + 2 =>
      ab2Iter h f t₀ y₀ y₁ (n + 1)
        + h * (3 / 2 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab2Iter h f t₀ y₀ y₁ (n + 1))
              - 1 / 2 * f (t₀ + (n : ℝ) * h)
                (ab2Iter h f t₀ y₀ y₁ n))

@[simp] lemma ab2Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ : ℝ) :
    ab2Iter h f t₀ y₀ y₁ 0 = y₀ := rfl

@[simp] lemma ab2Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ : ℝ) :
    ab2Iter h f t₀ y₀ y₁ 1 = y₁ := rfl

lemma ab2Iter_succ_succ
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ : ℝ) (n : ℕ) :
    ab2Iter h f t₀ y₀ y₁ (n + 2)
      = ab2Iter h f t₀ y₀ y₁ (n + 1)
          + h * (3 / 2 * f (t₀ + ((n : ℝ) + 1) * h)
                  (ab2Iter h f t₀ y₀ y₁ (n + 1))
                - 1 / 2 * f (t₀ + (n : ℝ) * h)
                  (ab2Iter h f t₀ y₀ y₁ n)) := rfl

/-- AB2 local truncation operator reduces to the textbook 2-step residual
`y(t + 2h) − y(t + h) − h · (3/2 · y'(t + h) − 1/2 · y'(t))`. -/
theorem ab2_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth2.localTruncationError h t y
      = y (t + 2 * h) - y (t + h)
          - h * (3 / 2 * deriv y (t + h) - 1 / 2 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth2, Fin.sum_univ_three, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AB2 Lipschitz step (without max-norm bookkeeping): a single
linearised increment of the global error from steps `n, n+1` to `n+2`,
with two Lipschitz contributions and additive `|τ_n|`. -/
theorem ab2_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab2Iter h f t₀ y₀ y₁ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
      ≤ |ab2Iter h f t₀ y₀ y₁ (n + 1)
            - y (t₀ + ((n : ℝ) + 1) * h)|
        + (3 / 2) * h * L
            * |ab2Iter h f t₀ y₀ y₁ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
        + (1 / 2) * h * L
            * |ab2Iter h f t₀ y₀ y₁ n - y (t₀ + (n : ℝ) * h)|
        + |adamsBashforth2.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  -- Abbreviations.
  set yn : ℝ := ab2Iter h f t₀ y₀ y₁ n with hyn_def
  set yn1 : ℝ := ab2Iter h f t₀ y₀ y₁ (n + 1) with hyn1_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set τ : ℝ := adamsBashforth2.localTruncationError h tn y with hτ_def
  -- AB2 step formula.
  have hstep : ab2Iter h f t₀ y₀ y₁ (n + 2)
      = yn1 + h * (3 / 2 * f tn1 yn1 - 1 / 2 * f tn yn) := by
    show ab2Iter h f t₀ y₀ y₁ (n + 2) = _
    rw [ab2Iter_succ_succ]
  -- Local truncation residual at `tn`, expressed via `f` along the trajectory.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have hτ_eq : τ = zn2 - zn1 - h * (3 / 2 * f tn1 zn1 - 1 / 2 * f tn zn) := by
    show adamsBashforth2.localTruncationError h tn y = _
    rw [ab2_localTruncationError_eq, htn1_h, htn_2h, hyf tn1, hyf tn]
  -- Algebraic decomposition of the global error increment.
  have halg : ab2Iter h f t₀ y₀ y₁ (n + 2) - zn2
      = (yn1 - zn1)
        + (3 / 2) * h * (f tn1 yn1 - f tn1 zn1)
        - (1 / 2) * h * (f tn yn - f tn zn)
        - τ := by
    rw [hstep, hτ_eq]; ring
  -- Lipschitz bounds on the two `f` increments.
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| := hf tn1 yn1 zn1
  have hLip2 : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  have h32_nn : 0 ≤ (3 / 2) * h := by linarith
  have h12_nn : 0 ≤ (1 / 2) * h := by linarith
  have h32_abs : |(3 / 2) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (3 / 2) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h32_nn]
    calc (3 / 2) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (3 / 2) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h32_nn
      _ = (3 / 2) * h * L * |yn1 - zn1| := by ring
  have h12_abs : |(1 / 2) * h * (f tn yn - f tn zn)|
      ≤ (1 / 2) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h12_nn]
    calc (1 / 2) * h * |f tn yn - f tn zn|
        ≤ (1 / 2) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip2 h12_nn
      _ = (1 / 2) * h * L * |yn - zn| := by ring
  -- Triangle inequality.
  have htri :
      |(yn1 - zn1)
        + (3 / 2) * h * (f tn1 yn1 - f tn1 zn1)
        - (1 / 2) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn1 - zn1|
          + |(3 / 2) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(1 / 2) * h * (f tn yn - f tn zn)|
          + |τ| := by
    have h1 :
        |(yn1 - zn1)
          + (3 / 2) * h * (f tn1 yn1 - f tn1 zn1)
          - (1 / 2) * h * (f tn yn - f tn zn)
          - τ|
          ≤ |(yn1 - zn1)
              + (3 / 2) * h * (f tn1 yn1 - f tn1 zn1)
              - (1 / 2) * h * (f tn yn - f tn zn)|
            + |τ| := abs_sub _ _
    have h2 :
        |(yn1 - zn1)
          + (3 / 2) * h * (f tn1 yn1 - f tn1 zn1)
          - (1 / 2) * h * (f tn yn - f tn zn)|
          ≤ |(yn1 - zn1)
              + (3 / 2) * h * (f tn1 yn1 - f tn1 zn1)|
            + |(1 / 2) * h * (f tn yn - f tn zn)| := abs_sub _ _
    have h3 :
        |(yn1 - zn1) + (3 / 2) * h * (f tn1 yn1 - f tn1 zn1)|
          ≤ |yn1 - zn1| + |(3 / 2) * h * (f tn1 yn1 - f tn1 zn1)| :=
      abs_add_le _ _
    linarith
  calc |ab2Iter h f t₀ y₀ y₁ (n + 2) - zn2|
      = |(yn1 - zn1)
          + (3 / 2) * h * (f tn1 yn1 - f tn1 zn1)
          - (1 / 2) * h * (f tn yn - f tn zn)
          - τ| := by rw [halg]
    _ ≤ |yn1 - zn1|
          + |(3 / 2) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(1 / 2) * h * (f tn yn - f tn zn)|
          + |τ| := htri
    _ ≤ |yn1 - zn1|
          + (3 / 2) * h * L * |yn1 - zn1|
          + (1 / 2) * h * L * |yn - zn|
          + |τ| := by linarith [h32_abs, h12_abs]

/-- Max-norm one-step error recurrence for AB2 with Lipschitz constant
`L`. With `eN k := |y_k − y(t_k)|` and `EN k := max (eN k) (eN (k+1))`,
`EN (n+1) ≤ (1 + h · 2L) · EN n + |τ_n|`. -/
theorem ab2_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max |ab2Iter h f t₀ y₀ y₁ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
        |ab2Iter h f t₀ y₀ y₁ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
      ≤ (1 + h * (2 * L))
            * max |ab2Iter h f t₀ y₀ y₁ n - y (t₀ + (n : ℝ) * h)|
                  |ab2Iter h f t₀ y₀ y₁ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)|
        + |adamsBashforth2.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |ab2Iter h f t₀ y₀ y₁ n - y (t₀ + (n : ℝ) * h)| with hen_def
  set en1 : ℝ :=
    |ab2Iter h f t₀ y₀ y₁ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| with hen1_def
  set en2 : ℝ :=
    |ab2Iter h f t₀ y₀ y₁ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| with hen2_def
  set τabs : ℝ :=
    |adamsBashforth2.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  -- One-step Lipschitz bound (from `ab2_one_step_lipschitz`).
  have hstep :
      en2 ≤ en1 + (3 / 2) * h * L * en1 + (1 / 2) * h * L * en + τabs := by
    have := ab2_one_step_lipschitz hh hf t₀ y₀ y₁ y hyf n
    show |ab2Iter h f t₀ y₀ y₁ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
        ≤ |ab2Iter h f t₀ y₀ y₁ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          + (3 / 2) * h * L
              * |ab2Iter h f t₀ y₀ y₁ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)|
          + (1 / 2) * h * L
              * |ab2Iter h f t₀ y₀ y₁ n - y (t₀ + (n : ℝ) * h)|
          + |adamsBashforth2.localTruncationError h (t₀ + (n : ℝ) * h) y|
    exact this
  set EN_n : ℝ := max en en1 with hEN_n_def
  have hen_le_EN : en ≤ EN_n := le_max_left _ _
  have hen1_le_EN : en1 ≤ EN_n := le_max_right _ _
  have h32_nn : 0 ≤ (3 / 2) * h * L := by positivity
  have h12_nn : 0 ≤ (1 / 2) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have h2hL_nn : 0 ≤ h * (2 * L) := by positivity
  -- en2 ≤ (1 + 2hL) * EN_n + τabs.
  have hen2_bd : en2 ≤ (1 + h * (2 * L)) * EN_n + τabs := by
    have h2 : (3 / 2) * h * L * en1 ≤ (3 / 2) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h32_nn
    have h3 : (1 / 2) * h * L * en ≤ (1 / 2) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h12_nn
    have h_alg :
        EN_n + (3 / 2) * h * L * EN_n + (1 / 2) * h * L * EN_n + τabs
          = (1 + h * (2 * L)) * EN_n + τabs := by ring
    linarith [hstep, hen1_le_EN, h2, h3, h_alg.le]
  -- en1 ≤ EN_n ≤ (1 + 2hL) * EN_n ≤ (1 + 2hL) * EN_n + τabs.
  have hen1_bd : en1 ≤ (1 + h * (2 * L)) * EN_n + τabs := by
    have hτ_nn : 0 ≤ τabs := abs_nonneg _
    have h1 : EN_n ≤ (1 + h * (2 * L)) * EN_n := by
      have hone : (1 : ℝ) * EN_n ≤ (1 + h * (2 * L)) * EN_n :=
        mul_le_mul_of_nonneg_right (by linarith) hEN_nn
      linarith
    linarith [hen1_le_EN]
  exact max_le hen1_bd hen2_bd

/-- A `C^3` function has its third derivative bounded on every compact
interval `[a, b]`. -/
theorem iteratedDeriv_three_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 3 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 3 y) :=
    hy.continuous_iteratedDeriv 3 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise third-order Taylor (Lagrange) remainder bound: if `y` is
`C^3` and `|iteratedDeriv 3 y| ≤ M` on `[a, b]`, then for `t, t + r ∈ [a, b]`
with `r ≥ 0`,
`|y(t+r) - y(t) - r·y'(t) - r²/2 · y''(t)| ≤ M/6 · r³`. -/
theorem y_third_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 3 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t - r * deriv y t - r ^ 2 / 2 * iteratedDeriv 2 y t|
      ≤ M / 6 * r ^ 3 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- Lagrange Taylor remainder at order 2 (third-derivative form).
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 2 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 3 y ξ * r ^ 3 / 6 := by
    have hcdo : ContDiffOn ℝ 3 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 3 = r ^ 3 := by ring
    have hfact : (((2 + 1 : ℕ).factorial : ℝ)) = 6 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial explicitly.
  have h_taylor :
      taylorWithinEval y 2 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t + r ^ 2 / 2 * iteratedDeriv 2 y t := by
    have h1 : iteratedDerivWithin 1 y (Set.Icc t (t + r)) t = deriv y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      simpa [iteratedDeriv_one] using heq
    have h2 :
        iteratedDerivWithin 2 y (Set.Icc t (t + r)) t = iteratedDeriv 2 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 2) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ,
      Nat.cast_mul, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one, Nat.factorial]
    ring
  -- Conclude.
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 3 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      y (t + r) - y t - r * deriv y t - r ^ 2 / 2 * iteratedDeriv 2 y t
        = iteratedDeriv 3 y ξ * r ^ 3 / 6 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  have hr3_nn : (0 : ℝ) ≤ r ^ 3 := by positivity
  rw [show iteratedDeriv 3 y ξ * r ^ 3 / 6
      = (iteratedDeriv 3 y ξ) * (r ^ 3 / 6) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 3 / 6)]
  calc |iteratedDeriv 3 y ξ| * (r ^ 3 / 6)
      ≤ M * (r ^ 3 / 6) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 6 * r ^ 3 := by ring

/-- Pointwise second-order Taylor (Lagrange) remainder bound for the
derivative: if `y` is `C^3` and `|iteratedDeriv 3 y| ≤ M` on `[a, b]`,
then for `t, t + r ∈ [a, b]` with `r ≥ 0`,
`|y'(t+r) - y'(t) - r·y''(t)| ≤ M/2 · r²`. -/
theorem derivY_second_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 3 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t|
      ≤ M / 2 * r ^ 2 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- `deriv y` is `C^2` (since `y` is `C^3`).
  have hdy : ContDiff ℝ 2 (deriv y) := hy.deriv'
  -- Lagrange Taylor at order 1 for `deriv y` on `[t, t+r]`.
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r) - taylorWithinEval (deriv y) 1 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 2 (deriv y) ξ * r ^ 2 / 2 := by
    have hcdo : ContDiffOn ℝ 2 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 2 = r ^ 2 := by ring
    have hfact : (((1 + 1 : ℕ).factorial : ℝ)) = 2 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute taylorWithinEval (deriv y) 1 [t, t+r] t (t+r) = deriv y t + r * iteratedDeriv 2 y t.
  have h_taylor :
      taylorWithinEval (deriv y) 1 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t := by
    have h0 :
        iteratedDerivWithin 0 (deriv y) (Set.Icc t (t + r)) t = deriv y t := by
      simp [iteratedDerivWithin_zero]
    have h1 :
        iteratedDerivWithin 1 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 2 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      simp only [iteratedDeriv_one] at heq
      rw [heq]
      rw [show iteratedDeriv 2 y = deriv (iteratedDeriv 1 y) from iteratedDeriv_succ]
      rw [iteratedDeriv_one]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, h0, h1]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one]
    ring
  -- Bound `iteratedDeriv 2 (deriv y) ξ = iteratedDeriv 3 y ξ`.
  have hidd_eq : iteratedDeriv 2 (deriv y) = iteratedDeriv 3 y := by
    have : iteratedDeriv 3 y = iteratedDeriv 2 (deriv y) :=
      iteratedDeriv_succ' (n := 2) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 3 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        = iteratedDeriv 3 y ξ * r ^ 2 / 2 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 3 y ξ * r ^ 2 / 2
      = (iteratedDeriv 3 y ξ) * (r ^ 2 / 2) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 2 / 2)]
  calc |iteratedDeriv 3 y ξ| * (r ^ 2 / 2)
      ≤ M * (r ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 2 * r ^ 2 := by ring

/-- Pointwise AB2 truncation residual bound. -/
private theorem ab2_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 3 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 2 * h) - y (t + h)
        - h * ((3 / 2) * deriv y (t + h) - (1 / 2) * deriv y t)|
      ≤ (9 / 4 : ℝ) * M * h ^ 3 := by
  -- Three Taylor remainders.
  have h2h : 0 ≤ 2 * h := by linarith
  -- R1 : y(t+h) - y(t) - h*y'(t) - h²/2*y''(t).
  have hR1 :=
    y_third_order_taylor_remainder hy hbnd ht hth hh
  -- R2 : y(t+2h) - y(t) - 2h*y'(t) - 2h²*y''(t).
  have hR2_raw :=
    y_third_order_taylor_remainder hy hbnd ht ht2h h2h
  -- Rewrite R2 to expose `(2h)^3` in target form.
  have hR2 :
      |y (t + 2 * h) - y t - (2 * h) * deriv y t
          - (2 * h) ^ 2 / 2 * iteratedDeriv 2 y t|
        ≤ M / 6 * (2 * h) ^ 3 := hR2_raw
  -- R3 : deriv y (t+h) - deriv y t - h * iteratedDeriv 2 y t.
  have hR3 :=
    derivY_second_order_taylor_remainder hy hbnd ht hth hh
  -- Algebraic combination of remainders gives the AB2 residual.
  set y0 := y t with hy0_def
  set y1 := y (t + h) with hy1_def
  set y2 := y (t + 2 * h) with hy2_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set dd := iteratedDeriv 2 y t with hdd_def
  -- Compute LTE in terms of remainders.
  have hLTE_eq :
      y2 - y1 - h * ((3 / 2) * d1 - (1 / 2) * d0)
        = (y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd)
          - (y1 - y0 - h * d0 - h ^ 2 / 2 * dd)
          - (3 * h / 2) * (d1 - d0 - h * dd) := by ring
  rw [hLTE_eq]
  -- Triangle inequality.
  have ht1 :
      |(y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd)
        - (y1 - y0 - h * d0 - h ^ 2 / 2 * dd)
        - (3 * h / 2) * (d1 - d0 - h * dd)|
        ≤ |y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd|
          + |y1 - y0 - h * d0 - h ^ 2 / 2 * dd|
          + (3 * h / 2) * |d1 - d0 - h * dd| := by
    have h12 :
        |(y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd)
          - (y1 - y0 - h * d0 - h ^ 2 / 2 * dd)|
          ≤ |y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd|
            + |y1 - y0 - h * d0 - h ^ 2 / 2 * dd| := abs_sub _ _
    have habs_3h : |(3 * h / 2)| = (3 * h / 2) :=
      abs_of_nonneg (by linarith)
    have h3 :
        |(3 * h / 2) * (d1 - d0 - h * dd)|
          = (3 * h / 2) * |d1 - d0 - h * dd| := by
      rw [abs_mul, habs_3h]
    have hsub :
        |(y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd)
          - (y1 - y0 - h * d0 - h ^ 2 / 2 * dd)
          - (3 * h / 2) * (d1 - d0 - h * dd)|
          ≤ |(y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd)
              - (y1 - y0 - h * d0 - h ^ 2 / 2 * dd)|
            + |(3 * h / 2) * (d1 - d0 - h * dd)| := abs_sub _ _
    linarith
  have hR1' : |y1 - y0 - h * d0 - h ^ 2 / 2 * dd| ≤ M / 6 * h ^ 3 := hR1
  have hR2' :
      |y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd|
        ≤ M / 6 * (2 * h) ^ 3 := hR2
  have hR3' : |d1 - d0 - h * dd| ≤ M / 2 * h ^ 2 := hR3
  -- Combine numeric bounds.
  have h2h3 : (2 * h) ^ 3 = 8 * h ^ 3 := by ring
  have hbound_nm :
      M / 6 * (2 * h) ^ 3 + M / 6 * h ^ 3 + (3 * h / 2) * (M / 2 * h ^ 2)
        = (9 / 4) * M * h ^ 3 := by
    rw [h2h3]; ring
  linarith [ht1, hR1', hR2', hR3', hbound_nm.le, hbound_nm.ge,
    mul_le_mul_of_nonneg_left hR3' (by linarith : (0 : ℝ) ≤ 3 * h / 2)]

/-- Uniform bound on the AB2 one-step truncation residual on a finite
horizon, given a `C^3` exact solution. -/
theorem ab2_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 2) * h ≤ T →
        |adamsBashforth2.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 3 := by
  -- Choose a compact sample interval `[t₀, t₀ + T + 1]` containing every
  -- relevant sample point `t, t + h, t + 2h` (using `(n+2)*h ≤ T` and `h ≤ 1`).
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_three_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(9 / 4 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
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
  -- Rewrite the LTE in textbook form.
  rw [ab2_localTruncationError_eq]
  show |y (t + 2 * h) - y (t + h)
      - h * (3 / 2 * deriv y (t + h) - 1 / 2 * deriv y t)|
    ≤ 9 / 4 * M * h ^ 3
  exact ab2_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem hh.le

/-- Final AB2 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
`C^3` exact solution `y` with `deriv y t = f t (y t)`, and starting
errors `|y₀ - y t₀| ≤ ε₀`, `|y₁ - y (t₀ + h)| ≤ ε₀`, the AB2 iterate
error obeys `O(ε₀ + h^2)` on a finite horizon. -/
theorem ab2_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 1) * h ≤ T →
      |ab2Iter h f t₀ y₀ y₁ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp (2 * L * T) * ε₀ + K * h ^ 2 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab2_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp (2 * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ ε₀ hε₀ he0_bd he1_bd N hNh
  -- Error sequence and max-norm sequence.
  set eN : ℕ → ℝ :=
    fun k => |ab2Iter h f t₀ y₀ y₁ k - y (t₀ + (k : ℝ) * h)| with heN_def
  set EN : ℕ → ℝ := fun k => max (eN k) (eN (k + 1)) with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (heN_nn k)
  -- Initial bound: EN 0 ≤ ε₀.
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (eN 0) (eN 1) ≤ ε₀
    refine max_le ?_ ?_
    · show |ab2Iter h f t₀ y₀ y₁ 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀
      simpa using he0_bd
    · show |ab2Iter h f t₀ y₀ y₁ 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀
      simpa using he1_bd
  have h2L_nn : (0 : ℝ) ≤ 2 * L := by linarith
  -- The general recurrence: when (n + 2) * h ≤ T,
  -- EN (n+1) ≤ (1 + h*(2L)) * EN n + C * h^3.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 2) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (2 * L)) * EN n + C * h ^ 3 := by
    intro n hnh_le
    have honestep := ab2_one_step_error_bound (h := h) (L := L)
        hh.le hL hf t₀ y₀ y₁ y hyf n
    -- Bridge `f` and `deriv y` via `hyf` so the residual bound applies.
    -- ab2_one_step_error_bound's RHS uses the LTE; the residual bound bounds it.
    have hres := hresidual hh hδ_le n hnh_le
    -- Cast (n+1 : ℕ : ℝ) = (n : ℝ) + 1 etc.
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    -- Rewrite `EN n`, `EN (n+1)` in terms of expressions matching honestep.
    have heq_eN_n : eN n
        = |ab2Iter h f t₀ y₀ y₁ n - y (t₀ + (n : ℝ) * h)| := rfl
    have heq_eN_n1 : eN (n + 1)
        = |ab2Iter h f t₀ y₀ y₁ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| := by
      show |_ - _| = _
      rw [hcast1]
    have heq_eN_n2 : eN (n + 1 + 1)
        = |ab2Iter h f t₀ y₀ y₁ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| := by
      show |_ - _| = _
      rw [hcast2]
    show max (eN (n + 1)) (eN (n + 1 + 1))
        ≤ (1 + h * (2 * L)) * max (eN n) (eN (n + 1)) + C * h ^ 3
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2]
    linarith [honestep, hres]
  -- Split on N.
  rcases N with _ | N'
  · -- N = 0: |y₀ - y t₀| ≤ ε₀ ≤ exp(2LT)*ε₀ + K*h².
    show |ab2Iter h f t₀ y₀ y₁ 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)|
        ≤ Real.exp (2 * L * T) * ε₀ + T * Real.exp (2 * L * T) * C * h ^ 2
    have hbase : |ab2Iter h f t₀ y₀ y₁ 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by simpa using he0_bd
    have hexp_ge : (1 : ℝ) ≤ Real.exp (2 * L * T) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hKnn : 0 ≤ T * Real.exp (2 * L * T) * C :=
      mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
    have hh2_nn : 0 ≤ h ^ 2 := by positivity
    nlinarith [hbase, hexp_ge, hKnn, hh2_nn, hε₀]
  · -- N = N' + 1: apply Gronwall to EN at index N'.
    have hN_hyp : ((N' : ℝ) + 1 + 1) * h ≤ T := by
      have hcast : (((N' + 1 : ℕ) : ℝ) + 1) = (N' : ℝ) + 1 + 1 := by push_cast; ring
      linarith [hcast.symm ▸ hNh]
    have hgronwall_step : ∀ n, n < N' →
        EN (n + 1) ≤ (1 + h * (2 * L)) * EN n + C * h ^ (2 + 1) := by
      intro n hn_lt
      have hpow : C * h ^ (2 + 1) = C * h ^ 3 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn1_le_N' : (n : ℝ) + 1 ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      -- (n + 2) * h ≤ (N' + 1) * h ≤ (N' + 2) * h - h ≤ T - h ≤ T.
      have h_le_chain : (n : ℝ) + 2 ≤ (N' : ℝ) + 1 + 1 := by linarith
      have h_mul : ((n : ℝ) + 2) * h ≤ ((N' : ℝ) + 1 + 1) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'h_le_T : (N' : ℝ) * h ≤ T := by
      have : (N' : ℝ) ≤ (N' : ℝ) + 1 + 1 := by linarith
      have := mul_le_mul_of_nonneg_right this hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 2 * L) (C := C) (T := T) (p := 2) (e := EN) (N := N')
        hh.le h2L_nn hC_nn (hEN_nn 0) hgronwall_step N' le_rfl hN'h_le_T
    -- eN (N' + 1) ≤ EN N'.
    have heN_le_EN : eN (N' + 1) ≤ EN N' := le_max_right _ _
    have hexp_nn : 0 ≤ Real.exp (2 * L * T) := Real.exp_nonneg _
    have h_chain :
        Real.exp (2 * L * T) * EN 0 ≤ Real.exp (2 * L * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show |ab2Iter h f t₀ y₀ y₁ (N' + 1) - y (t₀ + ((N' + 1 : ℕ) : ℝ) * h)|
        ≤ Real.exp (2 * L * T) * ε₀ + T * Real.exp (2 * L * T) * C * h ^ 2
    have heN_eq :
        eN (N' + 1)
          = |ab2Iter h f t₀ y₀ y₁ (N' + 1) - y (t₀ + ((N' + 1 : ℕ) : ℝ) * h)| :=
      rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

/-! ### Vector-valued Adams–Bashforth 2-step convergence chain

Mirror of the scalar AB2 chain above, in the same finite-dimensional normed
vector setting used by the cycle 407 forward-Euler vector chain. The textbook
local truncation error is the residual
`y(t + 2h) − y(t + h) − h · ((3/2) • y'(t + h) − (1/2) • y'(t))`. -/

/-- AB2 iteration in a normed vector space, with two starting samples
`y₀, y₁`:
`y_{n+2} = y_{n+1} + h • ((3/2) • f(t_{n+1}, y_{n+1}) − (1/2) • f(t_n, y_n))`. -/
noncomputable def ab2IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ : E) : ℕ → E
  | 0 => y₀
  | 1 => y₁
  | n + 2 =>
      ab2IterVec h f t₀ y₀ y₁ (n + 1)
        + h • ((3 / 2 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                  (ab2IterVec h f t₀ y₀ y₁ (n + 1))
              - (1 / 2 : ℝ) • f (t₀ + (n : ℝ) * h)
                  (ab2IterVec h f t₀ y₀ y₁ n))

@[simp] lemma ab2IterVec_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ : E) :
    ab2IterVec h f t₀ y₀ y₁ 0 = y₀ := rfl

@[simp] lemma ab2IterVec_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ : E) :
    ab2IterVec h f t₀ y₀ y₁ 1 = y₁ := rfl

lemma ab2IterVec_succ_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ : E) (n : ℕ) :
    ab2IterVec h f t₀ y₀ y₁ (n + 2)
      = ab2IterVec h f t₀ y₀ y₁ (n + 1)
          + h • ((3 / 2 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                    (ab2IterVec h f t₀ y₀ y₁ (n + 1))
                - (1 / 2 : ℝ) • f (t₀ + (n : ℝ) * h)
                    (ab2IterVec h f t₀ y₀ y₁ n)) := rfl

/-- Textbook AB2 vector residual: the value of the local truncation error of
the AB2 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def ab2VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 2 * h) - y (t + h)
    - h • ((3 / 2 : ℝ) • deriv y (t + h) - (1 / 2 : ℝ) • deriv y t)

/-- The vector AB2 residual unfolds to the textbook form
`y(t + 2h) − y(t + h) − h • ((3/2) • y'(t + h) − (1/2) • y'(t))`. -/
theorem ab2Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab2VecResidual h t y
      = y (t + 2 * h) - y (t + h)
          - h • ((3 / 2 : ℝ) • deriv y (t + h)
                - (1 / 2 : ℝ) • deriv y t) := rfl

/-- One-step AB2 Lipschitz step in a normed vector space. A single linearised
increment of the global error from steps `n, n+1` to `n+2`, with two Lipschitz
contributions and additive `‖τ_n‖`. -/
theorem ab2Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖ab2IterVec h f t₀ y₀ y₁ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
      ≤ ‖ab2IterVec h f t₀ y₀ y₁ (n + 1)
            - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (3 / 2) * h * L
            * ‖ab2IterVec h f t₀ y₀ y₁ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (1 / 2) * h * L
            * ‖ab2IterVec h f t₀ y₀ y₁ n - y (t₀ + (n : ℝ) * h)‖
        + ‖ab2VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := ab2IterVec h f t₀ y₀ y₁ n with hyn_def
  set yn1 : E := ab2IterVec h f t₀ y₀ y₁ (n + 1) with hyn1_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  set τ : E := ab2VecResidual h tn y with hτ_def
  have hτ_eq :
      τ = zn2 - zn1
            - h • ((3 / 2 : ℝ) • f tn1 zn1 - (1 / 2 : ℝ) • f tn zn) := by
    show ab2VecResidual h tn y = _
    unfold ab2VecResidual
    rw [htn1_h, htn_2h, hyf tn1, hyf tn]
  have hstep : ab2IterVec h f t₀ y₀ y₁ (n + 2)
      = yn1 + h • ((3 / 2 : ℝ) • f tn1 yn1 - (1 / 2 : ℝ) • f tn yn) := by
    show ab2IterVec h f t₀ y₀ y₁ (n + 2) = _
    rw [ab2IterVec_succ_succ]
  have halg : ab2IterVec h f t₀ y₀ y₁ (n + 2) - zn2
      = (yn1 - zn1)
        + h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        - h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    rw [hstep, hτ_eq]
    simp only [smul_sub]
    abel
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ := hf tn1 yn1 zn1
  have hLip2 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ := hf tn yn zn
  have h32_nn : (0 : ℝ) ≤ 3 / 2 := by norm_num
  have h12_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h32_norm :
      ‖h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
        ≤ (3 / 2) * h * L * ‖yn1 - zn1‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h32_nn]
    have : h * ((3 / 2 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((3 / 2 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 h32_nn
    nlinarith [this]
  have h12_norm :
      ‖h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))‖
        ≤ (1 / 2) * h * L * ‖yn - zn‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h12_nn]
    have : h * ((1 / 2 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((1 / 2 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 h12_nn
    nlinarith [this]
  have htri :
      ‖(yn1 - zn1)
        + h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        - h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))
        - τ‖
        ≤ ‖yn1 - zn1‖
          + ‖h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
          + ‖h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))‖
          + ‖τ‖ := by
    have h1 :
        ‖(yn1 - zn1)
          + h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))
          - h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))
          - τ‖
          ≤ ‖(yn1 - zn1)
              + h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))
              - h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))‖
            + ‖τ‖ := norm_sub_le _ _
    have h2 :
        ‖(yn1 - zn1)
          + h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))
          - h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))‖
          ≤ ‖(yn1 - zn1)
              + h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
            + ‖h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))‖ := norm_sub_le _ _
    have h3 :
        ‖(yn1 - zn1) + h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
          ≤ ‖yn1 - zn1‖
              + ‖h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖ :=
      norm_add_le _ _
    linarith
  calc ‖ab2IterVec h f t₀ y₀ y₁ (n + 2) - zn2‖
      = ‖(yn1 - zn1)
          + h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))
          - h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))
          - τ‖ := by rw [halg]
    _ ≤ ‖yn1 - zn1‖
          + ‖h • ((3 / 2 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
          + ‖h • ((1 / 2 : ℝ) • (f tn yn - f tn zn))‖
          + ‖τ‖ := htri
    _ ≤ ‖yn1 - zn1‖
          + (3 / 2) * h * L * ‖yn1 - zn1‖
          + (1 / 2) * h * L * ‖yn - zn‖
          + ‖τ‖ := by linarith [h32_norm, h12_norm]

/-- Max-norm one-step error recurrence for vector AB2 with Lipschitz constant
`L`. With `eN k := ‖y_k − y(t_k)‖` and `EN k := max (eN k) (eN (k+1))`,
`EN (n+1) ≤ (1 + h · 2L) · EN n + ‖τ_n‖`. -/
theorem ab2Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max ‖ab2IterVec h f t₀ y₀ y₁ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
        ‖ab2IterVec h f t₀ y₀ y₁ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
      ≤ (1 + h * (2 * L))
            * max ‖ab2IterVec h f t₀ y₀ y₁ n - y (t₀ + (n : ℝ) * h)‖
                  ‖ab2IterVec h f t₀ y₀ y₁ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)‖
        + ‖ab2VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖ab2IterVec h f t₀ y₀ y₁ n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖ab2IterVec h f t₀ y₀ y₁ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
    with hen1_def
  set en2 : ℝ :=
    ‖ab2IterVec h f t₀ y₀ y₁ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
    with hen2_def
  set τabs : ℝ := ‖ab2VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hstep :
      en2 ≤ en1 + (3 / 2) * h * L * en1 + (1 / 2) * h * L * en + τabs := by
    have := ab2Vec_one_step_lipschitz hh hf t₀ y₀ y₁ y hyf n
    show ‖ab2IterVec h f t₀ y₀ y₁ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
        ≤ ‖ab2IterVec h f t₀ y₀ y₁ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
          + (3 / 2) * h * L
              * ‖ab2IterVec h f t₀ y₀ y₁ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)‖
          + (1 / 2) * h * L
              * ‖ab2IterVec h f t₀ y₀ y₁ n - y (t₀ + (n : ℝ) * h)‖
          + ‖ab2VecResidual h (t₀ + (n : ℝ) * h) y‖
    exact this
  set EN_n : ℝ := max en en1 with hEN_n_def
  have hen_le_EN : en ≤ EN_n := le_max_left _ _
  have hen1_le_EN : en1 ≤ EN_n := le_max_right _ _
  have h32_nn : 0 ≤ (3 / 2) * h * L := by positivity
  have h12_nn : 0 ≤ (1 / 2) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hen2_bd : en2 ≤ (1 + h * (2 * L)) * EN_n + τabs := by
    have h2 : (3 / 2) * h * L * en1 ≤ (3 / 2) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h32_nn
    have h3 : (1 / 2) * h * L * en ≤ (1 / 2) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h12_nn
    have h_alg :
        EN_n + (3 / 2) * h * L * EN_n + (1 / 2) * h * L * EN_n + τabs
          = (1 + h * (2 * L)) * EN_n + τabs := by ring
    linarith [hstep, hen1_le_EN, h2, h3, h_alg.le]
  have hen1_bd : en1 ≤ (1 + h * (2 * L)) * EN_n + τabs := by
    have hτ_nn : 0 ≤ τabs := norm_nonneg _
    have h1 : EN_n ≤ (1 + h * (2 * L)) * EN_n := by
      have hone : (1 : ℝ) * EN_n ≤ (1 + h * (2 * L)) * EN_n :=
        mul_le_mul_of_nonneg_right (by nlinarith) hEN_nn
      linarith
    linarith [hen1_le_EN]
  exact max_le hen1_bd hen2_bd

/-- A vector-valued `C^3` function has its third derivative bounded on every
compact interval `[a, b]`. -/
private theorem iteratedDeriv_three_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 3 y t‖ ≤ M := by
  have h_cont : Continuous (iteratedDeriv 3 y) :=
    hy.continuous_iteratedDeriv 3 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

/-- Pointwise vector second-order Taylor remainder for `deriv y`: if `y` is
`C^3` and `‖iteratedDeriv 3 y‖ ≤ M` on `[a, b]`, then for `t, t + r ∈ [a, b]`
with `r ≥ 0`,
`‖deriv y (t + r) − deriv y t − r • iteratedDeriv 2 y t‖ ≤ M / 2 · r²`. -/
private theorem derivY_second_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 3 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖deriv y (t + r) - deriv y t - r • iteratedDeriv 2 y t‖
      ≤ M / 2 * r ^ 2 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htr_le : t ≤ t + r := by linarith
  -- `deriv y` is C^2 since `y` is C^3.
  have hdy : ContDiff ℝ 2 (deriv y) := hy.deriv'
  have hdy3 : ContDiff ℝ 3 y := hy
  -- Bound for `‖iteratedDeriv 2 y s − iteratedDeriv 2 y t‖ ≤ M·(s−t)` on `[t, t+r]`.
  have h_idd2_bound :
      ∀ s ∈ Set.Icc t (t + r),
        ‖iteratedDeriv 2 y s - iteratedDeriv 2 y t‖ ≤ M * (s - t) := by
    intro s hs
    have hts : t ≤ s := hs.1
    have hdiff_idd2 : Differentiable ℝ (iteratedDeriv 2 y) :=
      hy.differentiable_iteratedDeriv 2 (by norm_num)
    have hderiv_on :
        ∀ x ∈ Set.Icc t s,
          HasDerivWithinAt (iteratedDeriv 2 y) (iteratedDeriv 3 y x)
            (Set.Icc t s) x := by
      intro x _hx
      have hxderiv : HasDerivAt (iteratedDeriv 2 y) (iteratedDeriv 3 y x) x := by
        have := (hdiff_idd2 x).hasDerivAt
        convert this using 1
        rw [iteratedDeriv_succ]
      exact hxderiv.hasDerivWithinAt
    have hbound_seg : ∀ x ∈ Set.Ico t s, ‖iteratedDeriv 3 y x‖ ≤ M := by
      intro x hx
      have hx_ab : x ∈ Set.Icc a b := by
        refine ⟨?_, ?_⟩
        · linarith [ht.1, hx.1]
        · linarith [htr.2, hs.2, hx.2]
      exact hbnd x hx_ab
    have hseg :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        (f := iteratedDeriv 2 y) (f' := fun x => iteratedDeriv 3 y x)
        (a := t) (b := s) hderiv_on hbound_seg s
        (Set.right_mem_Icc.mpr hts)
    simpa using hseg
  -- `iteratedDeriv 2 y` is continuous, hence integrable.
  have h_idd2_cont : Continuous (iteratedDeriv 2 y) :=
    hy.continuous_iteratedDeriv 2 (by norm_num)
  have h_idd2_int :
      IntervalIntegrable (fun s => iteratedDeriv 2 y s)
        MeasureTheory.volume t (t + r) :=
    h_idd2_cont.intervalIntegrable _ _
  have h_const_int :
      IntervalIntegrable (fun _ : ℝ => iteratedDeriv 2 y t)
        MeasureTheory.volume t (t + r) := intervalIntegrable_const
  -- FTC: `∫_t^{t+r} iteratedDeriv 2 y = deriv y (t+r) − deriv y t`.
  have h_ftc :
      ∫ s in t..t + r, iteratedDeriv 2 y s = deriv y (t + r) - deriv y t := by
    have hderiv_at :
        ∀ x ∈ Set.uIcc t (t + r),
          HasDerivAt (deriv y) (iteratedDeriv 2 y x) x := by
      intro x _hx
      have hdy_diff : Differentiable ℝ (deriv y) := hdy.differentiable (by norm_num)
      have h1 : HasDerivAt (deriv y) (deriv (deriv y) x) x :=
        (hdy_diff x).hasDerivAt
      have h2 : deriv (deriv y) x = iteratedDeriv 2 y x := by
        rw [show iteratedDeriv 2 y = deriv (iteratedDeriv 1 y) from
            iteratedDeriv_succ, iteratedDeriv_one]
      rw [← h2]; exact h1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_at h_idd2_int
  -- Express residual as an integral of `iteratedDeriv 2 y s − iteratedDeriv 2 y t`.
  have h_residual_integral :
      deriv y (t + r) - deriv y t - r • iteratedDeriv 2 y t
        = ∫ s in t..t + r, (iteratedDeriv 2 y s - iteratedDeriv 2 y t) := by
    rw [intervalIntegral.integral_sub h_idd2_int h_const_int, h_ftc]
    simp
  have h_bound_integral :
      ‖∫ s in t..t + r, (iteratedDeriv 2 y s - iteratedDeriv 2 y t)‖
        ≤ ∫ s in t..t + r, M * (s - t) := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_idd2_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop : Continuous fun s : ℝ => M * (s - t)).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M * (s - t) = M / 2 * r ^ 2 := by
    calc
      ∫ s in t..t + r, M * (s - t)
          = M * (∫ s in t..t + r, (s - t)) := by
            rw [intervalIntegral.integral_const_mul]
      _ = M / 2 * r ^ 2 := by
        simp [intervalIntegral.integral_sub, integral_id,
          intervalIntegral.integral_const]
        ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

/-- Pointwise vector third-order Taylor remainder for `y`: if `y` is `C^3` and
`‖iteratedDeriv 3 y‖ ≤ M` on `[a, b]`, then for `t, t + r ∈ [a, b]` with
`r ≥ 0`,
`‖y(t+r) − y(t) − r • y'(t) − r²/2 • y''(t)‖ ≤ M / 6 · r³`. -/
private theorem y_third_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 3 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖y (t + r) - y t - r • deriv y t - (r ^ 2 / 2) • iteratedDeriv 2 y t‖
      ≤ M / 6 * r ^ 3 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htr_le : t ≤ t + r := by linarith
  -- Derivative bound from `derivY_second_order_taylor_remainder_vec`:
  -- ‖deriv y (t+s) − deriv y t − s • iteratedDeriv 2 y t‖ ≤ M/2 · s².
  have h_dy_bound :
      ∀ s ∈ Set.Icc t (t + r),
        ‖deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t‖
          ≤ M / 2 * (s - t) ^ 2 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have :=
      derivY_second_order_taylor_remainder_vec hy hbnd ht
        (by rw [hsplit]; exact hs_ab) hts
    rw [hsplit] at this
    exact this
  -- Set up integrand g(s) := deriv y s − deriv y t − (s−t) • iteratedDeriv 2 y t.
  -- Then ∫_t^{t+r} g(s) ds = y(t+r) − y(t) − r • deriv y t − r²/2 • iteratedDeriv 2 y t.
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
  -- FTC for y on [t, t+r].
  have h_ftc_y :
      ∫ s in t..t + r, deriv y s = y (t + r) - y t := by
    have hderiv_at :
        ∀ x ∈ Set.uIcc t (t + r),
          HasDerivAt y (deriv y x) x := by
      intro x _hx
      exact (hy.differentiable (by norm_num) x).hasDerivAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_at h_dy_int
  -- Compute ∫(s - t) ds = r²/2 and (s - t) • iteratedDeriv2 y t integral.
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
  have h_residual_integral :
      y (t + r) - y t - r • deriv y t - (r ^ 2 / 2) • iteratedDeriv 2 y t
        = ∫ s in t..t + r,
            (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t) := by
    rw [intervalIntegral.integral_sub
        (h_dy_int.sub h_const_int) h_lin_int,
      intervalIntegral.integral_sub h_dy_int h_const_int,
      h_ftc_y, h_lin_eval]
    have h_const_eval :
        ∫ _ in t..t + r, deriv y t = r • deriv y t := by
      rw [intervalIntegral.integral_const]
      simp
    rw [h_const_eval]
  have h_bound_integral :
      ‖∫ s in t..t + r,
          (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t)‖
        ≤ ∫ s in t..t + r, M / 2 * (s - t) ^ 2 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dy_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 2 * (s - t) ^ 2).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 2 * (s - t) ^ 2 = M / 6 * r ^ 3 := by
    have h_inner : ∫ s in t..t + r, (s - t) ^ 2 = r ^ 3 / 3 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 2
            = ∫ s in (t - t)..(t + r - t), s ^ 2 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) t
      rw [hsub]
      rw [integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr : (t + r - t) = r := by ring
      rw [hzero, hr]
      ring
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

/-- Pointwise vector AB2 truncation residual bound: if `y` is `C^3` with
`‖iteratedDeriv 3 y‖ ≤ M` on `[a, b]` and `t, t + h, t + 2h ∈ [a, b]` with
`h ≥ 0`, then `‖τ‖ ≤ (9/4) · M · h³`. -/
private theorem ab2Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 3 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 2 * h) - y (t + h)
        - h • ((3 / 2 : ℝ) • deriv y (t + h) - (1 / 2 : ℝ) • deriv y t)‖
      ≤ (9 / 4 : ℝ) * M * h ^ 3 := by
  have h2h : 0 ≤ 2 * h := by linarith
  -- R1: y(t+h) − y(t) − h • y'(t) − h²/2 • y''(t).
  have hR1 := y_third_order_taylor_remainder_vec hy hbnd ht hth hh
  -- R2: y(t+2h) − y(t) − 2h • y'(t) − (2h)²/2 • y''(t).
  have hR2 := y_third_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  -- R3: y'(t+h) − y'(t) − h • y''(t).
  have hR3 := derivY_second_order_taylor_remainder_vec hy hbnd ht hth hh
  set y0 : E := y t with hy0_def
  set y1 : E := y (t + h) with hy1_def
  set y2 : E := y (t + 2 * h) with hy2_def
  set d0 : E := deriv y t with hd0_def
  set d1 : E := deriv y (t + h) with hd1_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  -- LTE in terms of remainders.
  have hLTE_eq :
      y2 - y1 - h • ((3 / 2 : ℝ) • d1 - (1 / 2 : ℝ) • d0)
        = (y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd)
          - (y1 - y0 - h • d0 - (h ^ 2 / 2) • dd)
          - (3 * h / 2 : ℝ) • (d1 - d0 - h • dd) := by
    simp only [smul_sub, smul_smul]
    abel_nf
    rw [show (3 * h / 2 : ℝ) * h = (3 / 2 : ℝ) * h * h from by ring,
        show ((2 * h) ^ 2 / 2 : ℝ) = 2 * h * h from by ring]
    module
  rw [hLTE_eq]
  -- Triangle inequality.
  have ht1 :
      ‖(y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd)
        - (y1 - y0 - h • d0 - (h ^ 2 / 2) • dd)
        - (3 * h / 2 : ℝ) • (d1 - d0 - h • dd)‖
        ≤ ‖y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd‖
          + ‖y1 - y0 - h • d0 - (h ^ 2 / 2) • dd‖
          + ‖(3 * h / 2 : ℝ) • (d1 - d0 - h • dd)‖ := by
    have h12 :
        ‖(y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd)
          - (y1 - y0 - h • d0 - (h ^ 2 / 2) • dd)‖
          ≤ ‖y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd‖
            + ‖y1 - y0 - h • d0 - (h ^ 2 / 2) • dd‖ := norm_sub_le _ _
    have hsub :
        ‖(y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd)
          - (y1 - y0 - h • d0 - (h ^ 2 / 2) • dd)
          - (3 * h / 2 : ℝ) • (d1 - d0 - h • dd)‖
          ≤ ‖(y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd)
              - (y1 - y0 - h • d0 - (h ^ 2 / 2) • dd)‖
            + ‖(3 * h / 2 : ℝ) • (d1 - d0 - h • dd)‖ := norm_sub_le _ _
    linarith
  have hR1' : ‖y1 - y0 - h • d0 - (h ^ 2 / 2) • dd‖ ≤ M / 6 * h ^ 3 := hR1
  have hR2' :
      ‖y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd‖
        ≤ M / 6 * (2 * h) ^ 3 := hR2
  have hR3' : ‖d1 - d0 - h • dd‖ ≤ M / 2 * h ^ 2 := hR3
  have h3h_nn : 0 ≤ (3 * h / 2 : ℝ) := by linarith
  have hR3_smul :
      ‖(3 * h / 2 : ℝ) • (d1 - d0 - h • dd)‖
        ≤ (3 * h / 2 : ℝ) * (M / 2 * h ^ 2) := by
    rw [norm_smul, Real.norm_of_nonneg h3h_nn]
    exact mul_le_mul_of_nonneg_left hR3' h3h_nn
  have h2h3 : (2 * h) ^ 3 = 8 * h ^ 3 := by ring
  have hbound_nm :
      M / 6 * (2 * h) ^ 3 + M / 6 * h ^ 3 + (3 * h / 2 : ℝ) * (M / 2 * h ^ 2)
        = (9 / 4) * M * h ^ 3 := by
    rw [h2h3]; ring
  linarith [ht1, hR1', hR2', hR3_smul, hbound_nm.le, hbound_nm.ge]

/-- Uniform bound on the vector AB2 one-step truncation residual on a finite
horizon, given a `C^3` exact solution. -/
theorem ab2Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 2) * h ≤ T →
        ‖ab2VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 3 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_three_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(9 / 4 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
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
  show ‖ab2VecResidual h t y‖ ≤ 9 / 4 * M * h ^ 3
  unfold ab2VecResidual
  exact ab2Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem hh.le

/-! #### Refactor through the generic vector AB scaffold

The headline `ab2Vec_global_error_bound` is now obtained by specialising
`LMM.ab_global_error_bound_generic_vec` (cycle 427) to `s = 2` with the
AB2 coefficient tuple `(α 0, α 1) = (-1/2, 3/2)`. The per-step Taylor
residual infrastructure above is reused unchanged. -/

/-- AB2 coefficient vector for the generic AB scaffold:
`α 0 = -1/2`, `α 1 = 3/2`. -/
noncomputable def ab2GenericCoeff : Fin 2 → ℝ := ![-(1 / 2 : ℝ), (3 / 2 : ℝ)]

@[simp] lemma ab2GenericCoeff_zero :
    ab2GenericCoeff 0 = -(1 / 2 : ℝ) := rfl

@[simp] lemma ab2GenericCoeff_one :
    ab2GenericCoeff 1 = (3 / 2 : ℝ) := rfl

/-- The effective Lipschitz constant for the generic AB scaffold at the
AB2 coefficient tuple is `2 · L`. -/
lemma abLip_ab2GenericCoeff (L : ℝ) :
    abLip 2 ab2GenericCoeff L = 2 * L := by
  rw [abLip, Fin.sum_univ_two, ab2GenericCoeff_zero, ab2GenericCoeff_one]
  rw [show |(-(1 / 2 : ℝ))| = (1 / 2 : ℝ) by rw [abs_neg]; norm_num,
      show |((3 / 2 : ℝ))| = (3 / 2 : ℝ) by norm_num]
  ring

/-- Bridge: the AB2 vector iteration is the generic vector AB iteration
at `s = 2` with `α = ab2GenericCoeff` and starting samples `![y₀, y₁]`. -/
lemma ab2IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ : E) (n : ℕ) :
    ab2IterVec h f t₀ y₀ y₁ n
      = abIterVec 2 ab2GenericCoeff h f t₀ ![y₀, y₁] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [ab2IterVec_zero]
      unfold abIterVec
      simp
    | 1 =>
      rw [ab2IterVec_one]
      unfold abIterVec
      simp
    | k + 2 =>
      rw [ab2IterVec_succ_succ]
      rw [abIterVec_step (s := 2) (by norm_num)
          ab2GenericCoeff h f t₀ ![y₀, y₁] k]
      rw [show (k + 2 - 1 : ℕ) = k + 1 from by omega]
      rw [Fin.sum_univ_two]
      simp only [ab2GenericCoeff_zero, ab2GenericCoeff_one,
                 Fin.val_zero, Fin.val_one, Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
      rw [neg_smul]
      abel

/-- Bridge: the AB2 vector residual at base point `t₀ + n · h` equals the
generic AB vector residual at index `n`. -/
lemma ab2VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab2VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 2 ab2GenericCoeff h y t₀ n := by
  unfold ab2VecResidual abResidualVec
  rw [Fin.sum_univ_two, ab2GenericCoeff_zero, ab2GenericCoeff_one]
  -- Align time-coordinate arguments.
  have eA : t₀ + (n : ℝ) * h + 2 * h = t₀ + ((n + 2 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB : t₀ + (n : ℝ) * h + h = t₀ + ((n + 2 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 2 - 1 : ℕ) = n + 1 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h = t₀ + ((n + ((0 : Fin 2) : ℕ) : ℕ) : ℝ) * h := by
    simp [Fin.val_zero]
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 2) : ℕ) : ℕ) : ℝ) * h := by
    simp [Fin.val_one]; ring
  rw [← eA, ← eB, ← eC, ← eD]
  -- Reorder the smul expression: (3/2)•B - (1/2)•A = (-(1/2))•A + (3/2)•B.
  rw [show (-(1 / 2 : ℝ)) • deriv y (t₀ + (n : ℝ) * h)
        = -((1 / 2 : ℝ) • deriv y (t₀ + (n : ℝ) * h)) from neg_smul _ _]
  rw [show (3 / 2 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h)
        - (1 / 2 : ℝ) • deriv y (t₀ + (n : ℝ) * h)
        = -((1 / 2 : ℝ) • deriv y (t₀ + (n : ℝ) * h))
          + (3 / 2 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h) by abel]

/-- Final vector AB2 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
a `C^3` exact solution `y` with `deriv y t = f t (y t)`, and starting errors
`‖y₀ − y t₀‖ ≤ ε₀`, `‖y₁ − y(t₀ + h)‖ ≤ ε₀`, the AB2 iterate error obeys
`O(ε₀ + h^2)` on a finite horizon.

Cycle 428: rewired through `LMM.ab_global_error_bound_generic_vec` via the
bridge lemmas `ab2IterVec_eq_abIterVec` and `ab2VecResidual_eq_abResidualVec`.
The public statement and hypothesis names are unchanged. -/
theorem ab2Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
      ‖y₀ - y t₀‖ ≤ ε₀ → ‖y₁ - y (t₀ + h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 1) * h ≤ T →
      ‖ab2IterVec h f t₀ y₀ y₁ N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp (2 * L * T) * ε₀ + K * h ^ 2 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab2Vec_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp (2 * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ ε₀ hε₀ he0_bd he1_bd N hNh
  -- Specialize the generic vector AB convergence theorem at s = 2, p = 2.
  set α : Fin 2 → ℝ := ab2GenericCoeff with hα_def
  set y₀_pair : Fin 2 → E := ![y₀, y₁] with hy_pair_def
  have hs : (1 : ℕ) ≤ 2 := by norm_num
  haveI : Nonempty (Fin 2) := ⟨⟨0, hs⟩⟩
  -- (1) Starting bound on the window-max error.
  have hiter0 : abIterVec 2 α h f t₀ y₀_pair 0 = y₀ := by
    unfold abIterVec
    simp [hy_pair_def]
  have hiter1 : abIterVec 2 α h f t₀ y₀_pair 1 = y₁ := by
    unfold abIterVec
    simp [hy_pair_def]
  have hstart : abErrWindowVec hs α h f t₀ y₀_pair y 0 ≤ ε₀ := by
    unfold abErrWindowVec
    apply Finset.sup'_le
    intro j _
    show abErrVec 2 α h f t₀ y₀_pair y (0 + (j : ℕ)) ≤ ε₀
    unfold abErrVec
    fin_cases j
    · show ‖abIterVec 2 α h f t₀ y₀_pair 0 - y (t₀ + ((0 + (((0 : Fin 2) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 2) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]
      exact he0_bd
    · show ‖abIterVec 2 α h f t₀ y₀_pair 1 - y (t₀ + ((0 + (((1 : Fin 2) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 2) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]
      exact he1_bd
  -- (2) Residual bound for n < N, via the bridge.
  have hres_gen : ∀ n : ℕ, n < N →
      ‖abResidualVec 2 α h y t₀ n‖ ≤ C * h ^ (2 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 2 ≤ (N : ℝ) + 1 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn2_le : ((n : ℝ) + 2) * h ≤ T := by
      have hmul : ((n : ℝ) + 2) * h ≤ ((N : ℝ) + 1) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn2_le
    have hbridge :=
      ab2VecResidual_eq_abResidualVec (E := E) h y t₀ n
    have hpow : C * h ^ (2 + 1) = C * h ^ 3 := by norm_num
    rw [hα_def, ← hbridge]
    linarith [hres, hpow.symm.le, hpow.le]
  -- (3) (N : ℝ) * h ≤ T from ((N : ℝ) + 1) * h ≤ T and 0 ≤ h.
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 1) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  -- (4) Apply the generic theorem.
  have hgeneric :=
    ab_global_error_bound_generic_vec hs α hh.le hL hC_nn hf t₀ y₀_pair y hyf
      hε₀ hstart N hNh' hres_gen
  -- (5) Replace abLip 2 α L with 2 * L.
  rw [show abLip 2 α L = 2 * L from abLip_ab2GenericCoeff L] at hgeneric
  -- (6) Bound abErrVec at index N by the window-max bound.
  have hwindow_ge : abErrVec 2 α h f t₀ y₀_pair y N
      ≤ abErrWindowVec hs α h f t₀ y₀_pair y N := by
    show abErrVec 2 α h f t₀ y₀_pair y (N + ((⟨0, hs⟩ : Fin 2) : ℕ))
        ≤ abErrWindowVec hs α h f t₀ y₀_pair y N
    unfold abErrWindowVec
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 2 => abErrVec 2 α h f t₀ y₀_pair y (N + (j : ℕ)))
      (Finset.mem_univ _)
  -- (7) Convert abErrVec at N to ‖ab2IterVec ... N - y(...)‖ via the iter bridge.
  have hbridge :
      abIterVec 2 α h f t₀ y₀_pair N = ab2IterVec h f t₀ y₀ y₁ N := by
    rw [hα_def, hy_pair_def]
    exact (ab2IterVec_eq_abIterVec h f t₀ y₀ y₁ N).symm
  have habsErr :
      abErrVec 2 α h f t₀ y₀_pair y N
        = ‖ab2IterVec h f t₀ y₀ y₁ N - y (t₀ + (N : ℝ) * h)‖ := by
    show ‖abIterVec 2 α h f t₀ y₀_pair N - y (t₀ + (N : ℝ) * h)‖
        = ‖ab2IterVec h f t₀ y₀ y₁ N - y (t₀ + (N : ℝ) * h)‖
    rw [hbridge]
  -- Conclude.
  show ‖ab2IterVec h f t₀ y₀ y₁ N - y (t₀ + (N : ℝ) * h)‖
      ≤ Real.exp (2 * L * T) * ε₀ + T * Real.exp (2 * L * T) * C * h ^ 2
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]


end LMM
