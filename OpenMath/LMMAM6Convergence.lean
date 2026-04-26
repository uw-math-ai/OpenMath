import OpenMath.LMMTruncationOp
import OpenMath.LMMAB6ScalarConvergence
import OpenMath.AdamsMethods

/-! ## Adams--Moulton 6-step Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit Adams--Moulton
6-step method.  The chain follows the AM5 template (cycle 437) one stencil
step up: the implicit update is parameterised by a supplied trajectory
satisfying the AM6 recurrence, the local residual is bounded by eighth-order
Taylor remainders mirrored from the AB6 scalar ladder, and the global
error is assembled with `lmm_error_bound_from_local_truncation`.

The one-step Lipschitz inequality keeps the new implicit sample on the
left with factor `1 - (19087/60480)·h·L`.  The explicit-history weights
add up to `176463/60480 ≈ 2.918`, and we slacken the max-window growth
to `7L`.  The exact pointwise residual coefficient is
`1121952791/12700800 ≈ 88.34`, slackened to `89`. -/

namespace LMM

/-- A `C^8` function has its eighth derivative bounded on every compact
interval `[a, b]`. -/
private theorem iteratedDeriv_eight_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 8 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 8 y) :=
    hy.continuous_iteratedDeriv 8 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise eighth-order Taylor (Lagrange) remainder bound: if `y` is
`C^8` and `|iteratedDeriv 8 y| ≤ M` on `[a, b]`, then for `t, t + r ∈
[a, b]` with `r ≥ 0`,
`|y(t+r) - y(t) - r·y'(t) - r²/2·y''(t) - r³/6·y'''(t) - r⁴/24·y⁽⁴⁾(t)
  - r⁵/120·y⁽⁵⁾(t) - r⁶/720·y⁽⁶⁾(t) - r⁷/5040·y⁽⁷⁾(t)|
  ≤ M/40320 · r⁸`. -/
private theorem y_eighth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 8 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t
        - r ^ 4 / 24 * iteratedDeriv 4 y t
        - r ^ 5 / 120 * iteratedDeriv 5 y t
        - r ^ 6 / 720 * iteratedDeriv 6 y t
        - r ^ 7 / 5040 * iteratedDeriv 7 y t|
      ≤ M / 40320 * r ^ 8 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- Lagrange Taylor remainder at order 7 (eighth-derivative form).
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 7 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 8 y ξ * r ^ 8 / 40320 := by
    have hcdo : ContDiffOn ℝ 8 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 7) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 8 = r ^ 8 := by ring
    have hfact : (((7 + 1 : ℕ).factorial : ℝ)) = 40320 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial explicitly.
  have h_taylor :
      taylorWithinEval y 7 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t + r ^ 2 / 2 * iteratedDeriv 2 y t
              + r ^ 3 / 6 * iteratedDeriv 3 y t
              + r ^ 4 / 24 * iteratedDeriv 4 y t
              + r ^ 5 / 120 * iteratedDeriv 5 y t
              + r ^ 6 / 720 * iteratedDeriv 6 y t
              + r ^ 7 / 5040 * iteratedDeriv 7 y t := by
    have h1 : iteratedDerivWithin 1 y (Set.Icc t (t + r)) t = deriv y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      simpa [iteratedDeriv_one] using heq
    have h2 :
        iteratedDerivWithin 2 y (Set.Icc t (t + r)) t = iteratedDeriv 2 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 2) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h3 :
        iteratedDerivWithin 3 y (Set.Icc t (t + r)) t = iteratedDeriv 3 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 3) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h4 :
        iteratedDerivWithin 4 y (Set.Icc t (t + r)) t = iteratedDeriv 4 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 4) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h5 :
        iteratedDerivWithin 5 y (Set.Icc t (t + r)) t = iteratedDeriv 5 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 5) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h6 :
        iteratedDerivWithin 6 y (Set.Icc t (t + r)) t = iteratedDeriv 6 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 6) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h7 :
        iteratedDerivWithin 7 y (Set.Icc t (t + r)) t = iteratedDeriv 7 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 7) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  -- Conclude.
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 8 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      y (t + r) - y t - r * deriv y t
          - r ^ 2 / 2 * iteratedDeriv 2 y t
          - r ^ 3 / 6 * iteratedDeriv 3 y t
          - r ^ 4 / 24 * iteratedDeriv 4 y t
          - r ^ 5 / 120 * iteratedDeriv 5 y t
          - r ^ 6 / 720 * iteratedDeriv 6 y t
          - r ^ 7 / 5040 * iteratedDeriv 7 y t
        = iteratedDeriv 8 y ξ * r ^ 8 / 40320 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 8 y ξ * r ^ 8 / 40320
      = (iteratedDeriv 8 y ξ) * (r ^ 8 / 40320) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 8 / 40320)]
  calc |iteratedDeriv 8 y ξ| * (r ^ 8 / 40320)
      ≤ M * (r ^ 8 / 40320) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 40320 * r ^ 8 := by ring

/-- Pointwise seventh-order Taylor (Lagrange) remainder bound for the
derivative: if `y` is `C^8` and `|iteratedDeriv 8 y| ≤ M` on `[a, b]`,
then for `t, t + r ∈ [a, b]` with `r ≥ 0`,
`|y'(t+r) - y'(t) - r·y''(t) - r²/2·y'''(t) - r³/6·y⁽⁴⁾(t)
  - r⁴/24·y⁽⁵⁾(t) - r⁵/120·y⁽⁶⁾(t) - r⁶/720·y⁽⁷⁾(t)|
  ≤ M/5040 · r⁷`. -/
private theorem derivY_seventh_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 8 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t
        - r ^ 3 / 6 * iteratedDeriv 4 y t
        - r ^ 4 / 24 * iteratedDeriv 5 y t
        - r ^ 5 / 120 * iteratedDeriv 6 y t
        - r ^ 6 / 720 * iteratedDeriv 7 y t|
      ≤ M / 5040 * r ^ 7 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- `deriv y` is `C^7` (since `y` is `C^8`).
  have hdy : ContDiff ℝ 7 (deriv y) := hy.deriv'
  -- Lagrange Taylor at order 6 for `deriv y` on `[t, t+r]`.
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r)
          - taylorWithinEval (deriv y) 6 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 7 (deriv y) ξ * r ^ 7 / 5040 := by
    have hcdo : ContDiffOn ℝ 7 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 6) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 7 = r ^ 7 := by ring
    have hfact : (((6 + 1 : ℕ).factorial : ℝ)) = 5040 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial.
  have h_taylor :
      taylorWithinEval (deriv y) 6 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t
              + r ^ 2 / 2 * iteratedDeriv 3 y t
              + r ^ 3 / 6 * iteratedDeriv 4 y t
              + r ^ 4 / 24 * iteratedDeriv 5 y t
              + r ^ 5 / 120 * iteratedDeriv 6 y t
              + r ^ 6 / 720 * iteratedDeriv 7 y t := by
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
    have h2 :
        iteratedDerivWithin 2 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 3 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 2) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 3 y = iteratedDeriv 2 (deriv y) :=
        iteratedDeriv_succ' (n := 2) (f := y)
      rw [this]
    have h3 :
        iteratedDerivWithin 3 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 4 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 3) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 4 y = iteratedDeriv 3 (deriv y) :=
        iteratedDeriv_succ' (n := 3) (f := y)
      rw [this]
    have h4 :
        iteratedDerivWithin 4 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 5 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 4) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 5 y = iteratedDeriv 4 (deriv y) :=
        iteratedDeriv_succ' (n := 4) (f := y)
      rw [this]
    have h5 :
        iteratedDerivWithin 5 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 6 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 5) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 6 y = iteratedDeriv 5 (deriv y) :=
        iteratedDeriv_succ' (n := 5) (f := y)
      rw [this]
    have h6 :
        iteratedDerivWithin 6 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 7 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 6) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 7 y = iteratedDeriv 6 (deriv y) :=
        iteratedDeriv_succ' (n := 6) (f := y)
      rw [this]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, h0, h1, h2, h3, h4, h5, h6]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  -- Bound `iteratedDeriv 7 (deriv y) ξ = iteratedDeriv 8 y ξ`.
  have hidd_eq : iteratedDeriv 7 (deriv y) = iteratedDeriv 8 y := by
    have : iteratedDeriv 8 y = iteratedDeriv 7 (deriv y) :=
      iteratedDeriv_succ' (n := 7) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 8 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
          - r ^ 2 / 2 * iteratedDeriv 3 y t
          - r ^ 3 / 6 * iteratedDeriv 4 y t
          - r ^ 4 / 24 * iteratedDeriv 5 y t
          - r ^ 5 / 120 * iteratedDeriv 6 y t
          - r ^ 6 / 720 * iteratedDeriv 7 y t
        = iteratedDeriv 8 y ξ * r ^ 7 / 5040 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 8 y ξ * r ^ 7 / 5040
      = (iteratedDeriv 8 y ξ) * (r ^ 7 / 5040) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 7 / 5040)]
  calc |iteratedDeriv 8 y ξ| * (r ^ 7 / 5040)
      ≤ M * (r ^ 7 / 5040) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 5040 * r ^ 7 := by ring

/-- AM6 trajectory predicate:
`y_{n+6} = y_{n+5} + h(19087/60480 f_{n+6} + 65112/60480 f_{n+5}
  - 46461/60480 f_{n+4} + 37504/60480 f_{n+3} - 20211/60480 f_{n+2}
  + 6312/60480 f_{n+1} - 863/60480 f_n)`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM6Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 6)
      = y (n + 5)
        + h * ((19087 / 60480 : ℝ) * f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             + (65112 / 60480 : ℝ) * f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             - (46461 / 60480 : ℝ) * f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             + (37504 / 60480 : ℝ) * f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             - (20211 / 60480 : ℝ) * f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             + (6312 / 60480 : ℝ) * f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             - (863 / 60480 : ℝ) * f (t₀ + (n : ℝ) * h) (y n))

/-- AM6 local truncation operator reduces to the textbook residual. -/
theorem am6_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsMoulton6.localTruncationError h t y
      = y (t + 6 * h) - y (t + 5 * h)
          - h * ((19087 / 60480 : ℝ) * deriv y (t + 6 * h)
                + (65112 / 60480 : ℝ) * deriv y (t + 5 * h)
                - (46461 / 60480 : ℝ) * deriv y (t + 4 * h)
                + (37504 / 60480 : ℝ) * deriv y (t + 3 * h)
                - (20211 / 60480 : ℝ) * deriv y (t + 2 * h)
                + (6312 / 60480 : ℝ) * deriv y (t + h)
                - (863 / 60480 : ℝ) * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsMoulton6, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AM6 Lipschitz inequality before dividing by the implicit
new-point factor.  The side condition records the small-step regime used
by the divided form. -/
theorem am6_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (19087 / 60480 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM6Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (19087 / 60480 : ℝ) * h * L)
        * |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
      ≤ |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
        + (65112 / 60480 : ℝ) * h * L
            * |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
        + (46461 / 60480 : ℝ) * h * L
            * |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
        + (37504 / 60480 : ℝ) * h * L
            * |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
        + (20211 / 60480 : ℝ) * h * L
            * |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
        + (6312 / 60480 : ℝ) * h * L
            * |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
        + (863 / 60480 : ℝ) * h * L
            * |yseq n - y (t₀ + (n : ℝ) * h)|
        + |adamsMoulton6.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  -- Abbreviations.
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set yn3 : ℝ := yseq (n + 3) with hyn3_def
  set yn4 : ℝ := yseq (n + 4) with hyn4_def
  set yn5 : ℝ := yseq (n + 5) with hyn5_def
  set yn6 : ℝ := yseq (n + 6) with hyn6_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set zn6 : ℝ := y tn6 with hzn6_def
  set τ : ℝ := adamsMoulton6.localTruncationError h tn y with hτ_def
  have _hsmall_record : (19087 / 60480 : ℝ) * h * L ≤ 1 / 2 := hsmall
  -- AM6 step formula for the supplied implicit trajectory.
  have hstep : yn6
      = yn5
        + h * ((19087 / 60480 : ℝ) * f tn6 yn6
             + (65112 / 60480 : ℝ) * f tn5 yn5
             - (46461 / 60480 : ℝ) * f tn4 yn4
             + (37504 / 60480 : ℝ) * f tn3 yn3
             - (20211 / 60480 : ℝ) * f tn2 yn2
             + (6312 / 60480 : ℝ) * f tn1 yn1
             - (863 / 60480 : ℝ) * f tn yn) := by
    simpa [hyn6_def, hyn5_def, hyn4_def, hyn3_def, hyn2_def, hyn1_def, hyn_def,
      htn6_def, htn5_def, htn4_def, htn3_def, htn2_def, htn1_def, htn_def] using
      hy.recurrence n
  -- Local truncation residual at `tn`, expressed via `f` along the trajectory.
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
  have hτ_eq : τ = zn6 - zn5
      - h * ((19087 / 60480 : ℝ) * f tn6 zn6
             + (65112 / 60480 : ℝ) * f tn5 zn5
             - (46461 / 60480 : ℝ) * f tn4 zn4
             + (37504 / 60480 : ℝ) * f tn3 zn3
             - (20211 / 60480 : ℝ) * f tn2 zn2
             + (6312 / 60480 : ℝ) * f tn1 zn1
             - (863 / 60480 : ℝ) * f tn zn) := by
    show adamsMoulton6.localTruncationError h tn y = _
    rw [am6_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h,
      htn_5h, htn_6h, hyf tn6, hyf tn5, hyf tn4, hyf tn3, hyf tn2, hyf tn1,
      hyf tn]
  -- Algebraic decomposition of the implicit global-error increment.
  have halg : yn6 - zn6
      = (yn5 - zn5)
        + (19087 / 60480 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)
        + (65112 / 60480 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
        - (46461 / 60480 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        + (37504 / 60480 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        - (20211 / 60480 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        + (6312 / 60480 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        - (863 / 60480 : ℝ) * h * (f tn yn - f tn zn)
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
  -- Lipschitz bounds on the seven `f` increments.
  have hLip6 : |f tn6 yn6 - f tn6 zn6| ≤ L * |yn6 - zn6| :=
    hf tn6 yn6 zn6
  have hLip5 : |f tn5 yn5 - f tn5 zn5| ≤ L * |yn5 - zn5| :=
    hf tn5 yn5 zn5
  have hLip4 : |f tn4 yn4 - f tn4 zn4| ≤ L * |yn4 - zn4| :=
    hf tn4 yn4 zn4
  have hLip3 : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| :=
    hf tn3 yn3 zn3
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| :=
    hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| :=
    hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| :=
    hf tn yn zn
  have h19087_nn : 0 ≤ (19087 / 60480 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h65112_nn : 0 ≤ (65112 / 60480 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h46461_nn : 0 ≤ (46461 / 60480 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h37504_nn : 0 ≤ (37504 / 60480 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h20211_nn : 0 ≤ (20211 / 60480 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h6312_nn : 0 ≤ (6312 / 60480 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h863_nn : 0 ≤ (863 / 60480 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h19087_abs :
      |(19087 / 60480 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)|
      ≤ (19087 / 60480 : ℝ) * h * L * |yn6 - zn6| := by
    rw [abs_mul, abs_of_nonneg h19087_nn]
    calc (19087 / 60480 : ℝ) * h * |f tn6 yn6 - f tn6 zn6|
        ≤ (19087 / 60480 : ℝ) * h * (L * |yn6 - zn6|) :=
          mul_le_mul_of_nonneg_left hLip6 h19087_nn
      _ = (19087 / 60480 : ℝ) * h * L * |yn6 - zn6| := by ring
  have h65112_abs :
      |(65112 / 60480 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
      ≤ (65112 / 60480 : ℝ) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg h65112_nn]
    calc (65112 / 60480 : ℝ) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (65112 / 60480 : ℝ) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip5 h65112_nn
      _ = (65112 / 60480 : ℝ) * h * L * |yn5 - zn5| := by ring
  have h46461_abs :
      |(46461 / 60480 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (46461 / 60480 : ℝ) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h46461_nn]
    calc (46461 / 60480 : ℝ) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (46461 / 60480 : ℝ) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 h46461_nn
      _ = (46461 / 60480 : ℝ) * h * L * |yn4 - zn4| := by ring
  have h37504_abs :
      |(37504 / 60480 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (37504 / 60480 : ℝ) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h37504_nn]
    calc (37504 / 60480 : ℝ) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (37504 / 60480 : ℝ) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h37504_nn
      _ = (37504 / 60480 : ℝ) * h * L * |yn3 - zn3| := by ring
  have h20211_abs :
      |(20211 / 60480 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (20211 / 60480 : ℝ) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h20211_nn]
    calc (20211 / 60480 : ℝ) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (20211 / 60480 : ℝ) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h20211_nn
      _ = (20211 / 60480 : ℝ) * h * L * |yn2 - zn2| := by ring
  have h6312_abs :
      |(6312 / 60480 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (6312 / 60480 : ℝ) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h6312_nn]
    calc (6312 / 60480 : ℝ) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (6312 / 60480 : ℝ) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h6312_nn
      _ = (6312 / 60480 : ℝ) * h * L * |yn1 - zn1| := by ring
  have h863_abs :
      |(863 / 60480 : ℝ) * h * (f tn yn - f tn zn)|
      ≤ (863 / 60480 : ℝ) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h863_nn]
    calc (863 / 60480 : ℝ) * h * |f tn yn - f tn zn|
        ≤ (863 / 60480 : ℝ) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h863_nn
      _ = (863 / 60480 : ℝ) * h * L * |yn - zn| := by ring
  -- Triangle inequality for nine terms (8 algebraic + τ).
  have htri_terms (A B C D E F G H I : ℝ) :
      |A + B + C - D + E - F + G - H - I|
        ≤ |A| + |B| + |C| + |D| + |E| + |F| + |G| + |H| + |I| := by
    have h1 : |A + B + C - D + E - F + G - H - I|
        ≤ |A + B + C - D + E - F + G - H| + |I| := abs_sub _ _
    have h2 : |A + B + C - D + E - F + G - H|
        ≤ |A + B + C - D + E - F + G| + |H| := abs_sub _ _
    have h3 : |A + B + C - D + E - F + G|
        ≤ |A + B + C - D + E - F| + |G| := abs_add_le _ _
    have h4 : |A + B + C - D + E - F|
        ≤ |A + B + C - D + E| + |F| := abs_sub _ _
    have h5 : |A + B + C - D + E|
        ≤ |A + B + C - D| + |E| := abs_add_le _ _
    have h6 : |A + B + C - D| ≤ |A + B + C| + |D| := abs_sub _ _
    have h7 : |A + B + C| ≤ |A + B| + |C| := abs_add_le _ _
    have h8 : |A + B| ≤ |A| + |B| := abs_add_le _ _
    linarith
  have htri :
      |(yn5 - zn5)
        + (19087 / 60480 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)
        + (65112 / 60480 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
        - (46461 / 60480 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        + (37504 / 60480 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        - (20211 / 60480 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        + (6312 / 60480 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        - (863 / 60480 : ℝ) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn5 - zn5|
          + |(19087 / 60480 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(65112 / 60480 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(46461 / 60480 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(37504 / 60480 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(20211 / 60480 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(6312 / 60480 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(863 / 60480 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| :=
    htri_terms (yn5 - zn5)
      ((19087 / 60480 : ℝ) * h * (f tn6 yn6 - f tn6 zn6))
      ((65112 / 60480 : ℝ) * h * (f tn5 yn5 - f tn5 zn5))
      ((46461 / 60480 : ℝ) * h * (f tn4 yn4 - f tn4 zn4))
      ((37504 / 60480 : ℝ) * h * (f tn3 yn3 - f tn3 zn3))
      ((20211 / 60480 : ℝ) * h * (f tn2 yn2 - f tn2 zn2))
      ((6312 / 60480 : ℝ) * h * (f tn1 yn1 - f tn1 zn1))
      ((863 / 60480 : ℝ) * h * (f tn yn - f tn zn)) τ
  have hmain :
      |yn6 - zn6|
        ≤ |yn5 - zn5|
          + (19087 / 60480 : ℝ) * h * L * |yn6 - zn6|
          + (65112 / 60480 : ℝ) * h * L * |yn5 - zn5|
          + (46461 / 60480 : ℝ) * h * L * |yn4 - zn4|
          + (37504 / 60480 : ℝ) * h * L * |yn3 - zn3|
          + (20211 / 60480 : ℝ) * h * L * |yn2 - zn2|
          + (6312 / 60480 : ℝ) * h * L * |yn1 - zn1|
          + (863 / 60480 : ℝ) * h * L * |yn - zn|
          + |τ| := by
    calc |yn6 - zn6|
        = |(yn5 - zn5)
            + (19087 / 60480 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)
            + (65112 / 60480 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
            - (46461 / 60480 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
            + (37504 / 60480 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
            - (20211 / 60480 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
            + (6312 / 60480 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
            - (863 / 60480 : ℝ) * h * (f tn yn - f tn zn)
            - τ| := by rw [halg]
      _ ≤ |yn5 - zn5|
          + |(19087 / 60480 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(65112 / 60480 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(46461 / 60480 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(37504 / 60480 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(20211 / 60480 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(6312 / 60480 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(863 / 60480 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| := htri
      _ ≤ |yn5 - zn5|
          + (19087 / 60480 : ℝ) * h * L * |yn6 - zn6|
          + (65112 / 60480 : ℝ) * h * L * |yn5 - zn5|
          + (46461 / 60480 : ℝ) * h * L * |yn4 - zn4|
          + (37504 / 60480 : ℝ) * h * L * |yn3 - zn3|
          + (20211 / 60480 : ℝ) * h * L * |yn2 - zn2|
          + (6312 / 60480 : ℝ) * h * L * |yn1 - zn1|
          + (863 / 60480 : ℝ) * h * L * |yn - zn|
          + |τ| := by
        linarith [h19087_abs, h65112_abs, h46461_abs, h37504_abs,
          h20211_abs, h6312_abs, h863_abs]
  linarith [hmain]

/-- Divided one-step AM6 error bound.  The explicit AM6 weights contribute
`176463/60480`; after dividing by the implicit `(1 - (19087/60480)hL)`
factor, we slacken the max-window growth to `7L` and the residual
coefficient to `2`. -/
theorem am6_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (19087 / 60480 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM6Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
      ≤ (1 + h * (7 * L))
            * max (max (max (max (max
                |yseq n - y (t₀ + (n : ℝ) * h)|
                |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|)
                |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
                |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
                |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
                |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
        + 2 * |adamsMoulton6.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |yseq n - y (t₀ + (n : ℝ) * h)| with hen_def
  set en1 : ℝ :=
    |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| with hen1_def
  set en2 : ℝ :=
    |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| with hen2_def
  set en3 : ℝ :=
    |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)| with hen3_def
  set en4 : ℝ :=
    |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)| with hen4_def
  set en5 : ℝ :=
    |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)| with hen5_def
  set en6 : ℝ :=
    |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)| with hen6_def
  set τabs : ℝ :=
    |adamsMoulton6.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ := max (max (max (max (max en en1) en2) en3) en4) en5 with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen_le_E : en ≤ E :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen3_le_E : en3 ≤ E :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen4_le_E : en4 ≤ E := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen5_le_E : en5 ≤ E := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 30240 / 19087 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (19087 / 60480 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (19087 / 60480 : ℝ) * h * L) * en6
        ≤ en5
          + (65112 / 60480 : ℝ) * h * L * en5
          + (46461 / 60480 : ℝ) * h * L * en4
          + (37504 / 60480 : ℝ) * h * L * en3
          + (20211 / 60480 : ℝ) * h * L * en2
          + (6312 / 60480 : ℝ) * h * L * en1
          + (863 / 60480 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hτabs_def]
      using
      (am6_one_step_lipschitz (h := h) (L := L) hh hsmall hf t₀ hy y hyf n)
  have h65112_nn : 0 ≤ (65112 / 60480 : ℝ) * h * L := by positivity
  have h46461_nn : 0 ≤ (46461 / 60480 : ℝ) * h * L := by positivity
  have h37504_nn : 0 ≤ (37504 / 60480 : ℝ) * h * L := by positivity
  have h20211_nn : 0 ≤ (20211 / 60480 : ℝ) * h * L := by positivity
  have h6312_nn : 0 ≤ (6312 / 60480 : ℝ) * h * L := by positivity
  have h863_nn : 0 ≤ (863 / 60480 : ℝ) * h * L := by positivity
  have h65112_le :
      (65112 / 60480 : ℝ) * h * L * en5
        ≤ (65112 / 60480 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen5_le_E h65112_nn
  have h46461_le :
      (46461 / 60480 : ℝ) * h * L * en4
        ≤ (46461 / 60480 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen4_le_E h46461_nn
  have h37504_le :
      (37504 / 60480 : ℝ) * h * L * en3
        ≤ (37504 / 60480 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen3_le_E h37504_nn
  have h20211_le :
      (20211 / 60480 : ℝ) * h * L * en2
        ≤ (20211 / 60480 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen2_le_E h20211_nn
  have h6312_le :
      (6312 / 60480 : ℝ) * h * L * en1
        ≤ (6312 / 60480 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen1_le_E h6312_nn
  have h863_le :
      (863 / 60480 : ℝ) * h * L * en
        ≤ (863 / 60480 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen_le_E h863_nn
  have hR_le :
      en5
          + (65112 / 60480 : ℝ) * h * L * en5
          + (46461 / 60480 : ℝ) * h * L * en4
          + (37504 / 60480 : ℝ) * h * L * en3
          + (20211 / 60480 : ℝ) * h * L * en2
          + (6312 / 60480 : ℝ) * h * L * en1
          + (863 / 60480 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (176463 / 60480 : ℝ) * (h * L)) * E + τabs := by
    have h_alg :
        E + (65112 / 60480 : ℝ) * h * L * E
            + (46461 / 60480 : ℝ) * h * L * E
            + (37504 / 60480 : ℝ) * h * L * E
            + (20211 / 60480 : ℝ) * h * L * E
            + (6312 / 60480 : ℝ) * h * L * E
            + (863 / 60480 : ℝ) * h * L * E + τabs
          = (1 + (176463 / 60480 : ℝ) * (h * L)) * E + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (176463 / 60480 : ℝ) * (h * L)
        ≤ (1 - (19087 / 60480 : ℝ) * h * L) * (1 + h * (7 * L)) := by
    have hxL_eq :
        (1 - (19087 / 60480 : ℝ) * h * L) * (1 + h * (7 * L))
          - (1 + (176463 / 60480 : ℝ) * (h * L))
          = (h * L) / 60480 * (227810 - 133609 * (h * L)) := by ring
    have hpos : 0 ≤ 227810 - 133609 * (h * L) := by
      have hbound : 133609 * (h * L) ≤ 133609 * (30240 / 19087) := by
        have h133609_nn : (0 : ℝ) ≤ 133609 := by norm_num
        exact mul_le_mul_of_nonneg_left hx_small h133609_nn
      have hnum : (133609 : ℝ) * (30240 / 19087) ≤ 227810 := by norm_num
      linarith
    have hprod : 0 ≤ (h * L) / 60480 * (227810 - 133609 * (h * L)) := by
      apply mul_nonneg
      · positivity
      · exact hpos
    linarith
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (19087 / 60480 : ℝ) * h * L) * 2 := by
    linarith [hsmall]
  have hE_part :
      (1 + (176463 / 60480 : ℝ) * (h * L)) * E
        ≤ ((1 - (19087 / 60480 : ℝ) * h * L) * (1 + h * (7 * L))) * E :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (19087 / 60480 : ℝ) * h * L) * 2) * τabs :=
    by simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (176463 / 60480 : ℝ) * (h * L)) * E + τabs
        ≤ (1 - (19087 / 60480 : ℝ) * h * L)
            * ((1 + h * (7 * L)) * E + 2 * τabs) := by
    have hsplit :
        (1 - (19087 / 60480 : ℝ) * h * L)
            * ((1 + h * (7 * L)) * E + 2 * τabs)
          = ((1 - (19087 / 60480 : ℝ) * h * L) * (1 + h * (7 * L))) * E
              + ((1 - (19087 / 60480 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (19087 / 60480 : ℝ) * h * L) * en6
        ≤ (1 - (19087 / 60480 : ℝ) * h * L)
            * ((1 + h * (7 * L)) * E + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  have hcancel :
      en6 ≤ (1 + h * (7 * L)) * E + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  exact hcancel

/-- Max-norm AM6 one-step recurrence on the rolling 6-window
`(en, en1, en2, en3, en4, en5)`. -/
theorem am6_one_step_error_pair_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (19087 / 60480 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM6Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max
          |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
          |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
          |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
          |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
      ≤ (1 + h * (7 * L))
            * max (max (max (max (max
                |yseq n - y (t₀ + (n : ℝ) * h)|
                |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|)
                |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
                |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
                |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
                |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
        + 2 * |adamsMoulton6.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |yseq n - y (t₀ + (n : ℝ) * h)| with hen_def
  set en1 : ℝ :=
    |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| with hen1_def
  set en2 : ℝ :=
    |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| with hen2_def
  set en3 : ℝ :=
    |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)| with hen3_def
  set en4 : ℝ :=
    |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)| with hen4_def
  set en5 : ℝ :=
    |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)| with hen5_def
  set en6 : ℝ :=
    |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)| with hen6_def
  set τabs : ℝ :=
    |adamsMoulton6.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ := max (max (max (max (max en en1) en2) en3) en4) en5 with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen3_le_E : en3 ≤ E :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen4_le_E : en4 ≤ E := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen5_le_E : en5 ≤ E := le_max_right _ _
  have h7hL_nn : 0 ≤ h * (7 * L) := by positivity
  -- en6 bound from `am6_one_step_error_bound`.
  have hen6_bd :
      en6 ≤ (1 + h * (7 * L)) * E + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hτabs_def, hE_def]
      using
      (am6_one_step_error_bound (h := h) (L := L) hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : E ≤ (1 + h * (7 * L)) * E := by
    have hone : (1 : ℝ) * E ≤ (1 + h * (7 * L)) * E :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (7 * L)) * E + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (7 * L)) * E + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (7 * L)) * E + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  have hen4_bd : en4 ≤ (1 + h * (7 * L)) * E + 2 * τabs := by
    linarith [hen4_le_E, hE_le_grow]
  have hen5_bd : en5 ≤ (1 + h * (7 * L)) * E + 2 * τabs := by
    linarith [hen5_le_E, hE_le_grow]
  exact max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd)
    hen4_bd) hen5_bd) hen6_bd

/-- Pure algebraic identity: the AM6 residual rewrites as a signed sum of
eight Taylor remainders. Extracted as a stand-alone lemma so the kernel
checks the (large degree-8) `ring` proof term in isolation. -/
private lemma am6_residual_alg_identity
    (y0 y5 y6 d0 d1 d2 d3 d4 d5 d6 dd ddd dddd ddddd dddddd ddddddd h : ℝ) :
    y6 - y5 - h * ((19087 / 60480) * d6 + (65112 / 60480) * d5
                  - (46461 / 60480) * d4 + (37504 / 60480) * d3
                  - (20211 / 60480) * d2 + (6312 / 60480) * d1
                  - (863 / 60480) * d0)
      = (y6 - y0 - (6 * h) * d0
            - (6 * h) ^ 2 / 2 * dd
            - (6 * h) ^ 3 / 6 * ddd
            - (6 * h) ^ 4 / 24 * dddd
            - (6 * h) ^ 5 / 120 * ddddd
            - (6 * h) ^ 6 / 720 * dddddd
            - (6 * h) ^ 7 / 5040 * ddddddd)
        - (y5 - y0 - (5 * h) * d0
            - (5 * h) ^ 2 / 2 * dd
            - (5 * h) ^ 3 / 6 * ddd
            - (5 * h) ^ 4 / 24 * dddd
            - (5 * h) ^ 5 / 120 * ddddd
            - (5 * h) ^ 6 / 720 * dddddd
            - (5 * h) ^ 7 / 5040 * ddddddd)
        - (19087 * h / 60480)
            * (d6 - d0 - (6 * h) * dd
                - (6 * h) ^ 2 / 2 * ddd
                - (6 * h) ^ 3 / 6 * dddd
                - (6 * h) ^ 4 / 24 * ddddd
                - (6 * h) ^ 5 / 120 * dddddd
                - (6 * h) ^ 6 / 720 * ddddddd)
        - (65112 * h / 60480)
            * (d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd
                - (5 * h) ^ 6 / 720 * ddddddd)
        + (46461 * h / 60480)
            * (d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd
                - (4 * h) ^ 6 / 720 * ddddddd)
        - (37504 * h / 60480)
            * (d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd
                - (3 * h) ^ 6 / 720 * ddddddd)
        + (20211 * h / 60480)
            * (d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd
                - (2 * h) ^ 6 / 720 * ddddddd)
        - (6312 * h / 60480)
            * (d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd
                - h ^ 6 / 720 * ddddddd) := by
  ring

/-- Pure algebraic identity: the sum of the eight scaled Lagrange
remainder bounds equals `(1121952791/12700800) · M · h^8`. -/
private lemma am6_residual_bound_alg_identity (M h : ℝ) :
    M / 40320 * (6 * h) ^ 8 + M / 40320 * (5 * h) ^ 8
      + (19087 * h / 60480) * (M / 5040 * (6 * h) ^ 7)
      + (65112 * h / 60480) * (M / 5040 * (5 * h) ^ 7)
      + (46461 * h / 60480) * (M / 5040 * (4 * h) ^ 7)
      + (37504 * h / 60480) * (M / 5040 * (3 * h) ^ 7)
      + (20211 * h / 60480) * (M / 5040 * (2 * h) ^ 7)
      + (6312 * h / 60480) * (M / 5040 * h ^ 7)
      = (1121952791 / 12700800 : ℝ) * M * h ^ 8 := by
  ring

/-- Triangle inequality for the eight-term AM6 residual chunk. -/
private lemma am6_residual_eight_term_triangle
    (A B C D E F G H h : ℝ) (hh : 0 ≤ h) :
    |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
        + (46461 * h / 60480) * E - (37504 * h / 60480) * F
        + (20211 * h / 60480) * G - (6312 * h / 60480) * H|
      ≤ |A| + |B| + (19087 * h / 60480) * |C| + (65112 * h / 60480) * |D|
          + (46461 * h / 60480) * |E| + (37504 * h / 60480) * |F|
          + (20211 * h / 60480) * |G| + (6312 * h / 60480) * |H| := by
  have h19087h_nn : 0 ≤ 19087 * h / 60480 := by linarith
  have h65112h_nn : 0 ≤ 65112 * h / 60480 := by linarith
  have h46461h_nn : 0 ≤ 46461 * h / 60480 := by linarith
  have h37504h_nn : 0 ≤ 37504 * h / 60480 := by linarith
  have h20211h_nn : 0 ≤ 20211 * h / 60480 := by linarith
  have h6312h_nn : 0 ≤ 6312 * h / 60480 := by linarith
  have habs19087 : |(19087 * h / 60480) * C| = (19087 * h / 60480) * |C| := by
    rw [abs_mul, abs_of_nonneg h19087h_nn]
  have habs65112 : |(65112 * h / 60480) * D| = (65112 * h / 60480) * |D| := by
    rw [abs_mul, abs_of_nonneg h65112h_nn]
  have habs46461 : |(46461 * h / 60480) * E| = (46461 * h / 60480) * |E| := by
    rw [abs_mul, abs_of_nonneg h46461h_nn]
  have habs37504 : |(37504 * h / 60480) * F| = (37504 * h / 60480) * |F| := by
    rw [abs_mul, abs_of_nonneg h37504h_nn]
  have habs20211 : |(20211 * h / 60480) * G| = (20211 * h / 60480) * |G| := by
    rw [abs_mul, abs_of_nonneg h20211h_nn]
  have habs6312 : |(6312 * h / 60480) * H| = (6312 * h / 60480) * |H| := by
    rw [abs_mul, abs_of_nonneg h6312h_nn]
  have h1 : |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
                + (46461 * h / 60480) * E - (37504 * h / 60480) * F
                + (20211 * h / 60480) * G - (6312 * h / 60480) * H|
      ≤ |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
            + (46461 * h / 60480) * E - (37504 * h / 60480) * F
            + (20211 * h / 60480) * G|
        + |(6312 * h / 60480) * H| := abs_sub _ _
  have h2 : |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
                + (46461 * h / 60480) * E - (37504 * h / 60480) * F
                + (20211 * h / 60480) * G|
      ≤ |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
            + (46461 * h / 60480) * E - (37504 * h / 60480) * F|
        + |(20211 * h / 60480) * G| := abs_add_le _ _
  have h3 : |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
                + (46461 * h / 60480) * E - (37504 * h / 60480) * F|
      ≤ |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
            + (46461 * h / 60480) * E|
        + |(37504 * h / 60480) * F| := abs_sub _ _
  have h4 : |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
                + (46461 * h / 60480) * E|
      ≤ |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D|
        + |(46461 * h / 60480) * E| := abs_add_le _ _
  have h5 : |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D|
      ≤ |A - B - (19087 * h / 60480) * C| + |(65112 * h / 60480) * D| :=
    abs_sub _ _
  have h6 : |A - B - (19087 * h / 60480) * C|
      ≤ |A - B| + |(19087 * h / 60480) * C| := abs_sub _ _
  have h7 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith [habs19087.le, habs19087.ge, habs65112.le, habs65112.ge,
    habs46461.le, habs46461.ge, habs37504.le, habs37504.ge,
    habs20211.le, habs20211.ge, habs6312.le, habs6312.ge]

/-- Combine the eight-term triangle inequality with the absolute bounds
on each piece to obtain the `89 · M · h^8` final bound.  Extracted as a
helper so the kernel verifies the `linarith` proof term in isolation, not
inside the heavy `am6_pointwise_residual_bound` context. -/
private lemma am6_residual_combine
    {M h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D E F G H : ℝ)
    (htri : |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
              + (46461 * h / 60480) * E - (37504 * h / 60480) * F
              + (20211 * h / 60480) * G - (6312 * h / 60480) * H|
            ≤ |A| + |B| + (19087 * h / 60480) * |C|
              + (65112 * h / 60480) * |D| + (46461 * h / 60480) * |E|
              + (37504 * h / 60480) * |F| + (20211 * h / 60480) * |G|
              + (6312 * h / 60480) * |H|)
    (hA_bd : |A| ≤ M / 40320 * (6 * h) ^ 8)
    (hB_bd : |B| ≤ M / 40320 * (5 * h) ^ 8)
    (hC_bd : |C| ≤ M / 5040 * (6 * h) ^ 7)
    (hD_bd : |D| ≤ M / 5040 * (5 * h) ^ 7)
    (hE_bd : |E| ≤ M / 5040 * (4 * h) ^ 7)
    (hF_bd : |F| ≤ M / 5040 * (3 * h) ^ 7)
    (hG_bd : |G| ≤ M / 5040 * (2 * h) ^ 7)
    (hH_bd : |H| ≤ M / 5040 * h ^ 7) :
    |A - B - (19087 * h / 60480) * C - (65112 * h / 60480) * D
        + (46461 * h / 60480) * E - (37504 * h / 60480) * F
        + (20211 * h / 60480) * G - (6312 * h / 60480) * H|
      ≤ (89 : ℝ) * M * h ^ 8 := by
  have h19087h_nn : 0 ≤ 19087 * h / 60480 := by linarith
  have h65112h_nn : 0 ≤ 65112 * h / 60480 := by linarith
  have h46461h_nn : 0 ≤ 46461 * h / 60480 := by linarith
  have h37504h_nn : 0 ≤ 37504 * h / 60480 := by linarith
  have h20211h_nn : 0 ≤ 20211 * h / 60480 := by linarith
  have h6312h_nn : 0 ≤ 6312 * h / 60480 := by linarith
  have h19087C_bd : (19087 * h / 60480) * |C|
      ≤ (19087 * h / 60480) * (M / 5040 * (6 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hC_bd h19087h_nn
  have h65112D_bd : (65112 * h / 60480) * |D|
      ≤ (65112 * h / 60480) * (M / 5040 * (5 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hD_bd h65112h_nn
  have h46461E_bd : (46461 * h / 60480) * |E|
      ≤ (46461 * h / 60480) * (M / 5040 * (4 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hE_bd h46461h_nn
  have h37504F_bd : (37504 * h / 60480) * |F|
      ≤ (37504 * h / 60480) * (M / 5040 * (3 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hF_bd h37504h_nn
  have h20211G_bd : (20211 * h / 60480) * |G|
      ≤ (20211 * h / 60480) * (M / 5040 * (2 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hG_bd h20211h_nn
  have h6312H_bd : (6312 * h / 60480) * |H|
      ≤ (6312 * h / 60480) * (M / 5040 * h ^ 7) :=
    mul_le_mul_of_nonneg_left hH_bd h6312h_nn
  have hbound_alg :
      M / 40320 * (6 * h) ^ 8 + M / 40320 * (5 * h) ^ 8
        + (19087 * h / 60480) * (M / 5040 * (6 * h) ^ 7)
        + (65112 * h / 60480) * (M / 5040 * (5 * h) ^ 7)
        + (46461 * h / 60480) * (M / 5040 * (4 * h) ^ 7)
        + (37504 * h / 60480) * (M / 5040 * (3 * h) ^ 7)
        + (20211 * h / 60480) * (M / 5040 * (2 * h) ^ 7)
        + (6312 * h / 60480) * (M / 5040 * h ^ 7)
        = (1121952791 / 12700800 : ℝ) * M * h ^ 8 :=
    am6_residual_bound_alg_identity M h
  have hh8_nn : 0 ≤ h ^ 8 := by positivity
  have hMh8_nn : 0 ≤ M * h ^ 8 := mul_nonneg hMnn hh8_nn
  have hslack : (1121952791 / 12700800 : ℝ) * M * h ^ 8 ≤ 89 * M * h ^ 8 := by
    have hle : (1121952791 / 12700800 : ℝ) ≤ 89 := by norm_num
    have hbase :
        (1121952791 / 12700800 : ℝ) * (M * h ^ 8) ≤ 89 * (M * h ^ 8) :=
      mul_le_mul_of_nonneg_right hle hMh8_nn
    have hL : (1121952791 / 12700800 : ℝ) * M * h ^ 8
        = (1121952791 / 12700800 : ℝ) * (M * h ^ 8) := by ring
    have hR : (89 : ℝ) * M * h ^ 8 = 89 * (M * h ^ 8) := by ring
    rw [hL, hR]
    exact hbase
  linarith [htri, hA_bd, hB_bd, h19087C_bd, h65112D_bd, h46461E_bd,
    h37504F_bd, h20211G_bd, h6312H_bd, hbound_alg.le, hbound_alg.ge, hslack]

/-- Pointwise AM6 truncation residual bound.  The residual expands as
`R_y(6) - R_y(5) - (19087h/60480)·R_y'(6) - (65112h/60480)·R_y'(5)
  + (46461h/60480)·R_y'(4) - (37504h/60480)·R_y'(3)
  + (20211h/60480)·R_y'(2) - (6312h/60480)·R_y'(1)`.  The exact triangle
coefficient is `1121952791/12700800 ≈ 88.34`, slackened to `89`. -/
theorem am6_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 8 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 6 * h) - y (t + 5 * h)
        - h * ((19087 / 60480) * deriv y (t + 6 * h)
              + (65112 / 60480) * deriv y (t + 5 * h)
              - (46461 / 60480) * deriv y (t + 4 * h)
              + (37504 / 60480) * deriv y (t + 3 * h)
              - (20211 / 60480) * deriv y (t + 2 * h)
              + (6312 / 60480) * deriv y (t + h)
              - (863 / 60480) * deriv y t)|
      ≤ (89 : ℝ) * M * h ^ 8 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  -- R_y(5), R_y(6): y Taylor remainders at order 8.
  have hRy5 :=
    y_eighth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRy6 :=
    y_eighth_order_taylor_remainder hy hbnd ht ht6h h6h
  -- R_y'(1), …, R_y'(6): y' Taylor remainders at order 7.
  have hRyp1 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht6h h6h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y5 := y (t + 5 * h) with hy5_def
  set y6 := y (t + 6 * h) with hy6_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set d6 := deriv y (t + 6 * h) with hd6_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd := iteratedDeriv 7 y t with hddddddd_def
  -- Algebraic identity for the AM6 residual.
  have hLTE_eq :
      y6 - y5 - h * ((19087 / 60480) * d6 + (65112 / 60480) * d5
                    - (46461 / 60480) * d4 + (37504 / 60480) * d3
                    - (20211 / 60480) * d2 + (6312 / 60480) * d1
                    - (863 / 60480) * d0)
        = (y6 - y0 - (6 * h) * d0
              - (6 * h) ^ 2 / 2 * dd
              - (6 * h) ^ 3 / 6 * ddd
              - (6 * h) ^ 4 / 24 * dddd
              - (6 * h) ^ 5 / 120 * ddddd
              - (6 * h) ^ 6 / 720 * dddddd
              - (6 * h) ^ 7 / 5040 * ddddddd)
          - (y5 - y0 - (5 * h) * d0
              - (5 * h) ^ 2 / 2 * dd
              - (5 * h) ^ 3 / 6 * ddd
              - (5 * h) ^ 4 / 24 * dddd
              - (5 * h) ^ 5 / 120 * ddddd
              - (5 * h) ^ 6 / 720 * dddddd
              - (5 * h) ^ 7 / 5040 * ddddddd)
          - (19087 * h / 60480)
              * (d6 - d0 - (6 * h) * dd
                  - (6 * h) ^ 2 / 2 * ddd
                  - (6 * h) ^ 3 / 6 * dddd
                  - (6 * h) ^ 4 / 24 * ddddd
                  - (6 * h) ^ 5 / 120 * dddddd
                  - (6 * h) ^ 6 / 720 * ddddddd)
          - (65112 * h / 60480)
              * (d5 - d0 - (5 * h) * dd
                  - (5 * h) ^ 2 / 2 * ddd
                  - (5 * h) ^ 3 / 6 * dddd
                  - (5 * h) ^ 4 / 24 * ddddd
                  - (5 * h) ^ 5 / 120 * dddddd
                  - (5 * h) ^ 6 / 720 * ddddddd)
          + (46461 * h / 60480)
              * (d4 - d0 - (4 * h) * dd
                  - (4 * h) ^ 2 / 2 * ddd
                  - (4 * h) ^ 3 / 6 * dddd
                  - (4 * h) ^ 4 / 24 * ddddd
                  - (4 * h) ^ 5 / 120 * dddddd
                  - (4 * h) ^ 6 / 720 * ddddddd)
          - (37504 * h / 60480)
              * (d3 - d0 - (3 * h) * dd
                  - (3 * h) ^ 2 / 2 * ddd
                  - (3 * h) ^ 3 / 6 * dddd
                  - (3 * h) ^ 4 / 24 * ddddd
                  - (3 * h) ^ 5 / 120 * dddddd
                  - (3 * h) ^ 6 / 720 * ddddddd)
          + (20211 * h / 60480)
              * (d2 - d0 - (2 * h) * dd
                  - (2 * h) ^ 2 / 2 * ddd
                  - (2 * h) ^ 3 / 6 * dddd
                  - (2 * h) ^ 4 / 24 * ddddd
                  - (2 * h) ^ 5 / 120 * dddddd
                  - (2 * h) ^ 6 / 720 * ddddddd)
          - (6312 * h / 60480)
              * (d1 - d0 - h * dd
                  - h ^ 2 / 2 * ddd
                  - h ^ 3 / 6 * dddd
                  - h ^ 4 / 24 * ddddd
                  - h ^ 5 / 120 * dddddd
                  - h ^ 6 / 720 * ddddddd) :=
    am6_residual_alg_identity y0 y5 y6 d0 d1 d2 d3 d4 d5 d6 dd ddd dddd ddddd
      dddddd ddddddd h
  rw [hLTE_eq]
  -- Triangle inequality.
  set A := y6 - y0 - (6 * h) * d0
            - (6 * h) ^ 2 / 2 * dd
            - (6 * h) ^ 3 / 6 * ddd
            - (6 * h) ^ 4 / 24 * dddd
            - (6 * h) ^ 5 / 120 * ddddd
            - (6 * h) ^ 6 / 720 * dddddd
            - (6 * h) ^ 7 / 5040 * ddddddd with hA_def
  set B := y5 - y0 - (5 * h) * d0
            - (5 * h) ^ 2 / 2 * dd
            - (5 * h) ^ 3 / 6 * ddd
            - (5 * h) ^ 4 / 24 * dddd
            - (5 * h) ^ 5 / 120 * ddddd
            - (5 * h) ^ 6 / 720 * dddddd
            - (5 * h) ^ 7 / 5040 * ddddddd with hB_def
  set C := d6 - d0 - (6 * h) * dd
            - (6 * h) ^ 2 / 2 * ddd
            - (6 * h) ^ 3 / 6 * dddd
            - (6 * h) ^ 4 / 24 * ddddd
            - (6 * h) ^ 5 / 120 * dddddd
            - (6 * h) ^ 6 / 720 * ddddddd with hC_def
  set D := d5 - d0 - (5 * h) * dd
            - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd
            - (5 * h) ^ 5 / 120 * dddddd
            - (5 * h) ^ 6 / 720 * ddddddd with hD_def
  set E := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd
            - (4 * h) ^ 5 / 120 * dddddd
            - (4 * h) ^ 6 / 720 * ddddddd with hE_def
  set F := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd
            - (3 * h) ^ 5 / 120 * dddddd
            - (3 * h) ^ 6 / 720 * ddddddd with hF_def
  set G := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd
            - (2 * h) ^ 5 / 120 * dddddd
            - (2 * h) ^ 6 / 720 * ddddddd with hG_def
  set H := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd
            - h ^ 5 / 120 * dddddd
            - h ^ 6 / 720 * ddddddd with hH_def
  have h19087h_nn : 0 ≤ 19087 * h / 60480 := by linarith
  have h65112h_nn : 0 ≤ 65112 * h / 60480 := by linarith
  have h46461h_nn : 0 ≤ 46461 * h / 60480 := by linarith
  have h37504h_nn : 0 ≤ 37504 * h / 60480 := by linarith
  have h20211h_nn : 0 ≤ 20211 * h / 60480 := by linarith
  have h6312h_nn : 0 ≤ 6312 * h / 60480 := by linarith
  have htri := am6_residual_eight_term_triangle A B C D E F G H h hh
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 40320 * (6 * h) ^ 8 := hRy6
  have hB_bd : |B| ≤ M / 40320 * (5 * h) ^ 8 := hRy5
  have hC_bd : |C| ≤ M / 5040 * (6 * h) ^ 7 := hRyp6
  have hD_bd : |D| ≤ M / 5040 * (5 * h) ^ 7 := hRyp5
  have hE_bd : |E| ≤ M / 5040 * (4 * h) ^ 7 := hRyp4
  have hF_bd : |F| ≤ M / 5040 * (3 * h) ^ 7 := hRyp3
  have hG_bd : |G| ≤ M / 5040 * (2 * h) ^ 7 := hRyp2
  have hH_bd : |H| ≤ M / 5040 * h ^ 7 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact am6_residual_combine hh hMnn A B C D E F G H htri
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hH_bd

/-- Uniform bound on the AM6 one-step truncation residual on a finite
horizon, given a `C^8` exact solution. -/
theorem am6_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 6) * h ≤ T →
        |adamsMoulton6.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 8 := by
  -- Compact sample interval `[t₀, t₀ + T + 1]` covers all `t + kh` with `k ≤ 6`.
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_eight_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(89 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 6) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h = ((n : ℝ) + 6) * h := by ring
    linarith
  -- Rewrite the LTE in textbook form.
  rw [am6_localTruncationError_eq]
  show |y (t + 6 * h) - y (t + 5 * h)
      - h * ((19087 / 60480) * deriv y (t + 6 * h)
            + (65112 / 60480) * deriv y (t + 5 * h)
            - (46461 / 60480) * deriv y (t + 4 * h)
            + (37504 / 60480) * deriv y (t + 3 * h)
            - (20211 / 60480) * deriv y (t + 2 * h)
            + (6312 / 60480) * deriv y (t + h)
            - (863 / 60480) * deriv y t)|
    ≤ 89 * M * h ^ 8
  exact am6_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem hh.le

/-- Headline AM6 global error bound.  Given a supplied AM6 trajectory and
starting errors bounded by `ε₀`, the scalar global error is `O(ε₀ + h^7)`
on a finite horizon. -/
theorem am6_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 8 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (19087 / 60480 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsAM6Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      |yseq 2 - y (t₀ + 2 * h)| ≤ ε₀ →
      |yseq 3 - y (t₀ + 3 * h)| ≤ ε₀ →
      |yseq 4 - y (t₀ + 4 * h)| ≤ ε₀ →
      |yseq 5 - y (t₀ + 5 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 5) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((7 * L) * T) * ε₀ + K * h ^ 7 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am6_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((7 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => |yseq k - y (t₀ + (k : ℝ) * h)| with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (max (eN k) (eN (k + 1))) (eN (k + 2)))
        (eN (k + 3))) (eN (k + 4))) (eN (k + 5))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (le_max_of_le_left (heN_nn k)))))
  -- Initial bound: EN 0 ≤ ε₀.
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (max (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4)) (eN 5)
        ≤ ε₀
    refine max_le (max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_) ?_
    · show |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀
      simpa using he0_bd
    · show |yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    · show |yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    · show |yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
    · show |yseq 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]; simpa using he4_bd
    · show |yseq 5 - y (t₀ + ((5 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((5 : ℕ) : ℝ) * h = 5 * h := by push_cast; ring
      rw [hcast]; simpa using he5_bd
  have h7L_nn : (0 : ℝ) ≤ 7 * L := by linarith
  -- The general recurrence: when (n + 6) * h ≤ T,
  -- EN (n+1) ≤ (1 + h*(7L)) * EN n + 2*C*h^8.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 6) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (7 * L)) * EN n + (2 * C) * h ^ 8 := by
    intro n hnh_le
    have honestep := am6_one_step_error_pair_bound
      (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hcast4 : ((n + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 4 := by
      push_cast; ring
    have hcast5 : ((n + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 5 := by
      push_cast; ring
    have hcast6 : ((n + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 6 := by
      push_cast; ring
    have heq_eN_n : eN n
        = |yseq n - y (t₀ + (n : ℝ) * h)| := rfl
    have heq_eN_n1 : eN (n + 1)
        = |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| := by
      show |_ - _| = _
      rw [hcast1]
    have heq_eN_n2 : eN (n + 1 + 1)
        = |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| := by
      show |_ - _| = _
      rw [hcast2]
    have heq_eN_n3 : eN (n + 1 + 1 + 1)
        = |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)| := by
      show |_ - _| = _
      rw [hcast3]
    have heq_eN_n4 : eN (n + 1 + 1 + 1 + 1)
        = |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)| := by
      show |_ - _| = _
      rw [hcast4]
    have heq_eN_n5 : eN (n + 1 + 1 + 1 + 1 + 1)
        = |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)| := by
      show |_ - _| = _
      rw [hcast5]
    have heq_eN_n6 : eN (n + 1 + 1 + 1 + 1 + 1 + 1)
        = |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)| := by
      show |_ - _| = _
      rw [hcast6]
    show max (max (max (max (max (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * (7 * L))
            * max (max (max (max (max (eN n) (eN (n + 1))) (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1))
          + (2 * C) * h ^ 8
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5,
      heq_eN_n6]
    have h2τ : 2 * |adamsMoulton6.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (2 * C) * h ^ 8 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith [this]
    linarith [honestep, h2τ]
  -- Base cases N = 0, 1, …, 5 are direct from the starting bounds.
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((7 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((7 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh7_nn : 0 ≤ h ^ 7 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((7 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((7 * L) * T) * ε₀
            + T * Real.exp ((7 * L) * T) * (2 * C) * h ^ 7 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((7 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((7 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh7_nn : 0 ≤ T * Real.exp ((7 * L) * T) * (2 * C) * h ^ 7 :=
      mul_nonneg hKnn hh7_nn
    linarith
  match N, hNh with
  | 0, _ =>
    have hbase : |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      simpa using he0_bd
    exact hbase_to_headline _ hbase
  | 1, _ =>
    have hbase : |yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    exact hbase_to_headline _ hbase
  | 2, _ =>
    have hbase : |yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    exact hbase_to_headline _ hbase
  | 3, _ =>
    have hbase : |yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
    exact hbase_to_headline _ hbase
  | 4, _ =>
    have hbase : |yseq 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]; simpa using he4_bd
    exact hbase_to_headline _ hbase
  | 5, _ =>
    have hbase : |yseq 5 - y (t₀ + ((5 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((5 : ℕ) : ℝ) * h = 5 * h := by push_cast; ring
      rw [hcast]; simpa using he5_bd
    exact hbase_to_headline _ hbase
  | N' + 6, hNh =>
    -- Apply Gronwall to EN at index N'+1, then use EN_{N'+1} ≥ e_{N'+6}.
    have hcast : (((N' + 6 : ℕ) : ℝ) + 5) = (N' : ℝ) + 11 := by
      push_cast; ring
    have hN_hyp : ((N' : ℝ) + 11) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (7 * L)) * EN n + (2 * C) * h ^ (7 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (7 + 1) = (2 * C) * h ^ 8 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 6 ≤ (N' : ℝ) + 11 := by linarith
      have h_mul : ((n : ℝ) + 6) * h ≤ ((N' : ℝ) + 11) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have hle : (N' : ℝ) + 1 ≤ (N' : ℝ) + 11 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 7 * L) (C := 2 * C) (T := T) (p := 7)
        (e := EN) (N := N' + 1)
        hh.le h7L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 6) ≤ EN (N' + 1) := by
      show eN (N' + 6)
        ≤ max (max (max (max (max (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4)))
              (eN (N' + 1 + 5))
      have heq : N' + 6 = N' + 1 + 5 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((7 * L) * T) * EN 0 ≤ Real.exp ((7 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show |yseq (N' + 6) - y (t₀ + ((N' + 6 : ℕ) : ℝ) * h)|
        ≤ Real.exp ((7 * L) * T) * ε₀
          + T * Real.exp ((7 * L) * T) * (2 * C) * h ^ 7
    have heN_eq :
        eN (N' + 6)
          = |yseq (N' + 6) - y (t₀ + ((N' + 6 : ℕ) : ℝ) * h)| := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
