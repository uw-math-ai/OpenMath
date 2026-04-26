import OpenMath.LMMTruncationOp
import OpenMath.LMMAM7Convergence
import OpenMath.AdamsMethods

/-! ## Adams--Moulton 8-step Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit Adams--Moulton
8-step method.  The chain follows the AM7 template (cycle 444) one stencil
step up: the implicit update is parameterised by a supplied trajectory
satisfying the AM8 recurrence, the local residual is bounded by tenth-order
Taylor remainders, and the global error is assembled with
`lmm_error_bound_from_local_truncation`.

The one-step Lipschitz inequality keeps the new implicit sample on the
left with factor `1 - (1070017/3628800)·h·L`.  The explicit-history weights
add up to `24484545/3628800 ≈ 6.75`, and we slacken the max-window growth
to `15·L` (the smallest integer satisfying `G ≥ 2(β + S)`).  The exact
pointwise residual coefficient is `4555920744497/6858432000 ≈ 664.28`,
slackened to `665`. -/

namespace LMM

/-- A `C^10` function has its tenth derivative bounded on every compact
interval `[a, b]`. -/
private theorem iteratedDeriv_ten_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 10 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 10 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 10 y) :=
    hy.continuous_iteratedDeriv 10 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise tenth-order Taylor (Lagrange) remainder bound: if `y` is
`C^10` and `|iteratedDeriv 10 y| ≤ M` on `[a, b]`, then for `t, t + r ∈
[a, b]` with `r ≥ 0`,
`|y(t+r) - y(t) - r·y'(t) - r²/2·y''(t) - r³/6·y'''(t) - r⁴/24·y⁽⁴⁾(t)
  - r⁵/120·y⁽⁵⁾(t) - r⁶/720·y⁽⁶⁾(t) - r⁷/5040·y⁽⁷⁾(t)
  - r⁸/40320·y⁽⁸⁾(t) - r⁹/362880·y⁽⁹⁾(t)|
  ≤ M/3628800 · r¹⁰`. -/
private theorem y_tenth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 10 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 10 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t
        - r ^ 4 / 24 * iteratedDeriv 4 y t
        - r ^ 5 / 120 * iteratedDeriv 5 y t
        - r ^ 6 / 720 * iteratedDeriv 6 y t
        - r ^ 7 / 5040 * iteratedDeriv 7 y t
        - r ^ 8 / 40320 * iteratedDeriv 8 y t
        - r ^ 9 / 362880 * iteratedDeriv 9 y t|
      ≤ M / 3628800 * r ^ 10 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 9 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 10 y ξ * r ^ 10 / 3628800 := by
    have hcdo : ContDiffOn ℝ 10 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 9) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 10 = r ^ 10 := by ring
    have hfact : (((9 + 1 : ℕ).factorial : ℝ)) = 3628800 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval y 9 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t + r ^ 2 / 2 * iteratedDeriv 2 y t
              + r ^ 3 / 6 * iteratedDeriv 3 y t
              + r ^ 4 / 24 * iteratedDeriv 4 y t
              + r ^ 5 / 120 * iteratedDeriv 5 y t
              + r ^ 6 / 720 * iteratedDeriv 6 y t
              + r ^ 7 / 5040 * iteratedDeriv 7 y t
              + r ^ 8 / 40320 * iteratedDeriv 8 y t
              + r ^ 9 / 362880 * iteratedDeriv 9 y t := by
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
    have h8 :
        iteratedDerivWithin 8 y (Set.Icc t (t + r)) t = iteratedDeriv 8 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 8) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h9 :
        iteratedDerivWithin 9 y (Set.Icc t (t + r)) t = iteratedDeriv 9 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 9) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 10 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      y (t + r) - y t - r * deriv y t
          - r ^ 2 / 2 * iteratedDeriv 2 y t
          - r ^ 3 / 6 * iteratedDeriv 3 y t
          - r ^ 4 / 24 * iteratedDeriv 4 y t
          - r ^ 5 / 120 * iteratedDeriv 5 y t
          - r ^ 6 / 720 * iteratedDeriv 6 y t
          - r ^ 7 / 5040 * iteratedDeriv 7 y t
          - r ^ 8 / 40320 * iteratedDeriv 8 y t
          - r ^ 9 / 362880 * iteratedDeriv 9 y t
        = iteratedDeriv 10 y ξ * r ^ 10 / 3628800 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 10 y ξ * r ^ 10 / 3628800
      = (iteratedDeriv 10 y ξ) * (r ^ 10 / 3628800) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 10 / 3628800)]
  calc |iteratedDeriv 10 y ξ| * (r ^ 10 / 3628800)
      ≤ M * (r ^ 10 / 3628800) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 3628800 * r ^ 10 := by ring

/-- Pointwise ninth-order Taylor (Lagrange) remainder bound for the
derivative: if `y` is `C^10` and `|iteratedDeriv 10 y| ≤ M` on `[a, b]`,
then for `t, t + r ∈ [a, b]` with `r ≥ 0`,
`|y'(t+r) - y'(t) - r·y''(t) - r²/2·y'''(t) - r³/6·y⁽⁴⁾(t)
  - r⁴/24·y⁽⁵⁾(t) - r⁵/120·y⁽⁶⁾(t) - r⁶/720·y⁽⁷⁾(t)
  - r⁷/5040·y⁽⁸⁾(t) - r⁸/40320·y⁽⁹⁾(t)|
  ≤ M/362880 · r⁹`. -/
private theorem derivY_ninth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 10 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 10 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t
        - r ^ 3 / 6 * iteratedDeriv 4 y t
        - r ^ 4 / 24 * iteratedDeriv 5 y t
        - r ^ 5 / 120 * iteratedDeriv 6 y t
        - r ^ 6 / 720 * iteratedDeriv 7 y t
        - r ^ 7 / 5040 * iteratedDeriv 8 y t
        - r ^ 8 / 40320 * iteratedDeriv 9 y t|
      ≤ M / 362880 * r ^ 9 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  have hdy : ContDiff ℝ 9 (deriv y) := hy.deriv'
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r)
          - taylorWithinEval (deriv y) 8 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 9 (deriv y) ξ * r ^ 9 / 362880 := by
    have hcdo : ContDiffOn ℝ 9 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 8) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 9 = r ^ 9 := by ring
    have hfact : (((8 + 1 : ℕ).factorial : ℝ)) = 362880 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval (deriv y) 8 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t
              + r ^ 2 / 2 * iteratedDeriv 3 y t
              + r ^ 3 / 6 * iteratedDeriv 4 y t
              + r ^ 4 / 24 * iteratedDeriv 5 y t
              + r ^ 5 / 120 * iteratedDeriv 6 y t
              + r ^ 6 / 720 * iteratedDeriv 7 y t
              + r ^ 7 / 5040 * iteratedDeriv 8 y t
              + r ^ 8 / 40320 * iteratedDeriv 9 y t := by
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
    have h7 :
        iteratedDerivWithin 7 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 8 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 7) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 8 y = iteratedDeriv 7 (deriv y) :=
        iteratedDeriv_succ' (n := 7) (f := y)
      rw [this]
    have h8 :
        iteratedDerivWithin 8 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 9 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 8) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 9 y = iteratedDeriv 8 (deriv y) :=
        iteratedDeriv_succ' (n := 8) (f := y)
      rw [this]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero,
        h0, h1, h2, h3, h4, h5, h6, h7, h8]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hidd_eq : iteratedDeriv 9 (deriv y) = iteratedDeriv 10 y := by
    have : iteratedDeriv 10 y = iteratedDeriv 9 (deriv y) :=
      iteratedDeriv_succ' (n := 9) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 10 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
          - r ^ 2 / 2 * iteratedDeriv 3 y t
          - r ^ 3 / 6 * iteratedDeriv 4 y t
          - r ^ 4 / 24 * iteratedDeriv 5 y t
          - r ^ 5 / 120 * iteratedDeriv 6 y t
          - r ^ 6 / 720 * iteratedDeriv 7 y t
          - r ^ 7 / 5040 * iteratedDeriv 8 y t
          - r ^ 8 / 40320 * iteratedDeriv 9 y t
        = iteratedDeriv 10 y ξ * r ^ 9 / 362880 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 10 y ξ * r ^ 9 / 362880
      = (iteratedDeriv 10 y ξ) * (r ^ 9 / 362880) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 9 / 362880)]
  calc |iteratedDeriv 10 y ξ| * (r ^ 9 / 362880)
      ≤ M * (r ^ 9 / 362880) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 362880 * r ^ 9 := by ring

/-- AM8 trajectory predicate:
`y_{n+8} = y_{n+7} + h(1070017/3628800 f_{n+8} + 4467094/3628800 f_{n+7}
  - 4604594/3628800 f_{n+6} + 5595358/3628800 f_{n+5}
  - 5033120/3628800 f_{n+4} + 3146338/3628800 f_{n+3}
  - 1291214/3628800 f_{n+2} + 312874/3628800 f_{n+1}
  - 33953/3628800 f_n)`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM8Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 8)
      = y (n + 7)
        + h * ((1070017 / 3628800 : ℝ) * f (t₀ + ((n : ℝ) + 8) * h) (y (n + 8))
             + (4467094 / 3628800 : ℝ) * f (t₀ + ((n : ℝ) + 7) * h) (y (n + 7))
             - (4604594 / 3628800 : ℝ) * f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             + (5595358 / 3628800 : ℝ) * f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             - (5033120 / 3628800 : ℝ) * f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             + (3146338 / 3628800 : ℝ) * f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             - (1291214 / 3628800 : ℝ) * f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             + (312874 / 3628800 : ℝ) * f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             - (33953 / 3628800 : ℝ) * f (t₀ + (n : ℝ) * h) (y n))

/-- AM8 local truncation operator reduces to the textbook residual. -/
theorem am8_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsMoulton8.localTruncationError h t y
      = y (t + 8 * h) - y (t + 7 * h)
        - h * ((1070017 / 3628800 : ℝ) * deriv y (t + 8 * h)
             + (4467094 / 3628800 : ℝ) * deriv y (t + 7 * h)
             - (4604594 / 3628800 : ℝ) * deriv y (t + 6 * h)
             + (5595358 / 3628800 : ℝ) * deriv y (t + 5 * h)
             - (5033120 / 3628800 : ℝ) * deriv y (t + 4 * h)
             + (3146338 / 3628800 : ℝ) * deriv y (t + 3 * h)
             - (1291214 / 3628800 : ℝ) * deriv y (t + 2 * h)
             + (312874 / 3628800 : ℝ) * deriv y (t + h)
             - (33953 / 3628800 : ℝ) * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsMoulton8, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  norm_num
  ring


/-- One-step AM8 Lipschitz inequality before dividing by the implicit
new-point factor.  The side condition records the small-step regime used
by the divided form. -/
theorem am8_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM8Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (1070017 / 3628800 : ℝ) * h * L)
        * |yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
      ≤ |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
        + (4467094 / 3628800 : ℝ) * h * L
            * |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
        + (4604594 / 3628800 : ℝ) * h * L
            * |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
        + (5595358 / 3628800 : ℝ) * h * L
            * |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
        + (5033120 / 3628800 : ℝ) * h * L
            * |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
        + (3146338 / 3628800 : ℝ) * h * L
            * |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
        + (1291214 / 3628800 : ℝ) * h * L
            * |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
        + (312874 / 3628800 : ℝ) * h * L
            * |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
        + (33953 / 3628800 : ℝ) * h * L
            * |yseq n - y (t₀ + (n : ℝ) * h)|
        + |adamsMoulton8.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set yn3 : ℝ := yseq (n + 3) with hyn3_def
  set yn4 : ℝ := yseq (n + 4) with hyn4_def
  set yn5 : ℝ := yseq (n + 5) with hyn5_def
  set yn6 : ℝ := yseq (n + 6) with hyn6_def
  set yn7 : ℝ := yseq (n + 7) with hyn7_def
  set yn8 : ℝ := yseq (n + 8) with hyn8_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set tn8 : ℝ := t₀ + ((n : ℝ) + 8) * h with htn8_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set zn6 : ℝ := y tn6 with hzn6_def
  set zn7 : ℝ := y tn7 with hzn7_def
  set zn8 : ℝ := y tn8 with hzn8_def
  set τ : ℝ := adamsMoulton8.localTruncationError h tn y with hτ_def
  have _hsmall_record : (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2 := hsmall
  have hstep : yn8
      = yn7
        + h * ((1070017 / 3628800 : ℝ) * f tn8 yn8
             + (4467094 / 3628800 : ℝ) * f tn7 yn7
             - (4604594 / 3628800 : ℝ) * f tn6 yn6
             + (5595358 / 3628800 : ℝ) * f tn5 yn5
             - (5033120 / 3628800 : ℝ) * f tn4 yn4
             + (3146338 / 3628800 : ℝ) * f tn3 yn3
             - (1291214 / 3628800 : ℝ) * f tn2 yn2
             + (312874 / 3628800 : ℝ) * f tn1 yn1
             - (33953 / 3628800 : ℝ) * f tn yn) := by
    simpa [hyn8_def, hyn7_def, hyn6_def, hyn5_def, hyn4_def, hyn3_def, hyn2_def,
      hyn1_def, hyn_def, htn8_def, htn7_def, htn6_def, htn5_def, htn4_def,
      htn3_def, htn2_def, htn1_def, htn_def] using hy.recurrence n
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
  have hτ_eq : τ = zn8 - zn7
      - h * ((1070017 / 3628800 : ℝ) * f tn8 zn8
             + (4467094 / 3628800 : ℝ) * f tn7 zn7
             - (4604594 / 3628800 : ℝ) * f tn6 zn6
             + (5595358 / 3628800 : ℝ) * f tn5 zn5
             - (5033120 / 3628800 : ℝ) * f tn4 zn4
             + (3146338 / 3628800 : ℝ) * f tn3 zn3
             - (1291214 / 3628800 : ℝ) * f tn2 zn2
             + (312874 / 3628800 : ℝ) * f tn1 zn1
             - (33953 / 3628800 : ℝ) * f tn zn) := by
    show adamsMoulton8.localTruncationError h tn y = _
    rw [am8_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h,
      htn_5h, htn_6h, htn_7h, htn_8h, hyf tn8, hyf tn7, hyf tn6, hyf tn5,
      hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  have halg : yn8 - zn8
      = (yn7 - zn7)
        + (1070017 / 3628800 : ℝ) * h * (f tn8 yn8 - f tn8 zn8)
        + (4467094 / 3628800 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)
        - (4604594 / 3628800 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)
        + (5595358 / 3628800 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
        - (5033120 / 3628800 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        + (3146338 / 3628800 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        - (1291214 / 3628800 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        + (312874 / 3628800 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        - (33953 / 3628800 : ℝ) * h * (f tn yn - f tn zn)
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
  have hLip8 : |f tn8 yn8 - f tn8 zn8| ≤ L * |yn8 - zn8| :=
    hf tn8 yn8 zn8
  have hLip7 : |f tn7 yn7 - f tn7 zn7| ≤ L * |yn7 - zn7| :=
    hf tn7 yn7 zn7
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
  have h1070017_nn : 0 ≤ (1070017 / 3628800 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h4467094_nn : 0 ≤ (4467094 / 3628800 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h4604594_nn : 0 ≤ (4604594 / 3628800 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h5595358_nn : 0 ≤ (5595358 / 3628800 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h5033120_nn : 0 ≤ (5033120 / 3628800 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h3146338_nn : 0 ≤ (3146338 / 3628800 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h1291214_nn : 0 ≤ (1291214 / 3628800 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h312874_nn : 0 ≤ (312874 / 3628800 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h33953_nn : 0 ≤ (33953 / 3628800 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h1070017_abs :
      |(1070017 / 3628800 : ℝ) * h * (f tn8 yn8 - f tn8 zn8)|
      ≤ (1070017 / 3628800 : ℝ) * h * L * |yn8 - zn8| := by
    rw [abs_mul, abs_of_nonneg h1070017_nn]
    calc (1070017 / 3628800 : ℝ) * h * |f tn8 yn8 - f tn8 zn8|
        ≤ (1070017 / 3628800 : ℝ) * h * (L * |yn8 - zn8|) :=
          mul_le_mul_of_nonneg_left hLip8 h1070017_nn
      _ = (1070017 / 3628800 : ℝ) * h * L * |yn8 - zn8| := by ring
  have h4467094_abs :
      |(4467094 / 3628800 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)|
      ≤ (4467094 / 3628800 : ℝ) * h * L * |yn7 - zn7| := by
    rw [abs_mul, abs_of_nonneg h4467094_nn]
    calc (4467094 / 3628800 : ℝ) * h * |f tn7 yn7 - f tn7 zn7|
        ≤ (4467094 / 3628800 : ℝ) * h * (L * |yn7 - zn7|) :=
          mul_le_mul_of_nonneg_left hLip7 h4467094_nn
      _ = (4467094 / 3628800 : ℝ) * h * L * |yn7 - zn7| := by ring
  have h4604594_abs :
      |(4604594 / 3628800 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)|
      ≤ (4604594 / 3628800 : ℝ) * h * L * |yn6 - zn6| := by
    rw [abs_mul, abs_of_nonneg h4604594_nn]
    calc (4604594 / 3628800 : ℝ) * h * |f tn6 yn6 - f tn6 zn6|
        ≤ (4604594 / 3628800 : ℝ) * h * (L * |yn6 - zn6|) :=
          mul_le_mul_of_nonneg_left hLip6 h4604594_nn
      _ = (4604594 / 3628800 : ℝ) * h * L * |yn6 - zn6| := by ring
  have h5595358_abs :
      |(5595358 / 3628800 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
      ≤ (5595358 / 3628800 : ℝ) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg h5595358_nn]
    calc (5595358 / 3628800 : ℝ) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (5595358 / 3628800 : ℝ) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip5 h5595358_nn
      _ = (5595358 / 3628800 : ℝ) * h * L * |yn5 - zn5| := by ring
  have h5033120_abs :
      |(5033120 / 3628800 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (5033120 / 3628800 : ℝ) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h5033120_nn]
    calc (5033120 / 3628800 : ℝ) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (5033120 / 3628800 : ℝ) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 h5033120_nn
      _ = (5033120 / 3628800 : ℝ) * h * L * |yn4 - zn4| := by ring
  have h3146338_abs :
      |(3146338 / 3628800 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (3146338 / 3628800 : ℝ) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h3146338_nn]
    calc (3146338 / 3628800 : ℝ) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (3146338 / 3628800 : ℝ) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h3146338_nn
      _ = (3146338 / 3628800 : ℝ) * h * L * |yn3 - zn3| := by ring
  have h1291214_abs :
      |(1291214 / 3628800 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (1291214 / 3628800 : ℝ) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h1291214_nn]
    calc (1291214 / 3628800 : ℝ) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (1291214 / 3628800 : ℝ) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h1291214_nn
      _ = (1291214 / 3628800 : ℝ) * h * L * |yn2 - zn2| := by ring
  have h312874_abs :
      |(312874 / 3628800 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (312874 / 3628800 : ℝ) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h312874_nn]
    calc (312874 / 3628800 : ℝ) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (312874 / 3628800 : ℝ) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h312874_nn
      _ = (312874 / 3628800 : ℝ) * h * L * |yn1 - zn1| := by ring
  have h33953_abs :
      |(33953 / 3628800 : ℝ) * h * (f tn yn - f tn zn)|
      ≤ (33953 / 3628800 : ℝ) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h33953_nn]
    calc (33953 / 3628800 : ℝ) * h * |f tn yn - f tn zn|
        ≤ (33953 / 3628800 : ℝ) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h33953_nn
      _ = (33953 / 3628800 : ℝ) * h * L * |yn - zn| := by ring
  -- Triangle inequality for eleven terms (10 algebraic + τ).
  -- Pattern: A + B + C - D + E - F + G - H + I - J - K
  have htri_terms (A B C D E F G H I J K : ℝ) :
      |A + B + C - D + E - F + G - H + I - J - K|
        ≤ |A| + |B| + |C| + |D| + |E| + |F| + |G| + |H| + |I| + |J| + |K| := by
    have h1 : |A + B + C - D + E - F + G - H + I - J - K|
        ≤ |A + B + C - D + E - F + G - H + I - J| + |K| := abs_sub _ _
    have h2 : |A + B + C - D + E - F + G - H + I - J|
        ≤ |A + B + C - D + E - F + G - H + I| + |J| := abs_sub _ _
    have h3 : |A + B + C - D + E - F + G - H + I|
        ≤ |A + B + C - D + E - F + G - H| + |I| := abs_add_le _ _
    have h4 : |A + B + C - D + E - F + G - H|
        ≤ |A + B + C - D + E - F + G| + |H| := abs_sub _ _
    have h5 : |A + B + C - D + E - F + G|
        ≤ |A + B + C - D + E - F| + |G| := abs_add_le _ _
    have h6 : |A + B + C - D + E - F|
        ≤ |A + B + C - D + E| + |F| := abs_sub _ _
    have h7 : |A + B + C - D + E|
        ≤ |A + B + C - D| + |E| := abs_add_le _ _
    have h8 : |A + B + C - D| ≤ |A + B + C| + |D| := abs_sub _ _
    have h9 : |A + B + C| ≤ |A + B| + |C| := abs_add_le _ _
    have h10 : |A + B| ≤ |A| + |B| := abs_add_le _ _
    linarith
  have htri :
      |(yn7 - zn7)
        + (1070017 / 3628800 : ℝ) * h * (f tn8 yn8 - f tn8 zn8)
        + (4467094 / 3628800 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)
        - (4604594 / 3628800 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)
        + (5595358 / 3628800 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
        - (5033120 / 3628800 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        + (3146338 / 3628800 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        - (1291214 / 3628800 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        + (312874 / 3628800 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        - (33953 / 3628800 : ℝ) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn7 - zn7|
          + |(1070017 / 3628800 : ℝ) * h * (f tn8 yn8 - f tn8 zn8)|
          + |(4467094 / 3628800 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)|
          + |(4604594 / 3628800 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(5595358 / 3628800 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(5033120 / 3628800 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(3146338 / 3628800 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(1291214 / 3628800 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(312874 / 3628800 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(33953 / 3628800 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| :=
    htri_terms (yn7 - zn7)
      ((1070017 / 3628800 : ℝ) * h * (f tn8 yn8 - f tn8 zn8))
      ((4467094 / 3628800 : ℝ) * h * (f tn7 yn7 - f tn7 zn7))
      ((4604594 / 3628800 : ℝ) * h * (f tn6 yn6 - f tn6 zn6))
      ((5595358 / 3628800 : ℝ) * h * (f tn5 yn5 - f tn5 zn5))
      ((5033120 / 3628800 : ℝ) * h * (f tn4 yn4 - f tn4 zn4))
      ((3146338 / 3628800 : ℝ) * h * (f tn3 yn3 - f tn3 zn3))
      ((1291214 / 3628800 : ℝ) * h * (f tn2 yn2 - f tn2 zn2))
      ((312874 / 3628800 : ℝ) * h * (f tn1 yn1 - f tn1 zn1))
      ((33953 / 3628800 : ℝ) * h * (f tn yn - f tn zn)) τ
  have hmain :
      |yn8 - zn8|
        ≤ |yn7 - zn7|
          + (1070017 / 3628800 : ℝ) * h * L * |yn8 - zn8|
          + (4467094 / 3628800 : ℝ) * h * L * |yn7 - zn7|
          + (4604594 / 3628800 : ℝ) * h * L * |yn6 - zn6|
          + (5595358 / 3628800 : ℝ) * h * L * |yn5 - zn5|
          + (5033120 / 3628800 : ℝ) * h * L * |yn4 - zn4|
          + (3146338 / 3628800 : ℝ) * h * L * |yn3 - zn3|
          + (1291214 / 3628800 : ℝ) * h * L * |yn2 - zn2|
          + (312874 / 3628800 : ℝ) * h * L * |yn1 - zn1|
          + (33953 / 3628800 : ℝ) * h * L * |yn - zn|
          + |τ| := by
    calc |yn8 - zn8|
        = |(yn7 - zn7)
            + (1070017 / 3628800 : ℝ) * h * (f tn8 yn8 - f tn8 zn8)
            + (4467094 / 3628800 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)
            - (4604594 / 3628800 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)
            + (5595358 / 3628800 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
            - (5033120 / 3628800 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
            + (3146338 / 3628800 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
            - (1291214 / 3628800 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
            + (312874 / 3628800 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
            - (33953 / 3628800 : ℝ) * h * (f tn yn - f tn zn)
            - τ| := by rw [halg]
      _ ≤ |yn7 - zn7|
          + |(1070017 / 3628800 : ℝ) * h * (f tn8 yn8 - f tn8 zn8)|
          + |(4467094 / 3628800 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)|
          + |(4604594 / 3628800 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(5595358 / 3628800 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(5033120 / 3628800 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(3146338 / 3628800 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(1291214 / 3628800 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(312874 / 3628800 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(33953 / 3628800 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| := htri
      _ ≤ |yn7 - zn7|
          + (1070017 / 3628800 : ℝ) * h * L * |yn8 - zn8|
          + (4467094 / 3628800 : ℝ) * h * L * |yn7 - zn7|
          + (4604594 / 3628800 : ℝ) * h * L * |yn6 - zn6|
          + (5595358 / 3628800 : ℝ) * h * L * |yn5 - zn5|
          + (5033120 / 3628800 : ℝ) * h * L * |yn4 - zn4|
          + (3146338 / 3628800 : ℝ) * h * L * |yn3 - zn3|
          + (1291214 / 3628800 : ℝ) * h * L * |yn2 - zn2|
          + (312874 / 3628800 : ℝ) * h * L * |yn1 - zn1|
          + (33953 / 3628800 : ℝ) * h * L * |yn - zn|
          + |τ| := by
        linarith [h1070017_abs, h4467094_abs, h4604594_abs, h5595358_abs,
          h5033120_abs, h3146338_abs, h1291214_abs, h312874_abs, h33953_abs]
  linarith [hmain]

/-- Divided one-step AM8 error bound.  The explicit AM8 weights contribute
`24484545/3628800`; after dividing by the implicit `(1 - (1070017/3628800)hL)`
factor, we slacken the max-window growth to `15L` and the residual
coefficient to `2`. -/
theorem am8_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM8Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
      ≤ (1 + h * (15 * L))
            * max (max (max (max (max (max (max
                |yseq n - y (t₀ + (n : ℝ) * h)|
                |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|)
                |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
                |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
                |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
                |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
                |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|)
                |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
        + 2 * |adamsMoulton8.localTruncationError h
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
  set en7 : ℝ :=
    |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)| with hen7_def
  set en8 : ℝ :=
    |yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)| with hen8_def
  set τabs : ℝ :=
    |adamsMoulton8.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ :=
    max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7
    with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hen7_nn : 0 ≤ en7 := abs_nonneg _
  have hen8_nn : 0 ≤ en8 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _)))))))
  have hen_le_E : en ≤ E :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen3_le_E : en3 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen4_le_E : en4 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen5_le_E : en5 ≤ E :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen6_le_E : en6 ≤ E := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen7_le_E : en7 ≤ E := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 1814400 / 1070017 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (1070017 / 3628800 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (1070017 / 3628800 : ℝ) * h * L) * en8
        ≤ en7
          + (4467094 / 3628800 : ℝ) * h * L * en7
          + (4604594 / 3628800 : ℝ) * h * L * en6
          + (5595358 / 3628800 : ℝ) * h * L * en5
          + (5033120 / 3628800 : ℝ) * h * L * en4
          + (3146338 / 3628800 : ℝ) * h * L * en3
          + (1291214 / 3628800 : ℝ) * h * L * en2
          + (312874 / 3628800 : ℝ) * h * L * en1
          + (33953 / 3628800 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hτabs_def]
      using
      (am8_one_step_lipschitz (h := h) (L := L) hh hsmall hf t₀ hy y hyf n)
  have h4467094_nn : 0 ≤ (4467094 / 3628800 : ℝ) * h * L := by positivity
  have h4604594_nn : 0 ≤ (4604594 / 3628800 : ℝ) * h * L := by positivity
  have h5595358_nn : 0 ≤ (5595358 / 3628800 : ℝ) * h * L := by positivity
  have h5033120_nn : 0 ≤ (5033120 / 3628800 : ℝ) * h * L := by positivity
  have h3146338_nn : 0 ≤ (3146338 / 3628800 : ℝ) * h * L := by positivity
  have h1291214_nn : 0 ≤ (1291214 / 3628800 : ℝ) * h * L := by positivity
  have h312874_nn : 0 ≤ (312874 / 3628800 : ℝ) * h * L := by positivity
  have h33953_nn : 0 ≤ (33953 / 3628800 : ℝ) * h * L := by positivity
  have h4467094_le :
      (4467094 / 3628800 : ℝ) * h * L * en7
        ≤ (4467094 / 3628800 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen7_le_E h4467094_nn
  have h4604594_le :
      (4604594 / 3628800 : ℝ) * h * L * en6
        ≤ (4604594 / 3628800 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen6_le_E h4604594_nn
  have h5595358_le :
      (5595358 / 3628800 : ℝ) * h * L * en5
        ≤ (5595358 / 3628800 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen5_le_E h5595358_nn
  have h5033120_le :
      (5033120 / 3628800 : ℝ) * h * L * en4
        ≤ (5033120 / 3628800 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen4_le_E h5033120_nn
  have h3146338_le :
      (3146338 / 3628800 : ℝ) * h * L * en3
        ≤ (3146338 / 3628800 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen3_le_E h3146338_nn
  have h1291214_le :
      (1291214 / 3628800 : ℝ) * h * L * en2
        ≤ (1291214 / 3628800 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen2_le_E h1291214_nn
  have h312874_le :
      (312874 / 3628800 : ℝ) * h * L * en1
        ≤ (312874 / 3628800 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen1_le_E h312874_nn
  have h33953_le :
      (33953 / 3628800 : ℝ) * h * L * en
        ≤ (33953 / 3628800 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen_le_E h33953_nn
  have hR_le :
      en7
          + (4467094 / 3628800 : ℝ) * h * L * en7
          + (4604594 / 3628800 : ℝ) * h * L * en6
          + (5595358 / 3628800 : ℝ) * h * L * en5
          + (5033120 / 3628800 : ℝ) * h * L * en4
          + (3146338 / 3628800 : ℝ) * h * L * en3
          + (1291214 / 3628800 : ℝ) * h * L * en2
          + (312874 / 3628800 : ℝ) * h * L * en1
          + (33953 / 3628800 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (24484545 / 3628800 : ℝ) * (h * L)) * E + τabs := by
    have h_alg :
        E + (4467094 / 3628800 : ℝ) * h * L * E
            + (4604594 / 3628800 : ℝ) * h * L * E
            + (5595358 / 3628800 : ℝ) * h * L * E
            + (5033120 / 3628800 : ℝ) * h * L * E
            + (3146338 / 3628800 : ℝ) * h * L * E
            + (1291214 / 3628800 : ℝ) * h * L * E
            + (312874 / 3628800 : ℝ) * h * L * E
            + (33953 / 3628800 : ℝ) * h * L * E + τabs
          = (1 + (24484545 / 3628800 : ℝ) * (h * L)) * E + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (24484545 / 3628800 : ℝ) * (h * L)
        ≤ (1 - (1070017 / 3628800 : ℝ) * h * L) * (1 + h * (15 * L)) := by
    have hxL_eq :
        (1 - (1070017 / 3628800 : ℝ) * h * L) * (1 + h * (15 * L))
          - (1 + (24484545 / 3628800 : ℝ) * (h * L))
          = (h * L) / 3628800 * (28877438 - 16050255 * (h * L)) := by ring
    have hpos : 0 ≤ 28877438 - 16050255 * (h * L) := by
      have hbound : 16050255 * (h * L) ≤ 16050255 * (1814400 / 1070017) := by
        have h16050255_nn : (0 : ℝ) ≤ 16050255 := by norm_num
        exact mul_le_mul_of_nonneg_left hx_small h16050255_nn
      have hnum : (16050255 : ℝ) * (1814400 / 1070017) ≤ 28877438 := by
        norm_num
      linarith
    have hprod : 0 ≤ (h * L) / 3628800 * (28877438 - 16050255 * (h * L)) := by
      apply mul_nonneg
      · positivity
      · exact hpos
    linarith
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (1070017 / 3628800 : ℝ) * h * L) * 2 := by
    linarith [hsmall]
  have hE_part :
      (1 + (24484545 / 3628800 : ℝ) * (h * L)) * E
        ≤ ((1 - (1070017 / 3628800 : ℝ) * h * L) * (1 + h * (15 * L))) * E :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (1070017 / 3628800 : ℝ) * h * L) * 2) * τabs :=
    by simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (24484545 / 3628800 : ℝ) * (h * L)) * E + τabs
        ≤ (1 - (1070017 / 3628800 : ℝ) * h * L)
            * ((1 + h * (15 * L)) * E + 2 * τabs) := by
    have hsplit :
        (1 - (1070017 / 3628800 : ℝ) * h * L)
            * ((1 + h * (15 * L)) * E + 2 * τabs)
          = ((1 - (1070017 / 3628800 : ℝ) * h * L) * (1 + h * (15 * L))) * E
              + ((1 - (1070017 / 3628800 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (1070017 / 3628800 : ℝ) * h * L) * en8
        ≤ (1 - (1070017 / 3628800 : ℝ) * h * L)
            * ((1 + h * (15 * L)) * E + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  have hcancel :
      en8 ≤ (1 + h * (15 * L)) * E + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  exact hcancel

/-- Max-norm AM8 one-step recurrence on the rolling 8-window
`(en, en1, en2, en3, en4, en5, en6, en7)`. -/
theorem am8_one_step_error_pair_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM8Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max
          |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
          |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
          |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
          |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|)
          |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|)
          |yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
      ≤ (1 + h * (15 * L))
            * max (max (max (max (max (max (max
                |yseq n - y (t₀ + (n : ℝ) * h)|
                |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|)
                |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
                |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
                |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
                |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
                |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|)
                |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
        + 2 * |adamsMoulton8.localTruncationError h
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
  set en7 : ℝ :=
    |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)| with hen7_def
  set en8 : ℝ :=
    |yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)| with hen8_def
  set τabs : ℝ :=
    |adamsMoulton8.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ :=
    max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7
    with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hen7_nn : 0 ≤ en7 := abs_nonneg _
  have hen8_nn : 0 ≤ en8 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _)))))))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _)
              (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen3_le_E : en3 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen4_le_E : en4 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen5_le_E : en5 ≤ E :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen6_le_E : en6 ≤ E := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen7_le_E : en7 ≤ E := le_max_right _ _
  have h15hL_nn : 0 ≤ h * (15 * L) := by positivity
  have hen8_bd :
      en8 ≤ (1 + h * (15 * L)) * E + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hen8_def, hτabs_def, hE_def]
      using
      (am8_one_step_error_bound (h := h) (L := L) hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : E ≤ (1 + h * (15 * L)) * E := by
    have hone : (1 : ℝ) * E ≤ (1 + h * (15 * L)) * E :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (15 * L)) * E + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (15 * L)) * E + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (15 * L)) * E + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  have hen4_bd : en4 ≤ (1 + h * (15 * L)) * E + 2 * τabs := by
    linarith [hen4_le_E, hE_le_grow]
  have hen5_bd : en5 ≤ (1 + h * (15 * L)) * E + 2 * τabs := by
    linarith [hen5_le_E, hE_le_grow]
  have hen6_bd : en6 ≤ (1 + h * (15 * L)) * E + 2 * τabs := by
    linarith [hen6_le_E, hE_le_grow]
  have hen7_bd : en7 ≤ (1 + h * (15 * L)) * E + 2 * τabs := by
    linarith [hen7_le_E, hE_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd)
    hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd

/-- Pure algebraic identity: the AM8 residual rewrites as a signed sum of
ten Taylor remainders. Extracted as a stand-alone lemma so the kernel
checks the (large degree-10) `ring` proof term in isolation. -/
private lemma am8_residual_alg_identity
    (y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7 d8 dd ddd dddd ddddd dddddd ddddddd
        dddddddd ddddddddd h : ℝ) :
    y8 - y7 - h * ((1070017 / 3628800) * d8 + (4467094 / 3628800) * d7
                  - (4604594 / 3628800) * d6 + (5595358 / 3628800) * d5
                  - (5033120 / 3628800) * d4 + (3146338 / 3628800) * d3
                  - (1291214 / 3628800) * d2 + (312874 / 3628800) * d1
                  - (33953 / 3628800) * d0)
      = (y8 - y0 - (8 * h) * d0
            - (8 * h) ^ 2 / 2 * dd
            - (8 * h) ^ 3 / 6 * ddd
            - (8 * h) ^ 4 / 24 * dddd
            - (8 * h) ^ 5 / 120 * ddddd
            - (8 * h) ^ 6 / 720 * dddddd
            - (8 * h) ^ 7 / 5040 * ddddddd
            - (8 * h) ^ 8 / 40320 * dddddddd
            - (8 * h) ^ 9 / 362880 * ddddddddd)
        - (y7 - y0 - (7 * h) * d0
            - (7 * h) ^ 2 / 2 * dd
            - (7 * h) ^ 3 / 6 * ddd
            - (7 * h) ^ 4 / 24 * dddd
            - (7 * h) ^ 5 / 120 * ddddd
            - (7 * h) ^ 6 / 720 * dddddd
            - (7 * h) ^ 7 / 5040 * ddddddd
            - (7 * h) ^ 8 / 40320 * dddddddd
            - (7 * h) ^ 9 / 362880 * ddddddddd)
        - (1070017 * h / 3628800)
            * (d8 - d0 - (8 * h) * dd
                - (8 * h) ^ 2 / 2 * ddd
                - (8 * h) ^ 3 / 6 * dddd
                - (8 * h) ^ 4 / 24 * ddddd
                - (8 * h) ^ 5 / 120 * dddddd
                - (8 * h) ^ 6 / 720 * ddddddd
                - (8 * h) ^ 7 / 5040 * dddddddd
                - (8 * h) ^ 8 / 40320 * ddddddddd)
        - (4467094 * h / 3628800)
            * (d7 - d0 - (7 * h) * dd
                - (7 * h) ^ 2 / 2 * ddd
                - (7 * h) ^ 3 / 6 * dddd
                - (7 * h) ^ 4 / 24 * ddddd
                - (7 * h) ^ 5 / 120 * dddddd
                - (7 * h) ^ 6 / 720 * ddddddd
                - (7 * h) ^ 7 / 5040 * dddddddd
                - (7 * h) ^ 8 / 40320 * ddddddddd)
        + (4604594 * h / 3628800)
            * (d6 - d0 - (6 * h) * dd
                - (6 * h) ^ 2 / 2 * ddd
                - (6 * h) ^ 3 / 6 * dddd
                - (6 * h) ^ 4 / 24 * ddddd
                - (6 * h) ^ 5 / 120 * dddddd
                - (6 * h) ^ 6 / 720 * ddddddd
                - (6 * h) ^ 7 / 5040 * dddddddd
                - (6 * h) ^ 8 / 40320 * ddddddddd)
        - (5595358 * h / 3628800)
            * (d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd
                - (5 * h) ^ 6 / 720 * ddddddd
                - (5 * h) ^ 7 / 5040 * dddddddd
                - (5 * h) ^ 8 / 40320 * ddddddddd)
        + (5033120 * h / 3628800)
            * (d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd
                - (4 * h) ^ 6 / 720 * ddddddd
                - (4 * h) ^ 7 / 5040 * dddddddd
                - (4 * h) ^ 8 / 40320 * ddddddddd)
        - (3146338 * h / 3628800)
            * (d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd
                - (3 * h) ^ 6 / 720 * ddddddd
                - (3 * h) ^ 7 / 5040 * dddddddd
                - (3 * h) ^ 8 / 40320 * ddddddddd)
        + (1291214 * h / 3628800)
            * (d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd
                - (2 * h) ^ 6 / 720 * ddddddd
                - (2 * h) ^ 7 / 5040 * dddddddd
                - (2 * h) ^ 8 / 40320 * ddddddddd)
        - (312874 * h / 3628800)
            * (d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd
                - h ^ 6 / 720 * ddddddd
                - h ^ 7 / 5040 * dddddddd
                - h ^ 8 / 40320 * ddddddddd) := by
  ring

/-- Pure algebraic identity: the sum of the ten scaled Lagrange
remainder bounds equals `(4555920744497/6858432000) · M · h^10`. -/
private lemma am8_residual_bound_alg_identity (M h : ℝ) :
    M / 3628800 * (8 * h) ^ 10 + M / 3628800 * (7 * h) ^ 10
      + (1070017 * h / 3628800) * (M / 362880 * (8 * h) ^ 9)
      + (4467094 * h / 3628800) * (M / 362880 * (7 * h) ^ 9)
      + (4604594 * h / 3628800) * (M / 362880 * (6 * h) ^ 9)
      + (5595358 * h / 3628800) * (M / 362880 * (5 * h) ^ 9)
      + (5033120 * h / 3628800) * (M / 362880 * (4 * h) ^ 9)
      + (3146338 * h / 3628800) * (M / 362880 * (3 * h) ^ 9)
      + (1291214 * h / 3628800) * (M / 362880 * (2 * h) ^ 9)
      + (312874 * h / 3628800) * (M / 362880 * h ^ 9)
      = (4555920744497 / 6858432000 : ℝ) * M * h ^ 10 := by
  ring

/-- Triangle inequality for the ten-term AM8 residual chunk. -/
private lemma am8_residual_ten_term_triangle
    (A B C D E F G H I J h : ℝ) (hh : 0 ≤ h) :
    |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
        + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
        + (5033120 * h / 3628800) * G - (3146338 * h / 3628800) * H
        + (1291214 * h / 3628800) * I - (312874 * h / 3628800) * J|
      ≤ |A| + |B| + (1070017 * h / 3628800) * |C|
          + (4467094 * h / 3628800) * |D| + (4604594 * h / 3628800) * |E|
          + (5595358 * h / 3628800) * |F| + (5033120 * h / 3628800) * |G|
          + (3146338 * h / 3628800) * |H| + (1291214 * h / 3628800) * |I|
          + (312874 * h / 3628800) * |J| := by
  have h1070017h_nn : 0 ≤ 1070017 * h / 3628800 := by linarith
  have h4467094h_nn : 0 ≤ 4467094 * h / 3628800 := by linarith
  have h4604594h_nn : 0 ≤ 4604594 * h / 3628800 := by linarith
  have h5595358h_nn : 0 ≤ 5595358 * h / 3628800 := by linarith
  have h5033120h_nn : 0 ≤ 5033120 * h / 3628800 := by linarith
  have h3146338h_nn : 0 ≤ 3146338 * h / 3628800 := by linarith
  have h1291214h_nn : 0 ≤ 1291214 * h / 3628800 := by linarith
  have h312874h_nn : 0 ≤ 312874 * h / 3628800 := by linarith
  have habs1070017 :
      |(1070017 * h / 3628800) * C| = (1070017 * h / 3628800) * |C| := by
    rw [abs_mul, abs_of_nonneg h1070017h_nn]
  have habs4467094 :
      |(4467094 * h / 3628800) * D| = (4467094 * h / 3628800) * |D| := by
    rw [abs_mul, abs_of_nonneg h4467094h_nn]
  have habs4604594 :
      |(4604594 * h / 3628800) * E| = (4604594 * h / 3628800) * |E| := by
    rw [abs_mul, abs_of_nonneg h4604594h_nn]
  have habs5595358 :
      |(5595358 * h / 3628800) * F| = (5595358 * h / 3628800) * |F| := by
    rw [abs_mul, abs_of_nonneg h5595358h_nn]
  have habs5033120 :
      |(5033120 * h / 3628800) * G| = (5033120 * h / 3628800) * |G| := by
    rw [abs_mul, abs_of_nonneg h5033120h_nn]
  have habs3146338 :
      |(3146338 * h / 3628800) * H| = (3146338 * h / 3628800) * |H| := by
    rw [abs_mul, abs_of_nonneg h3146338h_nn]
  have habs1291214 :
      |(1291214 * h / 3628800) * I| = (1291214 * h / 3628800) * |I| := by
    rw [abs_mul, abs_of_nonneg h1291214h_nn]
  have habs312874 :
      |(312874 * h / 3628800) * J| = (312874 * h / 3628800) * |J| := by
    rw [abs_mul, abs_of_nonneg h312874h_nn]
  -- Pattern inside |·|: A - B - α1 C - α2 D + α3 E - α4 F + α5 G - α6 H + α7 I - α8 J
  have h1 : |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
                + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
                + (5033120 * h / 3628800) * G - (3146338 * h / 3628800) * H
                + (1291214 * h / 3628800) * I - (312874 * h / 3628800) * J|
      ≤ |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
            + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
            + (5033120 * h / 3628800) * G - (3146338 * h / 3628800) * H
            + (1291214 * h / 3628800) * I|
        + |(312874 * h / 3628800) * J| := abs_sub _ _
  have h2 : |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
                + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
                + (5033120 * h / 3628800) * G - (3146338 * h / 3628800) * H
                + (1291214 * h / 3628800) * I|
      ≤ |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
            + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
            + (5033120 * h / 3628800) * G - (3146338 * h / 3628800) * H|
        + |(1291214 * h / 3628800) * I| := abs_add_le _ _
  have h3 : |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
                + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
                + (5033120 * h / 3628800) * G - (3146338 * h / 3628800) * H|
      ≤ |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
            + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
            + (5033120 * h / 3628800) * G|
        + |(3146338 * h / 3628800) * H| := abs_sub _ _
  have h4 : |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
                + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
                + (5033120 * h / 3628800) * G|
      ≤ |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
            + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F|
        + |(5033120 * h / 3628800) * G| := abs_add_le _ _
  have h5 : |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
                + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F|
      ≤ |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
            + (4604594 * h / 3628800) * E|
        + |(5595358 * h / 3628800) * F| := abs_sub _ _
  have h6 : |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
                + (4604594 * h / 3628800) * E|
      ≤ |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D|
        + |(4604594 * h / 3628800) * E| := abs_add_le _ _
  have h7 : |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D|
      ≤ |A - B - (1070017 * h / 3628800) * C| + |(4467094 * h / 3628800) * D| :=
    abs_sub _ _
  have h8 : |A - B - (1070017 * h / 3628800) * C|
      ≤ |A - B| + |(1070017 * h / 3628800) * C| := abs_sub _ _
  have h9 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith [habs1070017.le, habs1070017.ge, habs4467094.le, habs4467094.ge,
    habs4604594.le, habs4604594.ge, habs5595358.le, habs5595358.ge,
    habs5033120.le, habs5033120.ge, habs3146338.le, habs3146338.ge,
    habs1291214.le, habs1291214.ge, habs312874.le, habs312874.ge]

/-- Combine the ten-term triangle inequality with the absolute bounds
on each piece to obtain the `665 · M · h^10` final bound.  Extracted as a
helper so the kernel verifies the `linarith` proof term in isolation, not
inside the heavy `am8_pointwise_residual_bound` context. -/
private lemma am8_residual_combine
    {M h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D E F G H I J : ℝ)
    (htri : |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
              + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
              + (5033120 * h / 3628800) * G - (3146338 * h / 3628800) * H
              + (1291214 * h / 3628800) * I - (312874 * h / 3628800) * J|
            ≤ |A| + |B| + (1070017 * h / 3628800) * |C|
              + (4467094 * h / 3628800) * |D| + (4604594 * h / 3628800) * |E|
              + (5595358 * h / 3628800) * |F| + (5033120 * h / 3628800) * |G|
              + (3146338 * h / 3628800) * |H| + (1291214 * h / 3628800) * |I|
              + (312874 * h / 3628800) * |J|)
    (hA_bd : |A| ≤ M / 3628800 * (8 * h) ^ 10)
    (hB_bd : |B| ≤ M / 3628800 * (7 * h) ^ 10)
    (hC_bd : |C| ≤ M / 362880 * (8 * h) ^ 9)
    (hD_bd : |D| ≤ M / 362880 * (7 * h) ^ 9)
    (hE_bd : |E| ≤ M / 362880 * (6 * h) ^ 9)
    (hF_bd : |F| ≤ M / 362880 * (5 * h) ^ 9)
    (hG_bd : |G| ≤ M / 362880 * (4 * h) ^ 9)
    (hH_bd : |H| ≤ M / 362880 * (3 * h) ^ 9)
    (hI_bd : |I| ≤ M / 362880 * (2 * h) ^ 9)
    (hJ_bd : |J| ≤ M / 362880 * h ^ 9) :
    |A - B - (1070017 * h / 3628800) * C - (4467094 * h / 3628800) * D
        + (4604594 * h / 3628800) * E - (5595358 * h / 3628800) * F
        + (5033120 * h / 3628800) * G - (3146338 * h / 3628800) * H
        + (1291214 * h / 3628800) * I - (312874 * h / 3628800) * J|
      ≤ (665 : ℝ) * M * h ^ 10 := by
  have h1070017h_nn : 0 ≤ 1070017 * h / 3628800 := by linarith
  have h4467094h_nn : 0 ≤ 4467094 * h / 3628800 := by linarith
  have h4604594h_nn : 0 ≤ 4604594 * h / 3628800 := by linarith
  have h5595358h_nn : 0 ≤ 5595358 * h / 3628800 := by linarith
  have h5033120h_nn : 0 ≤ 5033120 * h / 3628800 := by linarith
  have h3146338h_nn : 0 ≤ 3146338 * h / 3628800 := by linarith
  have h1291214h_nn : 0 ≤ 1291214 * h / 3628800 := by linarith
  have h312874h_nn : 0 ≤ 312874 * h / 3628800 := by linarith
  have h1070017C_bd : (1070017 * h / 3628800) * |C|
      ≤ (1070017 * h / 3628800) * (M / 362880 * (8 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hC_bd h1070017h_nn
  have h4467094D_bd : (4467094 * h / 3628800) * |D|
      ≤ (4467094 * h / 3628800) * (M / 362880 * (7 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hD_bd h4467094h_nn
  have h4604594E_bd : (4604594 * h / 3628800) * |E|
      ≤ (4604594 * h / 3628800) * (M / 362880 * (6 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hE_bd h4604594h_nn
  have h5595358F_bd : (5595358 * h / 3628800) * |F|
      ≤ (5595358 * h / 3628800) * (M / 362880 * (5 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hF_bd h5595358h_nn
  have h5033120G_bd : (5033120 * h / 3628800) * |G|
      ≤ (5033120 * h / 3628800) * (M / 362880 * (4 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hG_bd h5033120h_nn
  have h3146338H_bd : (3146338 * h / 3628800) * |H|
      ≤ (3146338 * h / 3628800) * (M / 362880 * (3 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hH_bd h3146338h_nn
  have h1291214I_bd : (1291214 * h / 3628800) * |I|
      ≤ (1291214 * h / 3628800) * (M / 362880 * (2 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hI_bd h1291214h_nn
  have h312874J_bd : (312874 * h / 3628800) * |J|
      ≤ (312874 * h / 3628800) * (M / 362880 * h ^ 9) :=
    mul_le_mul_of_nonneg_left hJ_bd h312874h_nn
  have hbound_alg :
      M / 3628800 * (8 * h) ^ 10 + M / 3628800 * (7 * h) ^ 10
        + (1070017 * h / 3628800) * (M / 362880 * (8 * h) ^ 9)
        + (4467094 * h / 3628800) * (M / 362880 * (7 * h) ^ 9)
        + (4604594 * h / 3628800) * (M / 362880 * (6 * h) ^ 9)
        + (5595358 * h / 3628800) * (M / 362880 * (5 * h) ^ 9)
        + (5033120 * h / 3628800) * (M / 362880 * (4 * h) ^ 9)
        + (3146338 * h / 3628800) * (M / 362880 * (3 * h) ^ 9)
        + (1291214 * h / 3628800) * (M / 362880 * (2 * h) ^ 9)
        + (312874 * h / 3628800) * (M / 362880 * h ^ 9)
        = (4555920744497 / 6858432000 : ℝ) * M * h ^ 10 :=
    am8_residual_bound_alg_identity M h
  have hh10_nn : 0 ≤ h ^ 10 := by positivity
  have hMh10_nn : 0 ≤ M * h ^ 10 := mul_nonneg hMnn hh10_nn
  have hslack :
      (4555920744497 / 6858432000 : ℝ) * M * h ^ 10 ≤ 665 * M * h ^ 10 := by
    have hle : (4555920744497 / 6858432000 : ℝ) ≤ 665 := by norm_num
    have hbase :
        (4555920744497 / 6858432000 : ℝ) * (M * h ^ 10) ≤ 665 * (M * h ^ 10) :=
      mul_le_mul_of_nonneg_right hle hMh10_nn
    have hL : (4555920744497 / 6858432000 : ℝ) * M * h ^ 10
        = (4555920744497 / 6858432000 : ℝ) * (M * h ^ 10) := by ring
    have hR : (665 : ℝ) * M * h ^ 10 = 665 * (M * h ^ 10) := by ring
    rw [hL, hR]
    exact hbase
  linarith [htri, hA_bd, hB_bd, h1070017C_bd, h4467094D_bd, h4604594E_bd,
    h5595358F_bd, h5033120G_bd, h3146338H_bd, h1291214I_bd, h312874J_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

/-- Pointwise AM8 truncation residual bound.  The residual expands as
`R_y(8) - R_y(7) - (1070017h/3628800)·R_y'(8) - (4467094h/3628800)·R_y'(7)
  + (4604594h/3628800)·R_y'(6) - (5595358h/3628800)·R_y'(5)
  + (5033120h/3628800)·R_y'(4) - (3146338h/3628800)·R_y'(3)
  + (1291214h/3628800)·R_y'(2) - (312874h/3628800)·R_y'(1)`.  The exact
triangle coefficient is `4555920744497/6858432000 ≈ 664.28`, slackened to
`665`. -/
theorem am8_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 10 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 10 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (ht8h : t + 8 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 8 * h) - y (t + 7 * h)
        - h * ((1070017 / 3628800) * deriv y (t + 8 * h)
              + (4467094 / 3628800) * deriv y (t + 7 * h)
              - (4604594 / 3628800) * deriv y (t + 6 * h)
              + (5595358 / 3628800) * deriv y (t + 5 * h)
              - (5033120 / 3628800) * deriv y (t + 4 * h)
              + (3146338 / 3628800) * deriv y (t + 3 * h)
              - (1291214 / 3628800) * deriv y (t + 2 * h)
              + (312874 / 3628800) * deriv y (t + h)
              - (33953 / 3628800) * deriv y t)|
      ≤ (665 : ℝ) * M * h ^ 10 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have hRy7 :=
    y_tenth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRy8 :=
    y_tenth_order_taylor_remainder hy hbnd ht ht8h h8h
  have hRyp1 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht8h h8h
  set y0 := y t with hy0_def
  set y7 := y (t + 7 * h) with hy7_def
  set y8 := y (t + 8 * h) with hy8_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set d6 := deriv y (t + 6 * h) with hd6_def
  set d7 := deriv y (t + 7 * h) with hd7_def
  set d8 := deriv y (t + 8 * h) with hd8_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd := iteratedDeriv 8 y t with hdddddddd_def
  set ddddddddd := iteratedDeriv 9 y t with hddddddddd_def
  have hLTE_eq :
      y8 - y7 - h * ((1070017 / 3628800) * d8 + (4467094 / 3628800) * d7
                    - (4604594 / 3628800) * d6 + (5595358 / 3628800) * d5
                    - (5033120 / 3628800) * d4 + (3146338 / 3628800) * d3
                    - (1291214 / 3628800) * d2 + (312874 / 3628800) * d1
                    - (33953 / 3628800) * d0)
        = (y8 - y0 - (8 * h) * d0
              - (8 * h) ^ 2 / 2 * dd
              - (8 * h) ^ 3 / 6 * ddd
              - (8 * h) ^ 4 / 24 * dddd
              - (8 * h) ^ 5 / 120 * ddddd
              - (8 * h) ^ 6 / 720 * dddddd
              - (8 * h) ^ 7 / 5040 * ddddddd
              - (8 * h) ^ 8 / 40320 * dddddddd
              - (8 * h) ^ 9 / 362880 * ddddddddd)
          - (y7 - y0 - (7 * h) * d0
              - (7 * h) ^ 2 / 2 * dd
              - (7 * h) ^ 3 / 6 * ddd
              - (7 * h) ^ 4 / 24 * dddd
              - (7 * h) ^ 5 / 120 * ddddd
              - (7 * h) ^ 6 / 720 * dddddd
              - (7 * h) ^ 7 / 5040 * ddddddd
              - (7 * h) ^ 8 / 40320 * dddddddd
              - (7 * h) ^ 9 / 362880 * ddddddddd)
          - (1070017 * h / 3628800)
              * (d8 - d0 - (8 * h) * dd
                  - (8 * h) ^ 2 / 2 * ddd
                  - (8 * h) ^ 3 / 6 * dddd
                  - (8 * h) ^ 4 / 24 * ddddd
                  - (8 * h) ^ 5 / 120 * dddddd
                  - (8 * h) ^ 6 / 720 * ddddddd
                  - (8 * h) ^ 7 / 5040 * dddddddd
                  - (8 * h) ^ 8 / 40320 * ddddddddd)
          - (4467094 * h / 3628800)
              * (d7 - d0 - (7 * h) * dd
                  - (7 * h) ^ 2 / 2 * ddd
                  - (7 * h) ^ 3 / 6 * dddd
                  - (7 * h) ^ 4 / 24 * ddddd
                  - (7 * h) ^ 5 / 120 * dddddd
                  - (7 * h) ^ 6 / 720 * ddddddd
                  - (7 * h) ^ 7 / 5040 * dddddddd
                  - (7 * h) ^ 8 / 40320 * ddddddddd)
          + (4604594 * h / 3628800)
              * (d6 - d0 - (6 * h) * dd
                  - (6 * h) ^ 2 / 2 * ddd
                  - (6 * h) ^ 3 / 6 * dddd
                  - (6 * h) ^ 4 / 24 * ddddd
                  - (6 * h) ^ 5 / 120 * dddddd
                  - (6 * h) ^ 6 / 720 * ddddddd
                  - (6 * h) ^ 7 / 5040 * dddddddd
                  - (6 * h) ^ 8 / 40320 * ddddddddd)
          - (5595358 * h / 3628800)
              * (d5 - d0 - (5 * h) * dd
                  - (5 * h) ^ 2 / 2 * ddd
                  - (5 * h) ^ 3 / 6 * dddd
                  - (5 * h) ^ 4 / 24 * ddddd
                  - (5 * h) ^ 5 / 120 * dddddd
                  - (5 * h) ^ 6 / 720 * ddddddd
                  - (5 * h) ^ 7 / 5040 * dddddddd
                  - (5 * h) ^ 8 / 40320 * ddddddddd)
          + (5033120 * h / 3628800)
              * (d4 - d0 - (4 * h) * dd
                  - (4 * h) ^ 2 / 2 * ddd
                  - (4 * h) ^ 3 / 6 * dddd
                  - (4 * h) ^ 4 / 24 * ddddd
                  - (4 * h) ^ 5 / 120 * dddddd
                  - (4 * h) ^ 6 / 720 * ddddddd
                  - (4 * h) ^ 7 / 5040 * dddddddd
                  - (4 * h) ^ 8 / 40320 * ddddddddd)
          - (3146338 * h / 3628800)
              * (d3 - d0 - (3 * h) * dd
                  - (3 * h) ^ 2 / 2 * ddd
                  - (3 * h) ^ 3 / 6 * dddd
                  - (3 * h) ^ 4 / 24 * ddddd
                  - (3 * h) ^ 5 / 120 * dddddd
                  - (3 * h) ^ 6 / 720 * ddddddd
                  - (3 * h) ^ 7 / 5040 * dddddddd
                  - (3 * h) ^ 8 / 40320 * ddddddddd)
          + (1291214 * h / 3628800)
              * (d2 - d0 - (2 * h) * dd
                  - (2 * h) ^ 2 / 2 * ddd
                  - (2 * h) ^ 3 / 6 * dddd
                  - (2 * h) ^ 4 / 24 * ddddd
                  - (2 * h) ^ 5 / 120 * dddddd
                  - (2 * h) ^ 6 / 720 * ddddddd
                  - (2 * h) ^ 7 / 5040 * dddddddd
                  - (2 * h) ^ 8 / 40320 * ddddddddd)
          - (312874 * h / 3628800)
              * (d1 - d0 - h * dd
                  - h ^ 2 / 2 * ddd
                  - h ^ 3 / 6 * dddd
                  - h ^ 4 / 24 * ddddd
                  - h ^ 5 / 120 * dddddd
                  - h ^ 6 / 720 * ddddddd
                  - h ^ 7 / 5040 * dddddddd
                  - h ^ 8 / 40320 * ddddddddd) :=
    am8_residual_alg_identity y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7 d8 dd ddd dddd
      ddddd dddddd ddddddd dddddddd ddddddddd h
  rw [hLTE_eq]
  set A := y8 - y0 - (8 * h) * d0
            - (8 * h) ^ 2 / 2 * dd
            - (8 * h) ^ 3 / 6 * ddd
            - (8 * h) ^ 4 / 24 * dddd
            - (8 * h) ^ 5 / 120 * ddddd
            - (8 * h) ^ 6 / 720 * dddddd
            - (8 * h) ^ 7 / 5040 * ddddddd
            - (8 * h) ^ 8 / 40320 * dddddddd
            - (8 * h) ^ 9 / 362880 * ddddddddd with hA_def
  set B := y7 - y0 - (7 * h) * d0
            - (7 * h) ^ 2 / 2 * dd
            - (7 * h) ^ 3 / 6 * ddd
            - (7 * h) ^ 4 / 24 * dddd
            - (7 * h) ^ 5 / 120 * ddddd
            - (7 * h) ^ 6 / 720 * dddddd
            - (7 * h) ^ 7 / 5040 * ddddddd
            - (7 * h) ^ 8 / 40320 * dddddddd
            - (7 * h) ^ 9 / 362880 * ddddddddd with hB_def
  set C := d8 - d0 - (8 * h) * dd
            - (8 * h) ^ 2 / 2 * ddd
            - (8 * h) ^ 3 / 6 * dddd
            - (8 * h) ^ 4 / 24 * ddddd
            - (8 * h) ^ 5 / 120 * dddddd
            - (8 * h) ^ 6 / 720 * ddddddd
            - (8 * h) ^ 7 / 5040 * dddddddd
            - (8 * h) ^ 8 / 40320 * ddddddddd with hC_def
  set D := d7 - d0 - (7 * h) * dd
            - (7 * h) ^ 2 / 2 * ddd
            - (7 * h) ^ 3 / 6 * dddd
            - (7 * h) ^ 4 / 24 * ddddd
            - (7 * h) ^ 5 / 120 * dddddd
            - (7 * h) ^ 6 / 720 * ddddddd
            - (7 * h) ^ 7 / 5040 * dddddddd
            - (7 * h) ^ 8 / 40320 * ddddddddd with hD_def
  set E := d6 - d0 - (6 * h) * dd
            - (6 * h) ^ 2 / 2 * ddd
            - (6 * h) ^ 3 / 6 * dddd
            - (6 * h) ^ 4 / 24 * ddddd
            - (6 * h) ^ 5 / 120 * dddddd
            - (6 * h) ^ 6 / 720 * ddddddd
            - (6 * h) ^ 7 / 5040 * dddddddd
            - (6 * h) ^ 8 / 40320 * ddddddddd with hE_def
  set F := d5 - d0 - (5 * h) * dd
            - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd
            - (5 * h) ^ 5 / 120 * dddddd
            - (5 * h) ^ 6 / 720 * ddddddd
            - (5 * h) ^ 7 / 5040 * dddddddd
            - (5 * h) ^ 8 / 40320 * ddddddddd with hF_def
  set G := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd
            - (4 * h) ^ 5 / 120 * dddddd
            - (4 * h) ^ 6 / 720 * ddddddd
            - (4 * h) ^ 7 / 5040 * dddddddd
            - (4 * h) ^ 8 / 40320 * ddddddddd with hG_def
  set H := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd
            - (3 * h) ^ 5 / 120 * dddddd
            - (3 * h) ^ 6 / 720 * ddddddd
            - (3 * h) ^ 7 / 5040 * dddddddd
            - (3 * h) ^ 8 / 40320 * ddddddddd with hH_def
  set I := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd
            - (2 * h) ^ 5 / 120 * dddddd
            - (2 * h) ^ 6 / 720 * ddddddd
            - (2 * h) ^ 7 / 5040 * dddddddd
            - (2 * h) ^ 8 / 40320 * ddddddddd with hI_def
  set J := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd
            - h ^ 5 / 120 * dddddd
            - h ^ 6 / 720 * ddddddd
            - h ^ 7 / 5040 * dddddddd
            - h ^ 8 / 40320 * ddddddddd with hJ_def
  have htri := am8_residual_ten_term_triangle A B C D E F G H I J h hh
  have hA_bd : |A| ≤ M / 3628800 * (8 * h) ^ 10 := hRy8
  have hB_bd : |B| ≤ M / 3628800 * (7 * h) ^ 10 := hRy7
  have hC_bd : |C| ≤ M / 362880 * (8 * h) ^ 9 := hRyp8
  have hD_bd : |D| ≤ M / 362880 * (7 * h) ^ 9 := hRyp7
  have hE_bd : |E| ≤ M / 362880 * (6 * h) ^ 9 := hRyp6
  have hF_bd : |F| ≤ M / 362880 * (5 * h) ^ 9 := hRyp5
  have hG_bd : |G| ≤ M / 362880 * (4 * h) ^ 9 := hRyp4
  have hH_bd : |H| ≤ M / 362880 * (3 * h) ^ 9 := hRyp3
  have hI_bd : |I| ≤ M / 362880 * (2 * h) ^ 9 := hRyp2
  have hJ_bd : |J| ≤ M / 362880 * h ^ 9 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact am8_residual_combine hh hMnn A B C D E F G H I J htri
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hH_bd hI_bd hJ_bd

/-- Uniform bound on the AM8 one-step truncation residual on a finite
horizon, given a `C^10` exact solution. -/
theorem am8_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 10 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 8) * h ≤ T →
        |adamsMoulton8.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 10 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_ten_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(665 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 8) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h = ((n : ℝ) + 8) * h := by ring
    linarith
  rw [am8_localTruncationError_eq]
  show |y (t + 8 * h) - y (t + 7 * h)
      - h * ((1070017 / 3628800) * deriv y (t + 8 * h)
            + (4467094 / 3628800) * deriv y (t + 7 * h)
            - (4604594 / 3628800) * deriv y (t + 6 * h)
            + (5595358 / 3628800) * deriv y (t + 5 * h)
            - (5033120 / 3628800) * deriv y (t + 4 * h)
            + (3146338 / 3628800) * deriv y (t + 3 * h)
            - (1291214 / 3628800) * deriv y (t + 2 * h)
            + (312874 / 3628800) * deriv y (t + h)
            - (33953 / 3628800) * deriv y t)|
    ≤ 665 * M * h ^ 10
  exact am8_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem hh.le

/-- Headline AM8 global error bound.  Given a supplied AM8 trajectory and
starting errors bounded by `ε₀`, the scalar global error is `O(ε₀ + h^9)`
on a finite horizon. -/
theorem am8_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 10 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (1070017 / 3628800 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsAM8Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      |yseq 2 - y (t₀ + 2 * h)| ≤ ε₀ →
      |yseq 3 - y (t₀ + 3 * h)| ≤ ε₀ →
      |yseq 4 - y (t₀ + 4 * h)| ≤ ε₀ →
      |yseq 5 - y (t₀ + 5 * h)| ≤ ε₀ →
      |yseq 6 - y (t₀ + 6 * h)| ≤ ε₀ →
      |yseq 7 - y (t₀ + 7 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 7) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((15 * L) * T) * ε₀ + K * h ^ 9 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am8_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((15 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd he7_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => |yseq k - y (t₀ + (k : ℝ) * h)| with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (max (max (max
        (eN k) (eN (k + 1))) (eN (k + 2)))
        (eN (k + 3))) (eN (k + 4))) (eN (k + 5))) (eN (k + 6))) (eN (k + 7))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
        (le_max_of_le_left (heN_nn k)))))))
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (max (max (max
        (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4)) (eN 5)) (eN 6)) (eN 7)
        ≤ ε₀
    refine max_le (max_le (max_le (max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
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
    · show |yseq 6 - y (t₀ + ((6 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((6 : ℕ) : ℝ) * h = 6 * h := by push_cast; ring
      rw [hcast]; simpa using he6_bd
    · show |yseq 7 - y (t₀ + ((7 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((7 : ℕ) : ℝ) * h = 7 * h := by push_cast; ring
      rw [hcast]; simpa using he7_bd
  have h15L_nn : (0 : ℝ) ≤ 15 * L := by linarith
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 8) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (15 * L)) * EN n + (2 * C) * h ^ 10 := by
    intro n hnh_le
    have honestep := am8_one_step_error_pair_bound
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
    have hcast7 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 7 := by
      push_cast; ring
    have hcast8 : ((n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 8 := by
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
    have heq_eN_n7 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)| := by
      show |_ - _| = _
      rw [hcast7]
    have heq_eN_n8 : eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        = |yseq (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)| := by
      show |_ - _| = _
      rw [hcast8]
    show max (max (max (max (max (max (max
            (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * (15 * L))
            * max (max (max (max (max (max (max (eN n) (eN (n + 1)))
                  (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1)))
                  (eN (n + 1 + 1 + 1 + 1 + 1 + 1 + 1))
          + (2 * C) * h ^ 10
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5,
      heq_eN_n6, heq_eN_n7, heq_eN_n8]
    have h2τ : 2 * |adamsMoulton8.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (2 * C) * h ^ 10 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith [this]
    linarith [honestep, h2τ]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((15 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((15 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh9_nn : 0 ≤ h ^ 9 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((15 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((15 * L) * T) * ε₀
            + T * Real.exp ((15 * L) * T) * (2 * C) * h ^ 9 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((15 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((15 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh9_nn : 0 ≤ T * Real.exp ((15 * L) * T) * (2 * C) * h ^ 9 :=
      mul_nonneg hKnn hh9_nn
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
  | 6, _ =>
    have hbase : |yseq 6 - y (t₀ + ((6 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((6 : ℕ) : ℝ) * h = 6 * h := by push_cast; ring
      rw [hcast]; simpa using he6_bd
    exact hbase_to_headline _ hbase
  | 7, _ =>
    have hbase : |yseq 7 - y (t₀ + ((7 : ℕ) : ℝ) * h)| ≤ ε₀ := by
      have hcast : ((7 : ℕ) : ℝ) * h = 7 * h := by push_cast; ring
      rw [hcast]; simpa using he7_bd
    exact hbase_to_headline _ hbase
  | N' + 8, hNh =>
    have hcast : (((N' + 8 : ℕ) : ℝ) + 7) = (N' : ℝ) + 15 := by
      push_cast; ring
    have hN_hyp : ((N' : ℝ) + 15) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (15 * L)) * EN n + (2 * C) * h ^ (9 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (9 + 1) = (2 * C) * h ^ 10 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 8 ≤ (N' : ℝ) + 15 := by linarith
      have h_mul : ((n : ℝ) + 8) * h ≤ ((N' : ℝ) + 15) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have hle : (N' : ℝ) + 1 ≤ (N' : ℝ) + 15 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 15 * L) (C := 2 * C) (T := T) (p := 9)
        (e := EN) (N := N' + 1)
        hh.le h15L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 8) ≤ EN (N' + 1) := by
      show eN (N' + 8)
        ≤ max (max (max (max (max (max (max
              (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4)))
              (eN (N' + 1 + 5))) (eN (N' + 1 + 6))) (eN (N' + 1 + 7))
      have heq : N' + 8 = N' + 1 + 7 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((15 * L) * T) * EN 0 ≤ Real.exp ((15 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show |yseq (N' + 8) - y (t₀ + ((N' + 8 : ℕ) : ℝ) * h)|
        ≤ Real.exp ((15 * L) * T) * ε₀
          + T * Real.exp ((15 * L) * T) * (2 * C) * h ^ 9
    have heN_eq :
        eN (N' + 8)
          = |yseq (N' + 8) - y (t₀ + ((N' + 8 : ℕ) : ℝ) * h)| := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
