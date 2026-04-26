import OpenMath.LMMTruncationOp
import OpenMath.LMMAB6ScalarConvergence
import OpenMath.AdamsMethods

/-! ## Adams--Moulton 7-step Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit Adams--Moulton
7-step method.  The chain follows the AM6 template (cycle 442) one stencil
step up: the implicit update is parameterised by a supplied trajectory
satisfying the AM7 recurrence, the local residual is bounded by ninth-order
Taylor remainders, and the global error is assembled with
`lmm_error_bound_from_local_truncation`.

The one-step Lipschitz inequality keeps the new implicit sample on the
left with factor `1 - (36799/120960)·h·L`.  The explicit-history weights
add up to `527551/120960 ≈ 4.36`, and we slacken the max-window growth
to `10L` (the smallest integer satisfying `G ≥ 2(β + S)`).  The exact
pointwise residual coefficient is `84361887977/348364800 ≈ 242.17`,
slackened to `243`. -/

namespace LMM

/-- A `C^9` function has its ninth derivative bounded on every compact
interval `[a, b]`. -/
private theorem iteratedDeriv_nine_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 9 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 9 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 9 y) :=
    hy.continuous_iteratedDeriv 9 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise ninth-order Taylor (Lagrange) remainder bound: if `y` is
`C^9` and `|iteratedDeriv 9 y| ≤ M` on `[a, b]`, then for `t, t + r ∈
[a, b]` with `r ≥ 0`,
`|y(t+r) - y(t) - r·y'(t) - r²/2·y''(t) - r³/6·y'''(t) - r⁴/24·y⁽⁴⁾(t)
  - r⁵/120·y⁽⁵⁾(t) - r⁶/720·y⁽⁶⁾(t) - r⁷/5040·y⁽⁷⁾(t)
  - r⁸/40320·y⁽⁸⁾(t)|
  ≤ M/362880 · r⁹`. -/
private theorem y_ninth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 9 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 9 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t
        - r ^ 4 / 24 * iteratedDeriv 4 y t
        - r ^ 5 / 120 * iteratedDeriv 5 y t
        - r ^ 6 / 720 * iteratedDeriv 6 y t
        - r ^ 7 / 5040 * iteratedDeriv 7 y t
        - r ^ 8 / 40320 * iteratedDeriv 8 y t|
      ≤ M / 362880 * r ^ 9 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 8 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 9 y ξ * r ^ 9 / 362880 := by
    have hcdo : ContDiffOn ℝ 9 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 8) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 9 = r ^ 9 := by ring
    have hfact : (((8 + 1 : ℕ).factorial : ℝ)) = 362880 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval y 8 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t + r ^ 2 / 2 * iteratedDeriv 2 y t
              + r ^ 3 / 6 * iteratedDeriv 3 y t
              + r ^ 4 / 24 * iteratedDeriv 4 y t
              + r ^ 5 / 120 * iteratedDeriv 5 y t
              + r ^ 6 / 720 * iteratedDeriv 6 y t
              + r ^ 7 / 5040 * iteratedDeriv 7 y t
              + r ^ 8 / 40320 * iteratedDeriv 8 y t := by
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
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero,
        h0, h1, h2, h3, h4, h5, h6, h7, h8]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 9 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      y (t + r) - y t - r * deriv y t
          - r ^ 2 / 2 * iteratedDeriv 2 y t
          - r ^ 3 / 6 * iteratedDeriv 3 y t
          - r ^ 4 / 24 * iteratedDeriv 4 y t
          - r ^ 5 / 120 * iteratedDeriv 5 y t
          - r ^ 6 / 720 * iteratedDeriv 6 y t
          - r ^ 7 / 5040 * iteratedDeriv 7 y t
          - r ^ 8 / 40320 * iteratedDeriv 8 y t
        = iteratedDeriv 9 y ξ * r ^ 9 / 362880 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 9 y ξ * r ^ 9 / 362880
      = (iteratedDeriv 9 y ξ) * (r ^ 9 / 362880) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 9 / 362880)]
  calc |iteratedDeriv 9 y ξ| * (r ^ 9 / 362880)
      ≤ M * (r ^ 9 / 362880) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 362880 * r ^ 9 := by ring

/-- Pointwise eighth-order Taylor (Lagrange) remainder bound for the
derivative: if `y` is `C^9` and `|iteratedDeriv 9 y| ≤ M` on `[a, b]`,
then for `t, t + r ∈ [a, b]` with `r ≥ 0`,
`|y'(t+r) - y'(t) - r·y''(t) - r²/2·y'''(t) - r³/6·y⁽⁴⁾(t)
  - r⁴/24·y⁽⁵⁾(t) - r⁵/120·y⁽⁶⁾(t) - r⁶/720·y⁽⁷⁾(t)
  - r⁷/5040·y⁽⁸⁾(t)|
  ≤ M/40320 · r⁸`. -/
private theorem derivY_eighth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 9 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 9 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t
        - r ^ 3 / 6 * iteratedDeriv 4 y t
        - r ^ 4 / 24 * iteratedDeriv 5 y t
        - r ^ 5 / 120 * iteratedDeriv 6 y t
        - r ^ 6 / 720 * iteratedDeriv 7 y t
        - r ^ 7 / 5040 * iteratedDeriv 8 y t|
      ≤ M / 40320 * r ^ 8 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  have hdy : ContDiff ℝ 8 (deriv y) := hy.deriv'
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r)
          - taylorWithinEval (deriv y) 7 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 8 (deriv y) ξ * r ^ 8 / 40320 := by
    have hcdo : ContDiffOn ℝ 8 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 7) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 8 = r ^ 8 := by ring
    have hfact : (((7 + 1 : ℕ).factorial : ℝ)) = 40320 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval (deriv y) 7 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t
              + r ^ 2 / 2 * iteratedDeriv 3 y t
              + r ^ 3 / 6 * iteratedDeriv 4 y t
              + r ^ 4 / 24 * iteratedDeriv 5 y t
              + r ^ 5 / 120 * iteratedDeriv 6 y t
              + r ^ 6 / 720 * iteratedDeriv 7 y t
              + r ^ 7 / 5040 * iteratedDeriv 8 y t := by
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
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hidd_eq : iteratedDeriv 8 (deriv y) = iteratedDeriv 9 y := by
    have : iteratedDeriv 9 y = iteratedDeriv 8 (deriv y) :=
      iteratedDeriv_succ' (n := 8) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 9 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
          - r ^ 2 / 2 * iteratedDeriv 3 y t
          - r ^ 3 / 6 * iteratedDeriv 4 y t
          - r ^ 4 / 24 * iteratedDeriv 5 y t
          - r ^ 5 / 120 * iteratedDeriv 6 y t
          - r ^ 6 / 720 * iteratedDeriv 7 y t
          - r ^ 7 / 5040 * iteratedDeriv 8 y t
        = iteratedDeriv 9 y ξ * r ^ 8 / 40320 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 9 y ξ * r ^ 8 / 40320
      = (iteratedDeriv 9 y ξ) * (r ^ 8 / 40320) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 8 / 40320)]
  calc |iteratedDeriv 9 y ξ| * (r ^ 8 / 40320)
      ≤ M * (r ^ 8 / 40320) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 40320 * r ^ 8 := by ring

/-- AM7 trajectory predicate:
`y_{n+7} = y_{n+6} + h(36799/120960 f_{n+7} + 139849/120960 f_{n+6}
  - 121797/120960 f_{n+5} + 123133/120960 f_{n+4}
  - 88547/120960 f_{n+3} + 41499/120960 f_{n+2}
  - 11351/120960 f_{n+1} + 1375/120960 f_n)`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM7Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 7)
      = y (n + 6)
        + h * ((36799 / 120960 : ℝ) * f (t₀ + ((n : ℝ) + 7) * h) (y (n + 7))
             + (139849 / 120960 : ℝ) * f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6))
             - (121797 / 120960 : ℝ) * f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))
             + (123133 / 120960 : ℝ) * f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))
             - (88547 / 120960 : ℝ) * f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             + (41499 / 120960 : ℝ) * f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             - (11351 / 120960 : ℝ) * f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             + (1375 / 120960 : ℝ) * f (t₀ + (n : ℝ) * h) (y n))

/-- AM7 local truncation operator reduces to the textbook residual. -/
theorem am7_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsMoulton7.localTruncationError h t y
      = y (t + 7 * h) - y (t + 6 * h)
          - h * ((36799 / 120960 : ℝ) * deriv y (t + 7 * h)
                + (139849 / 120960 : ℝ) * deriv y (t + 6 * h)
                - (121797 / 120960 : ℝ) * deriv y (t + 5 * h)
                + (123133 / 120960 : ℝ) * deriv y (t + 4 * h)
                - (88547 / 120960 : ℝ) * deriv y (t + 3 * h)
                + (41499 / 120960 : ℝ) * deriv y (t + 2 * h)
                - (11351 / 120960 : ℝ) * deriv y (t + h)
                + (1375 / 120960 : ℝ) * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsMoulton7, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AM7 Lipschitz inequality before dividing by the implicit
new-point factor.  The side condition records the small-step regime used
by the divided form. -/
theorem am7_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (36799 / 120960 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM7Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (36799 / 120960 : ℝ) * h * L)
        * |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
      ≤ |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
        + (139849 / 120960 : ℝ) * h * L
            * |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
        + (121797 / 120960 : ℝ) * h * L
            * |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
        + (123133 / 120960 : ℝ) * h * L
            * |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
        + (88547 / 120960 : ℝ) * h * L
            * |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
        + (41499 / 120960 : ℝ) * h * L
            * |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
        + (11351 / 120960 : ℝ) * h * L
            * |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
        + (1375 / 120960 : ℝ) * h * L
            * |yseq n - y (t₀ + (n : ℝ) * h)|
        + |adamsMoulton7.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set yn3 : ℝ := yseq (n + 3) with hyn3_def
  set yn4 : ℝ := yseq (n + 4) with hyn4_def
  set yn5 : ℝ := yseq (n + 5) with hyn5_def
  set yn6 : ℝ := yseq (n + 6) with hyn6_def
  set yn7 : ℝ := yseq (n + 7) with hyn7_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set zn6 : ℝ := y tn6 with hzn6_def
  set zn7 : ℝ := y tn7 with hzn7_def
  set τ : ℝ := adamsMoulton7.localTruncationError h tn y with hτ_def
  have _hsmall_record : (36799 / 120960 : ℝ) * h * L ≤ 1 / 2 := hsmall
  have hstep : yn7
      = yn6
        + h * ((36799 / 120960 : ℝ) * f tn7 yn7
             + (139849 / 120960 : ℝ) * f tn6 yn6
             - (121797 / 120960 : ℝ) * f tn5 yn5
             + (123133 / 120960 : ℝ) * f tn4 yn4
             - (88547 / 120960 : ℝ) * f tn3 yn3
             + (41499 / 120960 : ℝ) * f tn2 yn2
             - (11351 / 120960 : ℝ) * f tn1 yn1
             + (1375 / 120960 : ℝ) * f tn yn) := by
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
      - h * ((36799 / 120960 : ℝ) * f tn7 zn7
             + (139849 / 120960 : ℝ) * f tn6 zn6
             - (121797 / 120960 : ℝ) * f tn5 zn5
             + (123133 / 120960 : ℝ) * f tn4 zn4
             - (88547 / 120960 : ℝ) * f tn3 zn3
             + (41499 / 120960 : ℝ) * f tn2 zn2
             - (11351 / 120960 : ℝ) * f tn1 zn1
             + (1375 / 120960 : ℝ) * f tn zn) := by
    show adamsMoulton7.localTruncationError h tn y = _
    rw [am7_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h,
      htn_5h, htn_6h, htn_7h, hyf tn7, hyf tn6, hyf tn5, hyf tn4, hyf tn3,
      hyf tn2, hyf tn1, hyf tn]
  have halg : yn7 - zn7
      = (yn6 - zn6)
        + (36799 / 120960 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)
        + (139849 / 120960 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)
        - (121797 / 120960 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
        + (123133 / 120960 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        - (88547 / 120960 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        + (41499 / 120960 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        - (11351 / 120960 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        + (1375 / 120960 : ℝ) * h * (f tn yn - f tn zn)
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
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
  have h36799_nn : 0 ≤ (36799 / 120960 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h139849_nn : 0 ≤ (139849 / 120960 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h121797_nn : 0 ≤ (121797 / 120960 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h123133_nn : 0 ≤ (123133 / 120960 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h88547_nn : 0 ≤ (88547 / 120960 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h41499_nn : 0 ≤ (41499 / 120960 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h11351_nn : 0 ≤ (11351 / 120960 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h1375_nn : 0 ≤ (1375 / 120960 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h36799_abs :
      |(36799 / 120960 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)|
      ≤ (36799 / 120960 : ℝ) * h * L * |yn7 - zn7| := by
    rw [abs_mul, abs_of_nonneg h36799_nn]
    calc (36799 / 120960 : ℝ) * h * |f tn7 yn7 - f tn7 zn7|
        ≤ (36799 / 120960 : ℝ) * h * (L * |yn7 - zn7|) :=
          mul_le_mul_of_nonneg_left hLip7 h36799_nn
      _ = (36799 / 120960 : ℝ) * h * L * |yn7 - zn7| := by ring
  have h139849_abs :
      |(139849 / 120960 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)|
      ≤ (139849 / 120960 : ℝ) * h * L * |yn6 - zn6| := by
    rw [abs_mul, abs_of_nonneg h139849_nn]
    calc (139849 / 120960 : ℝ) * h * |f tn6 yn6 - f tn6 zn6|
        ≤ (139849 / 120960 : ℝ) * h * (L * |yn6 - zn6|) :=
          mul_le_mul_of_nonneg_left hLip6 h139849_nn
      _ = (139849 / 120960 : ℝ) * h * L * |yn6 - zn6| := by ring
  have h121797_abs :
      |(121797 / 120960 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
      ≤ (121797 / 120960 : ℝ) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg h121797_nn]
    calc (121797 / 120960 : ℝ) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (121797 / 120960 : ℝ) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip5 h121797_nn
      _ = (121797 / 120960 : ℝ) * h * L * |yn5 - zn5| := by ring
  have h123133_abs :
      |(123133 / 120960 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (123133 / 120960 : ℝ) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h123133_nn]
    calc (123133 / 120960 : ℝ) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (123133 / 120960 : ℝ) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 h123133_nn
      _ = (123133 / 120960 : ℝ) * h * L * |yn4 - zn4| := by ring
  have h88547_abs :
      |(88547 / 120960 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (88547 / 120960 : ℝ) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h88547_nn]
    calc (88547 / 120960 : ℝ) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (88547 / 120960 : ℝ) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h88547_nn
      _ = (88547 / 120960 : ℝ) * h * L * |yn3 - zn3| := by ring
  have h41499_abs :
      |(41499 / 120960 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (41499 / 120960 : ℝ) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h41499_nn]
    calc (41499 / 120960 : ℝ) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (41499 / 120960 : ℝ) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h41499_nn
      _ = (41499 / 120960 : ℝ) * h * L * |yn2 - zn2| := by ring
  have h11351_abs :
      |(11351 / 120960 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (11351 / 120960 : ℝ) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h11351_nn]
    calc (11351 / 120960 : ℝ) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (11351 / 120960 : ℝ) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h11351_nn
      _ = (11351 / 120960 : ℝ) * h * L * |yn1 - zn1| := by ring
  have h1375_abs :
      |(1375 / 120960 : ℝ) * h * (f tn yn - f tn zn)|
      ≤ (1375 / 120960 : ℝ) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h1375_nn]
    calc (1375 / 120960 : ℝ) * h * |f tn yn - f tn zn|
        ≤ (1375 / 120960 : ℝ) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h1375_nn
      _ = (1375 / 120960 : ℝ) * h * L * |yn - zn| := by ring
  -- Triangle inequality for ten terms (9 algebraic + τ).
  have htri_terms (A B C D E F G H I J : ℝ) :
      |A + B + C - D + E - F + G - H + I - J|
        ≤ |A| + |B| + |C| + |D| + |E| + |F| + |G| + |H| + |I| + |J| := by
    have h1 : |A + B + C - D + E - F + G - H + I - J|
        ≤ |A + B + C - D + E - F + G - H + I| + |J| := abs_sub _ _
    have h2 : |A + B + C - D + E - F + G - H + I|
        ≤ |A + B + C - D + E - F + G - H| + |I| := abs_add_le _ _
    have h3 : |A + B + C - D + E - F + G - H|
        ≤ |A + B + C - D + E - F + G| + |H| := abs_sub _ _
    have h4 : |A + B + C - D + E - F + G|
        ≤ |A + B + C - D + E - F| + |G| := abs_add_le _ _
    have h5 : |A + B + C - D + E - F|
        ≤ |A + B + C - D + E| + |F| := abs_sub _ _
    have h6 : |A + B + C - D + E|
        ≤ |A + B + C - D| + |E| := abs_add_le _ _
    have h7 : |A + B + C - D| ≤ |A + B + C| + |D| := abs_sub _ _
    have h8 : |A + B + C| ≤ |A + B| + |C| := abs_add_le _ _
    have h9 : |A + B| ≤ |A| + |B| := abs_add_le _ _
    linarith
  have htri :
      |(yn6 - zn6)
        + (36799 / 120960 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)
        + (139849 / 120960 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)
        - (121797 / 120960 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
        + (123133 / 120960 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
        - (88547 / 120960 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
        + (41499 / 120960 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
        - (11351 / 120960 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
        + (1375 / 120960 : ℝ) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn6 - zn6|
          + |(36799 / 120960 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)|
          + |(139849 / 120960 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(121797 / 120960 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(123133 / 120960 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(88547 / 120960 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(41499 / 120960 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(11351 / 120960 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(1375 / 120960 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| :=
    htri_terms (yn6 - zn6)
      ((36799 / 120960 : ℝ) * h * (f tn7 yn7 - f tn7 zn7))
      ((139849 / 120960 : ℝ) * h * (f tn6 yn6 - f tn6 zn6))
      ((121797 / 120960 : ℝ) * h * (f tn5 yn5 - f tn5 zn5))
      ((123133 / 120960 : ℝ) * h * (f tn4 yn4 - f tn4 zn4))
      ((88547 / 120960 : ℝ) * h * (f tn3 yn3 - f tn3 zn3))
      ((41499 / 120960 : ℝ) * h * (f tn2 yn2 - f tn2 zn2))
      ((11351 / 120960 : ℝ) * h * (f tn1 yn1 - f tn1 zn1))
      ((1375 / 120960 : ℝ) * h * (f tn yn - f tn zn)) τ
  have hmain :
      |yn7 - zn7|
        ≤ |yn6 - zn6|
          + (36799 / 120960 : ℝ) * h * L * |yn7 - zn7|
          + (139849 / 120960 : ℝ) * h * L * |yn6 - zn6|
          + (121797 / 120960 : ℝ) * h * L * |yn5 - zn5|
          + (123133 / 120960 : ℝ) * h * L * |yn4 - zn4|
          + (88547 / 120960 : ℝ) * h * L * |yn3 - zn3|
          + (41499 / 120960 : ℝ) * h * L * |yn2 - zn2|
          + (11351 / 120960 : ℝ) * h * L * |yn1 - zn1|
          + (1375 / 120960 : ℝ) * h * L * |yn - zn|
          + |τ| := by
    calc |yn7 - zn7|
        = |(yn6 - zn6)
            + (36799 / 120960 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)
            + (139849 / 120960 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)
            - (121797 / 120960 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)
            + (123133 / 120960 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)
            - (88547 / 120960 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)
            + (41499 / 120960 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)
            - (11351 / 120960 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)
            + (1375 / 120960 : ℝ) * h * (f tn yn - f tn zn)
            - τ| := by rw [halg]
      _ ≤ |yn6 - zn6|
          + |(36799 / 120960 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)|
          + |(139849 / 120960 : ℝ) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(121797 / 120960 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(123133 / 120960 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(88547 / 120960 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(41499 / 120960 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(11351 / 120960 : ℝ) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(1375 / 120960 : ℝ) * h * (f tn yn - f tn zn)|
          + |τ| := htri
      _ ≤ |yn6 - zn6|
          + (36799 / 120960 : ℝ) * h * L * |yn7 - zn7|
          + (139849 / 120960 : ℝ) * h * L * |yn6 - zn6|
          + (121797 / 120960 : ℝ) * h * L * |yn5 - zn5|
          + (123133 / 120960 : ℝ) * h * L * |yn4 - zn4|
          + (88547 / 120960 : ℝ) * h * L * |yn3 - zn3|
          + (41499 / 120960 : ℝ) * h * L * |yn2 - zn2|
          + (11351 / 120960 : ℝ) * h * L * |yn1 - zn1|
          + (1375 / 120960 : ℝ) * h * L * |yn - zn|
          + |τ| := by
        linarith [h36799_abs, h139849_abs, h121797_abs, h123133_abs,
          h88547_abs, h41499_abs, h11351_abs, h1375_abs]
  linarith [hmain]

/-- Divided one-step AM7 error bound.  The explicit AM7 weights contribute
`527551/120960`; after dividing by the implicit `(1 - (36799/120960)hL)`
factor, we slacken the max-window growth to `10L` and the residual
coefficient to `2`. -/
theorem am7_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (36799 / 120960 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM7Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
      ≤ (1 + h * (10 * L))
            * max (max (max (max (max (max
                |yseq n - y (t₀ + (n : ℝ) * h)|
                |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|)
                |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
                |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
                |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
                |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
                |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
        + 2 * |adamsMoulton7.localTruncationError h
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
  set τabs : ℝ :=
    |adamsMoulton7.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ :=
    max (max (max (max (max (max en en1) en2) en3) en4) en5) en6 with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hen7_nn : 0 ≤ en7 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen_le_E : en ≤ E :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen3_le_E : en3 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen4_le_E : en4 ≤ E :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen5_le_E : en5 ≤ E := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen6_le_E : en6 ≤ E := le_max_right _ _
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
      (am7_one_step_lipschitz (h := h) (L := L) hh hsmall hf t₀ hy y hyf n)
  have h139849_nn : 0 ≤ (139849 / 120960 : ℝ) * h * L := by positivity
  have h121797_nn : 0 ≤ (121797 / 120960 : ℝ) * h * L := by positivity
  have h123133_nn : 0 ≤ (123133 / 120960 : ℝ) * h * L := by positivity
  have h88547_nn : 0 ≤ (88547 / 120960 : ℝ) * h * L := by positivity
  have h41499_nn : 0 ≤ (41499 / 120960 : ℝ) * h * L := by positivity
  have h11351_nn : 0 ≤ (11351 / 120960 : ℝ) * h * L := by positivity
  have h1375_nn : 0 ≤ (1375 / 120960 : ℝ) * h * L := by positivity
  have h139849_le :
      (139849 / 120960 : ℝ) * h * L * en6
        ≤ (139849 / 120960 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen6_le_E h139849_nn
  have h121797_le :
      (121797 / 120960 : ℝ) * h * L * en5
        ≤ (121797 / 120960 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen5_le_E h121797_nn
  have h123133_le :
      (123133 / 120960 : ℝ) * h * L * en4
        ≤ (123133 / 120960 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen4_le_E h123133_nn
  have h88547_le :
      (88547 / 120960 : ℝ) * h * L * en3
        ≤ (88547 / 120960 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen3_le_E h88547_nn
  have h41499_le :
      (41499 / 120960 : ℝ) * h * L * en2
        ≤ (41499 / 120960 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen2_le_E h41499_nn
  have h11351_le :
      (11351 / 120960 : ℝ) * h * L * en1
        ≤ (11351 / 120960 : ℝ) * h * L * E :=
    mul_le_mul_of_nonneg_left hen1_le_E h11351_nn
  have h1375_le :
      (1375 / 120960 : ℝ) * h * L * en
        ≤ (1375 / 120960 : ℝ) * h * L * E :=
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
        ≤ (1 + (527551 / 120960 : ℝ) * (h * L)) * E + τabs := by
    have h_alg :
        E + (139849 / 120960 : ℝ) * h * L * E
            + (121797 / 120960 : ℝ) * h * L * E
            + (123133 / 120960 : ℝ) * h * L * E
            + (88547 / 120960 : ℝ) * h * L * E
            + (41499 / 120960 : ℝ) * h * L * E
            + (11351 / 120960 : ℝ) * h * L * E
            + (1375 / 120960 : ℝ) * h * L * E + τabs
          = (1 + (527551 / 120960 : ℝ) * (h * L)) * E + τabs := by
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
      (1 + (527551 / 120960 : ℝ) * (h * L)) * E
        ≤ ((1 - (36799 / 120960 : ℝ) * h * L) * (1 + h * (10 * L))) * E :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (36799 / 120960 : ℝ) * h * L) * 2) * τabs :=
    by simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (527551 / 120960 : ℝ) * (h * L)) * E + τabs
        ≤ (1 - (36799 / 120960 : ℝ) * h * L)
            * ((1 + h * (10 * L)) * E + 2 * τabs) := by
    have hsplit :
        (1 - (36799 / 120960 : ℝ) * h * L)
            * ((1 + h * (10 * L)) * E + 2 * τabs)
          = ((1 - (36799 / 120960 : ℝ) * h * L) * (1 + h * (10 * L))) * E
              + ((1 - (36799 / 120960 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (36799 / 120960 : ℝ) * h * L) * en7
        ≤ (1 - (36799 / 120960 : ℝ) * h * L)
            * ((1 + h * (10 * L)) * E + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  have hcancel :
      en7 ≤ (1 + h * (10 * L)) * E + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  exact hcancel

/-- Max-norm AM7 one-step recurrence on the rolling 7-window
`(en, en1, en2, en3, en4, en5, en6)`. -/
theorem am7_one_step_error_pair_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (36799 / 120960 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM7Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max
          |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
          |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
          |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
          |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|)
          |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
      ≤ (1 + h * (10 * L))
            * max (max (max (max (max (max
                |yseq n - y (t₀ + (n : ℝ) * h)|
                |yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|)
                |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
                |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
                |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
                |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
                |yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
        + 2 * |adamsMoulton7.localTruncationError h
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
  set τabs : ℝ :=
    |adamsMoulton7.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set E : ℝ :=
    max (max (max (max (max (max en en1) en2) en3) en4) en5) en6 with hE_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hen7_nn : 0 ≤ en7 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hE_nn : 0 ≤ E :=
    le_trans hen_nn (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _))))))
  have hen1_le_E : en1 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _)
            (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have hen2_le_E : en2 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hen3_le_E : en3 ≤ E :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hen4_le_E : en4 ≤ E :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen5_le_E : en5 ≤ E := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen6_le_E : en6 ≤ E := le_max_right _ _
  have h10hL_nn : 0 ≤ h * (10 * L) := by positivity
  have hen7_bd :
      en7 ≤ (1 + h * (10 * L)) * E + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hen4_def, hen5_def, hen6_def,
      hen7_def, hτabs_def, hE_def]
      using
      (am7_one_step_error_bound (h := h) (L := L) hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : E ≤ (1 + h * (10 * L)) * E := by
    have hone : (1 : ℝ) * E ≤ (1 + h * (10 * L)) * E :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (10 * L)) * E + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (10 * L)) * E + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  have hen3_bd : en3 ≤ (1 + h * (10 * L)) * E + 2 * τabs := by
    linarith [hen3_le_E, hE_le_grow]
  have hen4_bd : en4 ≤ (1 + h * (10 * L)) * E + 2 * τabs := by
    linarith [hen4_le_E, hE_le_grow]
  have hen5_bd : en5 ≤ (1 + h * (10 * L)) * E + 2 * τabs := by
    linarith [hen5_le_E, hE_le_grow]
  have hen6_bd : en6 ≤ (1 + h * (10 * L)) * E + 2 * τabs := by
    linarith [hen6_le_E, hE_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd)
    hen4_bd) hen5_bd) hen6_bd) hen7_bd

/-- Pure algebraic identity: the AM7 residual rewrites as a signed sum of
nine Taylor remainders. Extracted as a stand-alone lemma so the kernel
checks the (large degree-9) `ring` proof term in isolation. -/
private lemma am7_residual_alg_identity
    (y0 y6 y7 d0 d1 d2 d3 d4 d5 d6 d7 dd ddd dddd ddddd dddddd ddddddd
        dddddddd h : ℝ) :
    y7 - y6 - h * ((36799 / 120960) * d7 + (139849 / 120960) * d6
                  - (121797 / 120960) * d5 + (123133 / 120960) * d4
                  - (88547 / 120960) * d3 + (41499 / 120960) * d2
                  - (11351 / 120960) * d1 + (1375 / 120960) * d0)
      = (y7 - y0 - (7 * h) * d0
            - (7 * h) ^ 2 / 2 * dd
            - (7 * h) ^ 3 / 6 * ddd
            - (7 * h) ^ 4 / 24 * dddd
            - (7 * h) ^ 5 / 120 * ddddd
            - (7 * h) ^ 6 / 720 * dddddd
            - (7 * h) ^ 7 / 5040 * ddddddd
            - (7 * h) ^ 8 / 40320 * dddddddd)
        - (y6 - y0 - (6 * h) * d0
            - (6 * h) ^ 2 / 2 * dd
            - (6 * h) ^ 3 / 6 * ddd
            - (6 * h) ^ 4 / 24 * dddd
            - (6 * h) ^ 5 / 120 * ddddd
            - (6 * h) ^ 6 / 720 * dddddd
            - (6 * h) ^ 7 / 5040 * ddddddd
            - (6 * h) ^ 8 / 40320 * dddddddd)
        - (36799 * h / 120960)
            * (d7 - d0 - (7 * h) * dd
                - (7 * h) ^ 2 / 2 * ddd
                - (7 * h) ^ 3 / 6 * dddd
                - (7 * h) ^ 4 / 24 * ddddd
                - (7 * h) ^ 5 / 120 * dddddd
                - (7 * h) ^ 6 / 720 * ddddddd
                - (7 * h) ^ 7 / 5040 * dddddddd)
        - (139849 * h / 120960)
            * (d6 - d0 - (6 * h) * dd
                - (6 * h) ^ 2 / 2 * ddd
                - (6 * h) ^ 3 / 6 * dddd
                - (6 * h) ^ 4 / 24 * ddddd
                - (6 * h) ^ 5 / 120 * dddddd
                - (6 * h) ^ 6 / 720 * ddddddd
                - (6 * h) ^ 7 / 5040 * dddddddd)
        + (121797 * h / 120960)
            * (d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd
                - (5 * h) ^ 6 / 720 * ddddddd
                - (5 * h) ^ 7 / 5040 * dddddddd)
        - (123133 * h / 120960)
            * (d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd
                - (4 * h) ^ 6 / 720 * ddddddd
                - (4 * h) ^ 7 / 5040 * dddddddd)
        + (88547 * h / 120960)
            * (d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd
                - (3 * h) ^ 6 / 720 * ddddddd
                - (3 * h) ^ 7 / 5040 * dddddddd)
        - (41499 * h / 120960)
            * (d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd
                - (2 * h) ^ 6 / 720 * ddddddd
                - (2 * h) ^ 7 / 5040 * dddddddd)
        + (11351 * h / 120960)
            * (d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd
                - h ^ 6 / 720 * ddddddd
                - h ^ 7 / 5040 * dddddddd) := by
  ring

/-- Pure algebraic identity: the sum of the nine scaled Lagrange
remainder bounds equals `(84361887977/348364800) · M · h^9`. -/
private lemma am7_residual_bound_alg_identity (M h : ℝ) :
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

/-- Triangle inequality for the nine-term AM7 residual chunk. -/
private lemma am7_residual_nine_term_triangle
    (A B C D E F G H I h : ℝ) (hh : 0 ≤ h) :
    |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
        + (121797 * h / 120960) * E - (123133 * h / 120960) * F
        + (88547 * h / 120960) * G - (41499 * h / 120960) * H
        + (11351 * h / 120960) * I|
      ≤ |A| + |B| + (36799 * h / 120960) * |C| + (139849 * h / 120960) * |D|
          + (121797 * h / 120960) * |E| + (123133 * h / 120960) * |F|
          + (88547 * h / 120960) * |G| + (41499 * h / 120960) * |H|
          + (11351 * h / 120960) * |I| := by
  have h36799h_nn : 0 ≤ 36799 * h / 120960 := by linarith
  have h139849h_nn : 0 ≤ 139849 * h / 120960 := by linarith
  have h121797h_nn : 0 ≤ 121797 * h / 120960 := by linarith
  have h123133h_nn : 0 ≤ 123133 * h / 120960 := by linarith
  have h88547h_nn : 0 ≤ 88547 * h / 120960 := by linarith
  have h41499h_nn : 0 ≤ 41499 * h / 120960 := by linarith
  have h11351h_nn : 0 ≤ 11351 * h / 120960 := by linarith
  have habs36799 : |(36799 * h / 120960) * C| = (36799 * h / 120960) * |C| := by
    rw [abs_mul, abs_of_nonneg h36799h_nn]
  have habs139849 :
      |(139849 * h / 120960) * D| = (139849 * h / 120960) * |D| := by
    rw [abs_mul, abs_of_nonneg h139849h_nn]
  have habs121797 :
      |(121797 * h / 120960) * E| = (121797 * h / 120960) * |E| := by
    rw [abs_mul, abs_of_nonneg h121797h_nn]
  have habs123133 :
      |(123133 * h / 120960) * F| = (123133 * h / 120960) * |F| := by
    rw [abs_mul, abs_of_nonneg h123133h_nn]
  have habs88547 :
      |(88547 * h / 120960) * G| = (88547 * h / 120960) * |G| := by
    rw [abs_mul, abs_of_nonneg h88547h_nn]
  have habs41499 :
      |(41499 * h / 120960) * H| = (41499 * h / 120960) * |H| := by
    rw [abs_mul, abs_of_nonneg h41499h_nn]
  have habs11351 :
      |(11351 * h / 120960) * I| = (11351 * h / 120960) * |I| := by
    rw [abs_mul, abs_of_nonneg h11351h_nn]
  have h1 : |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
                + (121797 * h / 120960) * E - (123133 * h / 120960) * F
                + (88547 * h / 120960) * G - (41499 * h / 120960) * H
                + (11351 * h / 120960) * I|
      ≤ |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
            + (121797 * h / 120960) * E - (123133 * h / 120960) * F
            + (88547 * h / 120960) * G - (41499 * h / 120960) * H|
        + |(11351 * h / 120960) * I| := abs_add_le _ _
  have h2 : |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
                + (121797 * h / 120960) * E - (123133 * h / 120960) * F
                + (88547 * h / 120960) * G - (41499 * h / 120960) * H|
      ≤ |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
            + (121797 * h / 120960) * E - (123133 * h / 120960) * F
            + (88547 * h / 120960) * G|
        + |(41499 * h / 120960) * H| := abs_sub _ _
  have h3 : |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
                + (121797 * h / 120960) * E - (123133 * h / 120960) * F
                + (88547 * h / 120960) * G|
      ≤ |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
            + (121797 * h / 120960) * E - (123133 * h / 120960) * F|
        + |(88547 * h / 120960) * G| := abs_add_le _ _
  have h4 : |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
                + (121797 * h / 120960) * E - (123133 * h / 120960) * F|
      ≤ |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
            + (121797 * h / 120960) * E|
        + |(123133 * h / 120960) * F| := abs_sub _ _
  have h5 : |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
                + (121797 * h / 120960) * E|
      ≤ |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D|
        + |(121797 * h / 120960) * E| := abs_add_le _ _
  have h6 : |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D|
      ≤ |A - B - (36799 * h / 120960) * C| + |(139849 * h / 120960) * D| :=
    abs_sub _ _
  have h7 : |A - B - (36799 * h / 120960) * C|
      ≤ |A - B| + |(36799 * h / 120960) * C| := abs_sub _ _
  have h8 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith [habs36799.le, habs36799.ge, habs139849.le, habs139849.ge,
    habs121797.le, habs121797.ge, habs123133.le, habs123133.ge,
    habs88547.le, habs88547.ge, habs41499.le, habs41499.ge,
    habs11351.le, habs11351.ge]

/-- Combine the nine-term triangle inequality with the absolute bounds
on each piece to obtain the `243 · M · h^9` final bound.  Extracted as a
helper so the kernel verifies the `linarith` proof term in isolation, not
inside the heavy `am7_pointwise_residual_bound` context. -/
private lemma am7_residual_combine
    {M h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D E F G H I : ℝ)
    (htri : |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
              + (121797 * h / 120960) * E - (123133 * h / 120960) * F
              + (88547 * h / 120960) * G - (41499 * h / 120960) * H
              + (11351 * h / 120960) * I|
            ≤ |A| + |B| + (36799 * h / 120960) * |C|
              + (139849 * h / 120960) * |D| + (121797 * h / 120960) * |E|
              + (123133 * h / 120960) * |F| + (88547 * h / 120960) * |G|
              + (41499 * h / 120960) * |H| + (11351 * h / 120960) * |I|)
    (hA_bd : |A| ≤ M / 362880 * (7 * h) ^ 9)
    (hB_bd : |B| ≤ M / 362880 * (6 * h) ^ 9)
    (hC_bd : |C| ≤ M / 40320 * (7 * h) ^ 8)
    (hD_bd : |D| ≤ M / 40320 * (6 * h) ^ 8)
    (hE_bd : |E| ≤ M / 40320 * (5 * h) ^ 8)
    (hF_bd : |F| ≤ M / 40320 * (4 * h) ^ 8)
    (hG_bd : |G| ≤ M / 40320 * (3 * h) ^ 8)
    (hH_bd : |H| ≤ M / 40320 * (2 * h) ^ 8)
    (hI_bd : |I| ≤ M / 40320 * h ^ 8) :
    |A - B - (36799 * h / 120960) * C - (139849 * h / 120960) * D
        + (121797 * h / 120960) * E - (123133 * h / 120960) * F
        + (88547 * h / 120960) * G - (41499 * h / 120960) * H
        + (11351 * h / 120960) * I|
      ≤ (243 : ℝ) * M * h ^ 9 := by
  have h36799h_nn : 0 ≤ 36799 * h / 120960 := by linarith
  have h139849h_nn : 0 ≤ 139849 * h / 120960 := by linarith
  have h121797h_nn : 0 ≤ 121797 * h / 120960 := by linarith
  have h123133h_nn : 0 ≤ 123133 * h / 120960 := by linarith
  have h88547h_nn : 0 ≤ 88547 * h / 120960 := by linarith
  have h41499h_nn : 0 ≤ 41499 * h / 120960 := by linarith
  have h11351h_nn : 0 ≤ 11351 * h / 120960 := by linarith
  have h36799C_bd : (36799 * h / 120960) * |C|
      ≤ (36799 * h / 120960) * (M / 40320 * (7 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hC_bd h36799h_nn
  have h139849D_bd : (139849 * h / 120960) * |D|
      ≤ (139849 * h / 120960) * (M / 40320 * (6 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hD_bd h139849h_nn
  have h121797E_bd : (121797 * h / 120960) * |E|
      ≤ (121797 * h / 120960) * (M / 40320 * (5 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hE_bd h121797h_nn
  have h123133F_bd : (123133 * h / 120960) * |F|
      ≤ (123133 * h / 120960) * (M / 40320 * (4 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hF_bd h123133h_nn
  have h88547G_bd : (88547 * h / 120960) * |G|
      ≤ (88547 * h / 120960) * (M / 40320 * (3 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hG_bd h88547h_nn
  have h41499H_bd : (41499 * h / 120960) * |H|
      ≤ (41499 * h / 120960) * (M / 40320 * (2 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hH_bd h41499h_nn
  have h11351I_bd : (11351 * h / 120960) * |I|
      ≤ (11351 * h / 120960) * (M / 40320 * h ^ 8) :=
    mul_le_mul_of_nonneg_left hI_bd h11351h_nn
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
    am7_residual_bound_alg_identity M h
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
  linarith [htri, hA_bd, hB_bd, h36799C_bd, h139849D_bd, h121797E_bd,
    h123133F_bd, h88547G_bd, h41499H_bd, h11351I_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

/-- Pointwise AM7 truncation residual bound.  The residual expands as
`R_y(7) - R_y(6) - (36799h/120960)·R_y'(7) - (139849h/120960)·R_y'(6)
  + (121797h/120960)·R_y'(5) - (123133h/120960)·R_y'(4)
  + (88547h/120960)·R_y'(3) - (41499h/120960)·R_y'(2)
  + (11351h/120960)·R_y'(1)`.  The exact triangle coefficient is
`84361887977/348364800 ≈ 242.17`, slackened to `243`. -/
theorem am7_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 9 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 9 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 7 * h) - y (t + 6 * h)
        - h * ((36799 / 120960) * deriv y (t + 7 * h)
              + (139849 / 120960) * deriv y (t + 6 * h)
              - (121797 / 120960) * deriv y (t + 5 * h)
              + (123133 / 120960) * deriv y (t + 4 * h)
              - (88547 / 120960) * deriv y (t + 3 * h)
              + (41499 / 120960) * deriv y (t + 2 * h)
              - (11351 / 120960) * deriv y (t + h)
              + (1375 / 120960) * deriv y t)|
      ≤ (243 : ℝ) * M * h ^ 9 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have hRy6 :=
    y_ninth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRy7 :=
    y_ninth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRyp1 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht7h h7h
  set y0 := y t with hy0_def
  set y6 := y (t + 6 * h) with hy6_def
  set y7 := y (t + 7 * h) with hy7_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set d6 := deriv y (t + 6 * h) with hd6_def
  set d7 := deriv y (t + 7 * h) with hd7_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd := iteratedDeriv 8 y t with hdddddddd_def
  have hLTE_eq :
      y7 - y6 - h * ((36799 / 120960) * d7 + (139849 / 120960) * d6
                    - (121797 / 120960) * d5 + (123133 / 120960) * d4
                    - (88547 / 120960) * d3 + (41499 / 120960) * d2
                    - (11351 / 120960) * d1 + (1375 / 120960) * d0)
        = (y7 - y0 - (7 * h) * d0
              - (7 * h) ^ 2 / 2 * dd
              - (7 * h) ^ 3 / 6 * ddd
              - (7 * h) ^ 4 / 24 * dddd
              - (7 * h) ^ 5 / 120 * ddddd
              - (7 * h) ^ 6 / 720 * dddddd
              - (7 * h) ^ 7 / 5040 * ddddddd
              - (7 * h) ^ 8 / 40320 * dddddddd)
          - (y6 - y0 - (6 * h) * d0
              - (6 * h) ^ 2 / 2 * dd
              - (6 * h) ^ 3 / 6 * ddd
              - (6 * h) ^ 4 / 24 * dddd
              - (6 * h) ^ 5 / 120 * ddddd
              - (6 * h) ^ 6 / 720 * dddddd
              - (6 * h) ^ 7 / 5040 * ddddddd
              - (6 * h) ^ 8 / 40320 * dddddddd)
          - (36799 * h / 120960)
              * (d7 - d0 - (7 * h) * dd
                  - (7 * h) ^ 2 / 2 * ddd
                  - (7 * h) ^ 3 / 6 * dddd
                  - (7 * h) ^ 4 / 24 * ddddd
                  - (7 * h) ^ 5 / 120 * dddddd
                  - (7 * h) ^ 6 / 720 * ddddddd
                  - (7 * h) ^ 7 / 5040 * dddddddd)
          - (139849 * h / 120960)
              * (d6 - d0 - (6 * h) * dd
                  - (6 * h) ^ 2 / 2 * ddd
                  - (6 * h) ^ 3 / 6 * dddd
                  - (6 * h) ^ 4 / 24 * ddddd
                  - (6 * h) ^ 5 / 120 * dddddd
                  - (6 * h) ^ 6 / 720 * ddddddd
                  - (6 * h) ^ 7 / 5040 * dddddddd)
          + (121797 * h / 120960)
              * (d5 - d0 - (5 * h) * dd
                  - (5 * h) ^ 2 / 2 * ddd
                  - (5 * h) ^ 3 / 6 * dddd
                  - (5 * h) ^ 4 / 24 * ddddd
                  - (5 * h) ^ 5 / 120 * dddddd
                  - (5 * h) ^ 6 / 720 * ddddddd
                  - (5 * h) ^ 7 / 5040 * dddddddd)
          - (123133 * h / 120960)
              * (d4 - d0 - (4 * h) * dd
                  - (4 * h) ^ 2 / 2 * ddd
                  - (4 * h) ^ 3 / 6 * dddd
                  - (4 * h) ^ 4 / 24 * ddddd
                  - (4 * h) ^ 5 / 120 * dddddd
                  - (4 * h) ^ 6 / 720 * ddddddd
                  - (4 * h) ^ 7 / 5040 * dddddddd)
          + (88547 * h / 120960)
              * (d3 - d0 - (3 * h) * dd
                  - (3 * h) ^ 2 / 2 * ddd
                  - (3 * h) ^ 3 / 6 * dddd
                  - (3 * h) ^ 4 / 24 * ddddd
                  - (3 * h) ^ 5 / 120 * dddddd
                  - (3 * h) ^ 6 / 720 * ddddddd
                  - (3 * h) ^ 7 / 5040 * dddddddd)
          - (41499 * h / 120960)
              * (d2 - d0 - (2 * h) * dd
                  - (2 * h) ^ 2 / 2 * ddd
                  - (2 * h) ^ 3 / 6 * dddd
                  - (2 * h) ^ 4 / 24 * ddddd
                  - (2 * h) ^ 5 / 120 * dddddd
                  - (2 * h) ^ 6 / 720 * ddddddd
                  - (2 * h) ^ 7 / 5040 * dddddddd)
          + (11351 * h / 120960)
              * (d1 - d0 - h * dd
                  - h ^ 2 / 2 * ddd
                  - h ^ 3 / 6 * dddd
                  - h ^ 4 / 24 * ddddd
                  - h ^ 5 / 120 * dddddd
                  - h ^ 6 / 720 * ddddddd
                  - h ^ 7 / 5040 * dddddddd) :=
    am7_residual_alg_identity y0 y6 y7 d0 d1 d2 d3 d4 d5 d6 d7 dd ddd dddd ddddd
      dddddd ddddddd dddddddd h
  rw [hLTE_eq]
  set A := y7 - y0 - (7 * h) * d0
            - (7 * h) ^ 2 / 2 * dd
            - (7 * h) ^ 3 / 6 * ddd
            - (7 * h) ^ 4 / 24 * dddd
            - (7 * h) ^ 5 / 120 * ddddd
            - (7 * h) ^ 6 / 720 * dddddd
            - (7 * h) ^ 7 / 5040 * ddddddd
            - (7 * h) ^ 8 / 40320 * dddddddd with hA_def
  set B := y6 - y0 - (6 * h) * d0
            - (6 * h) ^ 2 / 2 * dd
            - (6 * h) ^ 3 / 6 * ddd
            - (6 * h) ^ 4 / 24 * dddd
            - (6 * h) ^ 5 / 120 * ddddd
            - (6 * h) ^ 6 / 720 * dddddd
            - (6 * h) ^ 7 / 5040 * ddddddd
            - (6 * h) ^ 8 / 40320 * dddddddd with hB_def
  set C := d7 - d0 - (7 * h) * dd
            - (7 * h) ^ 2 / 2 * ddd
            - (7 * h) ^ 3 / 6 * dddd
            - (7 * h) ^ 4 / 24 * ddddd
            - (7 * h) ^ 5 / 120 * dddddd
            - (7 * h) ^ 6 / 720 * ddddddd
            - (7 * h) ^ 7 / 5040 * dddddddd with hC_def
  set D := d6 - d0 - (6 * h) * dd
            - (6 * h) ^ 2 / 2 * ddd
            - (6 * h) ^ 3 / 6 * dddd
            - (6 * h) ^ 4 / 24 * ddddd
            - (6 * h) ^ 5 / 120 * dddddd
            - (6 * h) ^ 6 / 720 * ddddddd
            - (6 * h) ^ 7 / 5040 * dddddddd with hD_def
  set E := d5 - d0 - (5 * h) * dd
            - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd
            - (5 * h) ^ 5 / 120 * dddddd
            - (5 * h) ^ 6 / 720 * ddddddd
            - (5 * h) ^ 7 / 5040 * dddddddd with hE_def
  set F := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd
            - (4 * h) ^ 5 / 120 * dddddd
            - (4 * h) ^ 6 / 720 * ddddddd
            - (4 * h) ^ 7 / 5040 * dddddddd with hF_def
  set G := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd
            - (3 * h) ^ 5 / 120 * dddddd
            - (3 * h) ^ 6 / 720 * ddddddd
            - (3 * h) ^ 7 / 5040 * dddddddd with hG_def
  set H := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd
            - (2 * h) ^ 5 / 120 * dddddd
            - (2 * h) ^ 6 / 720 * ddddddd
            - (2 * h) ^ 7 / 5040 * dddddddd with hH_def
  set I := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd
            - h ^ 5 / 120 * dddddd
            - h ^ 6 / 720 * ddddddd
            - h ^ 7 / 5040 * dddddddd with hI_def
  have htri := am7_residual_nine_term_triangle A B C D E F G H I h hh
  have hA_bd : |A| ≤ M / 362880 * (7 * h) ^ 9 := hRy7
  have hB_bd : |B| ≤ M / 362880 * (6 * h) ^ 9 := hRy6
  have hC_bd : |C| ≤ M / 40320 * (7 * h) ^ 8 := hRyp7
  have hD_bd : |D| ≤ M / 40320 * (6 * h) ^ 8 := hRyp6
  have hE_bd : |E| ≤ M / 40320 * (5 * h) ^ 8 := hRyp5
  have hF_bd : |F| ≤ M / 40320 * (4 * h) ^ 8 := hRyp4
  have hG_bd : |G| ≤ M / 40320 * (3 * h) ^ 8 := hRyp3
  have hH_bd : |H| ≤ M / 40320 * (2 * h) ^ 8 := hRyp2
  have hI_bd : |I| ≤ M / 40320 * h ^ 8 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact am7_residual_combine hh hMnn A B C D E F G H I htri
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hH_bd hI_bd

/-- Uniform bound on the AM7 one-step truncation residual on a finite
horizon, given a `C^9` exact solution. -/
theorem am7_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 9 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 7) * h ≤ T →
        |adamsMoulton7.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 9 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_nine_bounded_on_Icc hy t₀ (t₀ + T + 1)
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
  rw [am7_localTruncationError_eq]
  show |y (t + 7 * h) - y (t + 6 * h)
      - h * ((36799 / 120960) * deriv y (t + 7 * h)
            + (139849 / 120960) * deriv y (t + 6 * h)
            - (121797 / 120960) * deriv y (t + 5 * h)
            + (123133 / 120960) * deriv y (t + 4 * h)
            - (88547 / 120960) * deriv y (t + 3 * h)
            + (41499 / 120960) * deriv y (t + 2 * h)
            - (11351 / 120960) * deriv y (t + h)
            + (1375 / 120960) * deriv y t)|
    ≤ 243 * M * h ^ 9
  exact am7_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem hh.le

/-- Headline AM7 global error bound.  Given a supplied AM7 trajectory and
starting errors bounded by `ε₀`, the scalar global error is `O(ε₀ + h^8)`
on a finite horizon. -/
theorem am7_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 9 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (36799 / 120960 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsAM7Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      |yseq 2 - y (t₀ + 2 * h)| ≤ ε₀ →
      |yseq 3 - y (t₀ + 3 * h)| ≤ ε₀ →
      |yseq 4 - y (t₀ + 4 * h)| ≤ ε₀ →
      |yseq 5 - y (t₀ + 5 * h)| ≤ ε₀ →
      |yseq 6 - y (t₀ + 6 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 6) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((10 * L) * T) * ε₀ + K * h ^ 8 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am7_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((10 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd
    he4_bd he5_bd he6_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => |yseq k - y (t₀ + (k : ℝ) * h)| with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (max (max
        (eN k) (eN (k + 1))) (eN (k + 2)))
        (eN (k + 3))) (eN (k + 4))) (eN (k + 5))) (eN (k + 6))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (heN_nn k))))))
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (max (max
        (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4)) (eN 5)) (eN 6)
        ≤ ε₀
    refine max_le (max_le (max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_) ?_) ?_
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
  have h10L_nn : (0 : ℝ) ≤ 10 * L := by linarith
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 7) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (10 * L)) * EN n + (2 * C) * h ^ 9 := by
    intro n hnh_le
    have honestep := am7_one_step_error_pair_bound
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
    have h2τ : 2 * |adamsMoulton7.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (2 * C) * h ^ 9 := by
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
    show |yseq (N' + 7) - y (t₀ + ((N' + 7 : ℕ) : ℝ) * h)|
        ≤ Real.exp ((10 * L) * T) * ε₀
          + T * Real.exp ((10 * L) * T) * (2 * C) * h ^ 8
    have heN_eq :
        eN (N' + 7)
          = |yseq (N' + 7) - y (t₀ + ((N' + 7 : ℕ) : ℝ) * h)| := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
