import OpenMath.LMMTruncationOp
import OpenMath.LMMAB12Convergence
import OpenMath.AdamsMethods

/-! ## Adams--Moulton 12-step Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit Adams--Moulton
12-step method.  This adds public fourteenth-order scalar Taylor helpers
and the AM12 quantitative ladder.

The AM12 coefficients are obtained by integrating the Lagrange basis on
nodes 0,...,12 over `[11, 12]`; over the common denominator `2615348736000`
the numerators are [-13695779093, 179842822566, -1092096992268, 4063327863170, -10344711794985, 19058185652796, -26204344465152, 27345870698436, -21847538039895, 13465774256510, -6616420957428, 3917551216986, 703604254357],
summing to `2615348736000`.

With the implicit smallness assumption `β₁₂ h L ≤ 1/2`, division by the
implicit new-point factor requires the growth slack `104 L`. The exact
fourteenth-order residual coefficient is approximately
`39097.4964`, slackened to `39098`. -/

namespace LMM

/-! ### Fourteenth-order Taylor helpers (public, reusable for AB13/AM12-vector) -/

/-- A `C^14` function has its fourteenth derivative bounded on every compact
interval `[a, b]`. -/
theorem iteratedDeriv_fourteen_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 14 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 14 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 14 y) :=
    hy.continuous_iteratedDeriv 14 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise fourteenth-order Taylor (Lagrange) remainder bound. -/
theorem y_fourteenth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 14 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 14 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t
        - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t
        - r ^ 4 / 24 * iteratedDeriv 4 y t
        - r ^ 5 / 120 * iteratedDeriv 5 y t
        - r ^ 6 / 720 * iteratedDeriv 6 y t
        - r ^ 7 / 5040 * iteratedDeriv 7 y t
        - r ^ 8 / 40320 * iteratedDeriv 8 y t
        - r ^ 9 / 362880 * iteratedDeriv 9 y t
        - r ^ 10 / 3628800 * iteratedDeriv 10 y t
        - r ^ 11 / 39916800 * iteratedDeriv 11 y t
        - r ^ 12 / 479001600 * iteratedDeriv 12 y t
        - r ^ 13 / 6227020800 * iteratedDeriv 13 y t|
      ≤ M / 87178291200 * r ^ 14 := by
  by_cases hr' : r = 0
  · subst hr'
    simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 13 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 14 y ξ * r ^ 14 / 87178291200 := by
    have hcdo : ContDiffOn ℝ 14 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 13) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 14 = r ^ 14 := by ring
    have hfact : (((13 + 1 : ℕ).factorial : ℝ)) = 87178291200 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval y 13 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t
              + r ^ 2 / 2 * iteratedDeriv 2 y t
              + r ^ 3 / 6 * iteratedDeriv 3 y t
              + r ^ 4 / 24 * iteratedDeriv 4 y t
              + r ^ 5 / 120 * iteratedDeriv 5 y t
              + r ^ 6 / 720 * iteratedDeriv 6 y t
              + r ^ 7 / 5040 * iteratedDeriv 7 y t
              + r ^ 8 / 40320 * iteratedDeriv 8 y t
              + r ^ 9 / 362880 * iteratedDeriv 9 y t
              + r ^ 10 / 3628800 * iteratedDeriv 10 y t
              + r ^ 11 / 39916800 * iteratedDeriv 11 y t
              + r ^ 12 / 479001600 * iteratedDeriv 12 y t
              + r ^ 13 / 6227020800 * iteratedDeriv 13 y t := by
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
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
    have h10 :
        iteratedDerivWithin 10 y (Set.Icc t (t + r)) t = iteratedDeriv 10 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 10) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h11 :
        iteratedDerivWithin 11 y (Set.Icc t (t + r)) t = iteratedDeriv 11 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 11) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h12 :
        iteratedDerivWithin 12 y (Set.Icc t (t + r)) t = iteratedDeriv 12 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 12) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h13 :
        iteratedDerivWithin 13 y (Set.Icc t (t + r)) t = iteratedDeriv 13 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 13) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 14 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      y (t + r) - y t
        - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t
        - r ^ 4 / 24 * iteratedDeriv 4 y t
        - r ^ 5 / 120 * iteratedDeriv 5 y t
        - r ^ 6 / 720 * iteratedDeriv 6 y t
        - r ^ 7 / 5040 * iteratedDeriv 7 y t
        - r ^ 8 / 40320 * iteratedDeriv 8 y t
        - r ^ 9 / 362880 * iteratedDeriv 9 y t
        - r ^ 10 / 3628800 * iteratedDeriv 10 y t
        - r ^ 11 / 39916800 * iteratedDeriv 11 y t
        - r ^ 12 / 479001600 * iteratedDeriv 12 y t
        - r ^ 13 / 6227020800 * iteratedDeriv 13 y t
        = iteratedDeriv 14 y ξ * r ^ 14 / 87178291200 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 14 y ξ * r ^ 14 / 87178291200
      = (iteratedDeriv 14 y ξ) * (r ^ 14 / 87178291200) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 14 / 87178291200)]
  calc |iteratedDeriv 14 y ξ| * (r ^ 14 / 87178291200)
      ≤ M * (r ^ 14 / 87178291200) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 87178291200 * r ^ 14 := by ring

/-- Pointwise thirteenth-order Taylor (Lagrange) remainder bound for the
derivative. -/
theorem derivY_thirteenth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 14 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 14 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t
        - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t
        - r ^ 3 / 6 * iteratedDeriv 4 y t
        - r ^ 4 / 24 * iteratedDeriv 5 y t
        - r ^ 5 / 120 * iteratedDeriv 6 y t
        - r ^ 6 / 720 * iteratedDeriv 7 y t
        - r ^ 7 / 5040 * iteratedDeriv 8 y t
        - r ^ 8 / 40320 * iteratedDeriv 9 y t
        - r ^ 9 / 362880 * iteratedDeriv 10 y t
        - r ^ 10 / 3628800 * iteratedDeriv 11 y t
        - r ^ 11 / 39916800 * iteratedDeriv 12 y t
        - r ^ 12 / 479001600 * iteratedDeriv 13 y t|
      ≤ M / 6227020800 * r ^ 13 := by
  by_cases hr' : r = 0
  · subst hr'
    simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  have hdy : ContDiff ℝ 13 (deriv y) := hy.deriv'
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r)
          - taylorWithinEval (deriv y) 12 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 13 (deriv y) ξ * r ^ 13 / 6227020800 := by
    have hcdo : ContDiffOn ℝ 13 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 12) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 13 = r ^ 13 := by ring
    have hfact : (((12 + 1 : ℕ).factorial : ℝ)) = 6227020800 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval (deriv y) 12 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t
              + r ^ 2 / 2 * iteratedDeriv 3 y t
              + r ^ 3 / 6 * iteratedDeriv 4 y t
              + r ^ 4 / 24 * iteratedDeriv 5 y t
              + r ^ 5 / 120 * iteratedDeriv 6 y t
              + r ^ 6 / 720 * iteratedDeriv 7 y t
              + r ^ 7 / 5040 * iteratedDeriv 8 y t
              + r ^ 8 / 40320 * iteratedDeriv 9 y t
              + r ^ 9 / 362880 * iteratedDeriv 10 y t
              + r ^ 10 / 3628800 * iteratedDeriv 11 y t
              + r ^ 11 / 39916800 * iteratedDeriv 12 y t
              + r ^ 12 / 479001600 * iteratedDeriv 13 y t := by
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
    have h9 :
        iteratedDerivWithin 9 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 10 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 9) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 10 y = iteratedDeriv 9 (deriv y) :=
        iteratedDeriv_succ' (n := 9) (f := y)
      rw [this]
    have h10 :
        iteratedDerivWithin 10 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 11 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 10) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 11 y = iteratedDeriv 10 (deriv y) :=
        iteratedDeriv_succ' (n := 10) (f := y)
      rw [this]
    have h11 :
        iteratedDerivWithin 11 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 12 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 11) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 12 y = iteratedDeriv 11 (deriv y) :=
        iteratedDeriv_succ' (n := 11) (f := y)
      rw [this]
    have h12 :
        iteratedDerivWithin 12 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 13 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 12) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 13 y = iteratedDeriv 12 (deriv y) :=
        iteratedDeriv_succ' (n := 12) (f := y)
      rw [this]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hidd_eq : iteratedDeriv 13 (deriv y) = iteratedDeriv 14 y := by
    have : iteratedDeriv 14 y = iteratedDeriv 13 (deriv y) :=
      iteratedDeriv_succ' (n := 13) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 14 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t
        - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t
        - r ^ 3 / 6 * iteratedDeriv 4 y t
        - r ^ 4 / 24 * iteratedDeriv 5 y t
        - r ^ 5 / 120 * iteratedDeriv 6 y t
        - r ^ 6 / 720 * iteratedDeriv 7 y t
        - r ^ 7 / 5040 * iteratedDeriv 8 y t
        - r ^ 8 / 40320 * iteratedDeriv 9 y t
        - r ^ 9 / 362880 * iteratedDeriv 10 y t
        - r ^ 10 / 3628800 * iteratedDeriv 11 y t
        - r ^ 11 / 39916800 * iteratedDeriv 12 y t
        - r ^ 12 / 479001600 * iteratedDeriv 13 y t
        = iteratedDeriv 14 y ξ * r ^ 13 / 6227020800 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 14 y ξ * r ^ 13 / 6227020800
      = (iteratedDeriv 14 y ξ) * (r ^ 13 / 6227020800) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 13 / 6227020800)]
  calc |iteratedDeriv 14 y ξ| * (r ^ 13 / 6227020800)
      ≤ M * (r ^ 13 / 6227020800) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 6227020800 * r ^ 13 := by ring



/-! ### AM12 coefficients and trajectory predicate -/

/-- AM12 coefficients as a compact reusable finite vector. -/
noncomputable def am12Coeff : Fin 13 → ℝ :=
  ![-13695779093/2615348736000, 179842822566/2615348736000, -1092096992268/2615348736000, 4063327863170/2615348736000, -10344711794985/2615348736000, 19058185652796/2615348736000, -26204344465152/2615348736000, 27345870698436/2615348736000, -21847538039895/2615348736000, 13465774256510/2615348736000, -6616420957428/2615348736000, 3917551216986/2615348736000, 703604254357/2615348736000]

/-- The twelve already-known AM12 coefficients, excluding the implicit new point. -/
noncomputable def am12ExplicitCoeff (j : Fin 12) : ℝ :=
  am12Coeff ⟨j, by omega⟩

/-- Textbook AM12 residual at base point `t`. -/
noncomputable def am12Residual (h t : ℝ) (y : ℝ → ℝ) : ℝ :=
  y (t + 12 * h) - y (t + 11 * h)
    - h * ∑ j : Fin 13, am12Coeff j * deriv y (t + (j : ℕ) * h)

/-- AM12 trajectory predicate. -/
structure IsAM12Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 12)
      = y (n + 11)
        + h * ∑ j : Fin 13,
            am12Coeff j * f (t₀ + (n : ℝ) * h + (j : ℕ) * h)
              (y (n + (j : ℕ)))

/-- Scalar pointwise error at an index. -/
noncomputable def am12Err (h t₀ : ℝ) (yseq : ℕ → ℝ) (y : ℝ → ℝ)
    (k : ℕ) : ℝ :=
  |yseq k - y (t₀ + (k : ℝ) * h)|

/-- Rolling AM12 twelve-sample window max. -/
noncomputable def am12ErrWindow (h t₀ : ℝ) (yseq : ℕ → ℝ) (y : ℝ → ℝ)
    (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin 12 => am12Err h t₀ yseq y (k + (j : ℕ)))

lemma am12ErrWindow_nonneg (h t₀ : ℝ) (yseq : ℕ → ℝ) (y : ℝ → ℝ)
    (k : ℕ) : 0 ≤ am12ErrWindow h t₀ yseq y k := by
  unfold am12ErrWindow
  exact (abs_nonneg _).trans
    (Finset.le_sup' (b := (0 : Fin 12))
      (f := fun j : Fin 12 => am12Err h t₀ yseq y (k + (j : ℕ)))
      (Finset.mem_univ _))

/-- AM12 local truncation operator reduces to the textbook residual. -/
theorem am12_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsMoulton12.localTruncationError h t y = am12Residual h t y := by
  unfold localTruncationError truncationOp am12Residual
  simp [adamsMoulton12, am12Coeff, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  norm_num
  ring

/-- One-step AM12 Lipschitz inequality before dividing by the implicit
new-point factor. -/
theorem am12_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) (_hL : 0 ≤ L)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM12Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
        * am12Err h t₀ yseq y (n + 12)
      ≤ am12Err h t₀ yseq y (n + 11)
        + h * L * ∑ j : Fin 12,
            |am12ExplicitCoeff j| * am12Err h t₀ yseq y (n + (j : ℕ))
        + |adamsMoulton12.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  set τ : ℝ := adamsMoulton12.localTruncationError h t y with hτ_def
  set Sa : ℝ := ∑ j : Fin 13,
      am12Coeff j * f (t + (j : ℕ) * h) (yseq (n + (j : ℕ))) with hSa_def
  set Sy : ℝ := ∑ j : Fin 13,
      am12Coeff j * f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)) with hSy_def
  have hstep : yseq (n + 12) = yseq (n + 11) + h * Sa := by
    simpa [hSa_def, ht_def, add_assoc] using hy.recurrence n
  have hτ_alt : τ = y (t + 12 * h) - y (t + 11 * h) - h * Sy := by
    show adamsMoulton12.localTruncationError h t y = _
    rw [am12_localTruncationError_eq]
    unfold am12Residual
    have hcong :
        (fun j : Fin 13 => am12Coeff j * deriv y (t + (j : ℕ) * h))
          = (fun j : Fin 13 =>
              am12Coeff j * f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))) := by
      funext j
      rw [hyf]
    rw [hcong, hSy_def]
  set Sd : ℝ := ∑ j : Fin 13, am12Coeff j
      * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
        - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))) with hSd_def
  have hSa_sub_Sy : Sa - Sy = Sd := by
    rw [hSa_def, hSy_def, hSd_def, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have halg :
      yseq (n + 12) - y (t + 12 * h)
        = (yseq (n + 11) - y (t + 11 * h)) + h * Sd - τ := by
    rw [hstep, hτ_alt, ← hSa_sub_Sy]
    ring
  have hdiff_bound : ∀ j : Fin 13,
      |am12Coeff j
          * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))|
        ≤ |am12Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by
    intro j
    have hLip := hf (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
      (y (t + (j : ℕ) * h))
    rw [abs_mul]
    have hcoeff_nn : 0 ≤ |am12Coeff j| := abs_nonneg _
    calc
      |am12Coeff j| *
          |f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h))|
          ≤ |am12Coeff j| *
              (L * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)|) :=
            mul_le_mul_of_nonneg_left hLip hcoeff_nn
      _ = |am12Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by ring
  have hSd_abs :
      |Sd| ≤ ∑ j : Fin 13, |am12Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by
    rw [hSd_def]
    calc
      |∑ j : Fin 13, am12Coeff j
          * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
            - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))|
          ≤ ∑ j : Fin 13,
              |am12Coeff j
                * (f (t + (j : ℕ) * h) (yseq (n + (j : ℕ)))
                  - f (t + (j : ℕ) * h) (y (t + (j : ℕ) * h)))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 13, |am12Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| :=
            Finset.sum_le_sum (fun j _ => hdiff_bound j)
  have htri :
      |yseq (n + 12) - y (t + 12 * h)|
        ≤ |yseq (n + 11) - y (t + 11 * h)| + |h * Sd| + |τ| := by
    rw [halg]
    have h1 :
        |(yseq (n + 11) - y (t + 11 * h)) + h * Sd - τ|
          ≤ |(yseq (n + 11) - y (t + 11 * h)) + h * Sd| + |τ| :=
      abs_sub _ _
    have h2 :
        |(yseq (n + 11) - y (t + 11 * h)) + h * Sd|
          ≤ |yseq (n + 11) - y (t + 11 * h)| + |h * Sd| :=
      abs_add_le _ _
    linarith
  have h_hSd :
      |h * Sd| ≤ h * ∑ j : Fin 13, |am12Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)| := by
    rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hSd_abs hh
  have hmain_local :
      |yseq (n + 12) - y (t + 12 * h)|
        ≤ |yseq (n + 11) - y (t + 11 * h)|
          + h * ∑ j : Fin 13, |am12Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)|
          + |τ| := by
    linarith
  have hsplit :
      h * ∑ j : Fin 13, |am12Coeff j| * L
            * |yseq (n + (j : ℕ)) - y (t + (j : ℕ) * h)|
        = h * L * ∑ j : Fin 12,
            |am12ExplicitCoeff j| * am12Err h t₀ yseq y (n + (j : ℕ))
          + (703604254357 / 2615348736000 : ℝ) * h * L
              * am12Err h t₀ yseq y (n + 12) := by
    simp [am12Coeff, am12ExplicitCoeff, am12Err, Fin.sum_univ_succ, ht_def]
    ring_nf
  have hmain :
      am12Err h t₀ yseq y (n + 12)
        ≤ am12Err h t₀ yseq y (n + 11)
          + h * L * ∑ j : Fin 12,
            |am12ExplicitCoeff j| * am12Err h t₀ yseq y (n + (j : ℕ))
          + (703604254357 / 2615348736000 : ℝ) * h * L
              * am12Err h t₀ yseq y (n + 12)
          + |adamsMoulton12.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
    have hmain_local' := hmain_local
    rw [hsplit] at hmain_local'
    simpa [am12Err, ht_def, Nat.cast_add, add_mul, add_assoc, add_left_comm,
      add_comm, hτ_def] using hmain_local'
  linarith [hmain]

/-- Divided AM12 one-step error bound at the new point. -/
theorem am12_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (703604254357 / 2615348736000 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM12Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    am12Err h t₀ yseq y (n + 12)
      ≤ (1 + h * (104 * L)) * am12ErrWindow h t₀ yseq y n
        + 2 * |adamsMoulton12.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set E : ℝ := am12ErrWindow h t₀ yseq y n with hE_def
  set τabs : ℝ :=
    |adamsMoulton12.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hE_nn : 0 ≤ E := by
    simpa [hE_def] using am12ErrWindow_nonneg h t₀ yseq y n
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 1307674368000 / 703604254357 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (703604254357 / 2615348736000 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hwin : ∀ j : Fin 12,
      am12Err h t₀ yseq y (n + (j : ℕ)) ≤ E := by
    intro j
    show am12Err h t₀ yseq y (n + (j : ℕ))
        ≤ am12ErrWindow h t₀ yseq y n
    unfold am12ErrWindow
    exact Finset.le_sup' (b := j)
      (f := fun k : Fin 12 => am12Err h t₀ yseq y (n + (k : ℕ)))
      (Finset.mem_univ _)
  have he_last_le_E : am12Err h t₀ yseq y (n + 11) ≤ E :=
    hwin ⟨11, by norm_num⟩
  have hsum_le :
      ∑ j : Fin 12, |am12ExplicitCoeff j| * am12Err h t₀ yseq y (n + (j : ℕ))
        ≤ (32759306603 / 638668800 : ℝ) * E := by
    calc
      ∑ j : Fin 12, |am12ExplicitCoeff j| * am12Err h t₀ yseq y (n + (j : ℕ))
          ≤ ∑ j : Fin 12, |am12ExplicitCoeff j| * E :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (hwin j) (abs_nonneg _))
      _ = (32759306603 / 638668800 : ℝ) * E := by
        simp [am12ExplicitCoeff, am12Coeff, Fin.sum_univ_succ]
        ring
  have hstep :=
    am12_one_step_lipschitz (h := h) (L := L) hh hL hf t₀ hy y hyf n
  have hR_le :
      am12Err h t₀ yseq y (n + 11)
        + h * L * ∑ j : Fin 12,
            |am12ExplicitCoeff j| * am12Err h t₀ yseq y (n + (j : ℕ))
        + τabs
        ≤ (1 + (32759306603 / 638668800 : ℝ) * (h * L)) * E + τabs := by
    have hsum_scaled :
        h * L * ∑ j : Fin 12,
            |am12ExplicitCoeff j| * am12Err h t₀ yseq y (n + (j : ℕ))
          ≤ h * L * ((32759306603 / 638668800 : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hsum_le hx_nn
    have h_alg :
        E + h * L * ((32759306603 / 638668800 : ℝ) * E) + τabs
          = (1 + (32759306603 / 638668800 : ℝ) * (h * L)) * E + τabs := by
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
          (73174842453128 : ℝ) * (1307674368000 / 703604254357) ≤ 137143303750358 := by
        norm_num
      exact sub_nonneg.mpr (le_trans hbound hnum)
    have hprod : 0 ≤ (h * L) / 2615348736000 * (137143303750358 - 73174842453128 * (h * L)) := by
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
      (1 + (32759306603 / 638668800 : ℝ) * (h * L)) * E
        ≤ ((1 - (703604254357 / 2615348736000 : ℝ) * h * L)
            * (1 + h * (104 * L))) * E :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (703604254357 / 2615348736000 : ℝ) * h * L) * 2) * τabs := by
    have hraw := mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
    calc
      τabs = (1 : ℝ) * τabs := by ring
      _ ≤ ((1 - (703604254357 / 2615348736000 : ℝ) * h * L) * 2) * τabs := hraw
  have hfactor :
      (1 + (32759306603 / 638668800 : ℝ) * (h * L)) * E + τabs
        ≤ (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
            * ((1 + h * (104 * L)) * E + 2 * τabs) := by
    let A : ℝ := 1 - (703604254357 / 2615348736000 : ℝ) * h * L
    let B : ℝ := 1 + h * (104 * L)
    let Cg : ℝ := 1 + (32759306603 / 638668800 : ℝ) * (h * L)
    change Cg * E + τabs ≤ A * (B * E + 2 * τabs)
    have hE_part' : Cg * E ≤ (A * B) * E := hE_part
    have hτ_part' : τabs ≤ (A * 2) * τabs := hτ_part
    calc
      Cg * E + τabs ≤ (A * B) * E + (A * 2) * τabs :=
        add_le_add hE_part' hτ_part'
      _ = A * (B * E + 2 * τabs) := by ring
  have hprod :
      (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
          * am12Err h t₀ yseq y (n + 12)
        ≤ (1 - (703604254357 / 2615348736000 : ℝ) * h * L)
            * ((1 + h * (104 * L)) * E + 2 * τabs) :=
    le_trans hstep (le_trans (by simpa [hτabs_def] using hR_le) hfactor)
  have hcancel :
      am12Err h t₀ yseq y (n + 12)
        ≤ (1 + h * (104 * L)) * E + 2 * τabs :=
    le_of_mul_le_mul_left hprod hA_pos
  simpa [hE_def, hτabs_def] using hcancel

/-- Max-norm AM12 one-step recurrence on the rolling 12-window. -/
theorem am12_one_step_error_pair_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (703604254357 / 2615348736000 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsAM12Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    am12ErrWindow h t₀ yseq y (n + 1)
      ≤ (1 + h * (104 * L)) * am12ErrWindow h t₀ yseq y n
        + 2 * |adamsMoulton12.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set E : ℝ := am12ErrWindow h t₀ yseq y n with hE_def
  set τabs : ℝ :=
    |adamsMoulton12.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  set R : ℝ := (1 + h * (104 * L)) * E + 2 * τabs with hR_def
  have hE_nn : 0 ≤ E := by
    simpa [hE_def] using am12ErrWindow_nonneg h t₀ yseq y n
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hGhL_nn : 0 ≤ h * (104 * L) := by positivity
  have hE_le_R : E ≤ R := by
    have hcoef : (1 : ℝ) ≤ 1 + h * (104 * L) :=
      le_add_of_nonneg_right hGhL_nn
    have hgrow : E ≤ (1 + h * (104 * L)) * E := by
      have := mul_le_mul_of_nonneg_right hcoef hE_nn
      simpa using this
    have hplus :
        (1 + h * (104 * L)) * E ≤ R := by
      rw [hR_def]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hτ_nn)
    exact le_trans hgrow hplus
  have hwin : ∀ j : Fin 12,
      am12Err h t₀ yseq y (n + (j : ℕ)) ≤ E := by
    intro j
    show am12Err h t₀ yseq y (n + (j : ℕ))
        ≤ am12ErrWindow h t₀ yseq y n
    unfold am12ErrWindow
    exact Finset.le_sup' (b := j)
      (f := fun k : Fin 12 => am12Err h t₀ yseq y (n + (k : ℕ)))
      (Finset.mem_univ _)
  have hnew :
      am12Err h t₀ yseq y (n + 12) ≤ R := by
    simpa [hE_def, hτabs_def, hR_def] using
      (am12_one_step_error_bound (h := h) (L := L) hh hL hsmall hf t₀ hy y hyf n)
  have h_per : ∀ j : Fin 12,
      am12Err h t₀ yseq y (n + 1 + (j : ℕ)) ≤ R := by
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
  unfold am12ErrWindow
  exact Finset.sup'_le _ _ (fun j _ => by
    simpa [hE_def, hτabs_def, hR_def] using h_per j)



/-- Packed Taylor polynomial for the y-remainder pattern in the AM12 proof. -/
private noncomputable def am12_yPoly13
    (m h : ℝ) (d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t : ℝ) : ℝ :=
  (m * h) * d0
    + (m * h) ^ 2 / 2 * d2t
    + (m * h) ^ 3 / 6 * d3t
    + (m * h) ^ 4 / 24 * d4t
    + (m * h) ^ 5 / 120 * d5t
    + (m * h) ^ 6 / 720 * d6t
    + (m * h) ^ 7 / 5040 * d7t
    + (m * h) ^ 8 / 40320 * d8t
    + (m * h) ^ 9 / 362880 * d9t
    + (m * h) ^ 10 / 3628800 * d10t
    + (m * h) ^ 11 / 39916800 * d11t
    + (m * h) ^ 12 / 479001600 * d12t
    + (m * h) ^ 13 / 6227020800 * d13t

/-- Packed Taylor polynomial for the derivative-remainder pattern in the AM12 proof. -/
private noncomputable def am12_dPoly12
    (m h : ℝ) (d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t : ℝ) : ℝ :=
  (m * h) * d2t
    + (m * h) ^ 2 / 2 * d3t
    + (m * h) ^ 3 / 6 * d4t
    + (m * h) ^ 4 / 24 * d5t
    + (m * h) ^ 5 / 120 * d6t
    + (m * h) ^ 6 / 720 * d7t
    + (m * h) ^ 7 / 5040 * d8t
    + (m * h) ^ 8 / 40320 * d9t
    + (m * h) ^ 9 / 362880 * d10t
    + (m * h) ^ 10 / 3628800 * d11t
    + (m * h) ^ 11 / 39916800 * d12t
    + (m * h) ^ 12 / 479001600 * d13t

private lemma am12_residual_alg_identity
    (y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12
      d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t h : ℝ)
    (A B C D E F G H I J K L M N : ℝ)
    (hA : A = y12 - y0 - am12_yPoly13 12 h d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hB : B = y11 - y0 - am12_yPoly13 11 h d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hC : C = d12 - d0 - am12_dPoly12 12 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hD : D = d11 - d0 - am12_dPoly12 11 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hE : E = d10 - d0 - am12_dPoly12 10 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hF : F = d9 - d0 - am12_dPoly12 9 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hG : G = d8 - d0 - am12_dPoly12 8 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hH : H = d7 - d0 - am12_dPoly12 7 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hI : I = d6 - d0 - am12_dPoly12 6 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hJ : J = d5 - d0 - am12_dPoly12 5 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hK : K = d4 - d0 - am12_dPoly12 4 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hL : L = d3 - d0 - am12_dPoly12 3 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hM : M = d2 - d0 - am12_dPoly12 2 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t)
    (hN : N = d1 - d0 - am12_dPoly12 1 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t) :
    y12 - y11 - h * ((703604254357 / 2615348736000 : ℝ) * d12
                  + (3917551216986 / 2615348736000 : ℝ) * d11
                  - (6616420957428 / 2615348736000 : ℝ) * d10
                  + (13465774256510 / 2615348736000 : ℝ) * d9
                  - (21847538039895 / 2615348736000 : ℝ) * d8
                  + (27345870698436 / 2615348736000 : ℝ) * d7
                  - (26204344465152 / 2615348736000 : ℝ) * d6
                  + (19058185652796 / 2615348736000 : ℝ) * d5
                  - (10344711794985 / 2615348736000 : ℝ) * d4
                  + (4063327863170 / 2615348736000 : ℝ) * d3
                  - (1092096992268 / 2615348736000 : ℝ) * d2
                  + (179842822566 / 2615348736000 : ℝ) * d1
                  - (13695779093 / 2615348736000 : ℝ) * d0)
      = A - B
                - (703604254357 * h / 2615348736000) * C
                - (3917551216986 * h / 2615348736000) * D
                + (6616420957428 * h / 2615348736000) * E
                - (13465774256510 * h / 2615348736000) * F
                + (21847538039895 * h / 2615348736000) * G
                - (27345870698436 * h / 2615348736000) * H
                + (26204344465152 * h / 2615348736000) * I
                - (19058185652796 * h / 2615348736000) * J
                + (10344711794985 * h / 2615348736000) * K
                - (4063327863170 * h / 2615348736000) * L
                + (1092096992268 * h / 2615348736000) * M
                - (179842822566 * h / 2615348736000) * N := by
  subst hA; subst hB; subst hC; subst hD; subst hE; subst hF; subst hG; subst hH; subst hI; subst hJ; subst hK; subst hL; subst hM; subst hN
  unfold am12_yPoly13 am12_dPoly12
  ring


private lemma am12_residual_bound_alg_identity (Mb h : ℝ) :
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


private lemma am12_residual_triangle_aux
    (A B sC sD sE sF sG sH sI sJ sK sL sM sN : ℝ) :
    |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL + sM - sN|
      ≤ |A| + |B| + |sC| + |sD| + |sE| + |sF| + |sG| + |sH| + |sI| + |sJ| + |sK| + |sL| + |sM| + |sN| := by
  have h1 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL + sM - sN|
      ≤ |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL + sM| + |sN| := abs_sub _ _
  have h2 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL + sM|
      ≤ |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL| + |sM| := abs_add_le _ _
  have h3 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK - sL|
      ≤ |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK| + |sL| := abs_sub _ _
  have h4 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ + sK|
      ≤ |A - B - sC - sD + sE - sF + sG - sH + sI - sJ| + |sK| := abs_add_le _ _
  have h5 : |A - B - sC - sD + sE - sF + sG - sH + sI - sJ|
      ≤ |A - B - sC - sD + sE - sF + sG - sH + sI| + |sJ| := abs_sub _ _
  have h6 : |A - B - sC - sD + sE - sF + sG - sH + sI|
      ≤ |A - B - sC - sD + sE - sF + sG - sH| + |sI| := abs_add_le _ _
  have h7 : |A - B - sC - sD + sE - sF + sG - sH|
      ≤ |A - B - sC - sD + sE - sF + sG| + |sH| := abs_sub _ _
  have h8 : |A - B - sC - sD + sE - sF + sG|
      ≤ |A - B - sC - sD + sE - sF| + |sG| := abs_add_le _ _
  have h9 : |A - B - sC - sD + sE - sF|
      ≤ |A - B - sC - sD + sE| + |sF| := abs_sub _ _
  have h10 : |A - B - sC - sD + sE|
      ≤ |A - B - sC - sD| + |sE| := abs_add_le _ _
  have h11 : |A - B - sC - sD|
      ≤ |A - B - sC| + |sD| := abs_sub _ _
  have h12 : |A - B - sC|
      ≤ |A - B| + |sC| := abs_sub _ _
  have h13 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith


private lemma am12_residual_fourteen_term_triangle
    (A B C D E F G H I J K L M N h : ℝ) (hh : 0 ≤ h) :
    |A - B - (703604254357 * h / 2615348736000) * C - (3917551216986 * h / 2615348736000) * D + (6616420957428 * h / 2615348736000) * E - (13465774256510 * h / 2615348736000) * F + (21847538039895 * h / 2615348736000) * G - (27345870698436 * h / 2615348736000) * H + (26204344465152 * h / 2615348736000) * I - (19058185652796 * h / 2615348736000) * J + (10344711794985 * h / 2615348736000) * K - (4063327863170 * h / 2615348736000) * L + (1092096992268 * h / 2615348736000) * M - (179842822566 * h / 2615348736000) * N| ≤ |A| + |B| + (703604254357 * h / 2615348736000) * |C| + (3917551216986 * h / 2615348736000) * |D| + (6616420957428 * h / 2615348736000) * |E| + (13465774256510 * h / 2615348736000) * |F| + (21847538039895 * h / 2615348736000) * |G| + (27345870698436 * h / 2615348736000) * |H| + (26204344465152 * h / 2615348736000) * |I| + (19058185652796 * h / 2615348736000) * |J| + (10344711794985 * h / 2615348736000) * |K| + (4063327863170 * h / 2615348736000) * |L| + (1092096992268 * h / 2615348736000) * |M| + (179842822566 * h / 2615348736000) * |N| := by
  have hcC_nn : 0 ≤ 703604254357 * h / 2615348736000 := by positivity
  have hcD_nn : 0 ≤ 3917551216986 * h / 2615348736000 := by positivity
  have hcE_nn : 0 ≤ 6616420957428 * h / 2615348736000 := by positivity
  have hcF_nn : 0 ≤ 13465774256510 * h / 2615348736000 := by positivity
  have hcG_nn : 0 ≤ 21847538039895 * h / 2615348736000 := by positivity
  have hcH_nn : 0 ≤ 27345870698436 * h / 2615348736000 := by positivity
  have hcI_nn : 0 ≤ 26204344465152 * h / 2615348736000 := by positivity
  have hcJ_nn : 0 ≤ 19058185652796 * h / 2615348736000 := by positivity
  have hcK_nn : 0 ≤ 10344711794985 * h / 2615348736000 := by positivity
  have hcL_nn : 0 ≤ 4063327863170 * h / 2615348736000 := by positivity
  have hcM_nn : 0 ≤ 1092096992268 * h / 2615348736000 := by positivity
  have hcN_nn : 0 ≤ 179842822566 * h / 2615348736000 := by positivity
  have habsC : |(703604254357 * h / 2615348736000) * C| = (703604254357 * h / 2615348736000) * |C| := by
    rw [abs_mul, abs_of_nonneg hcC_nn]
  have habsD : |(3917551216986 * h / 2615348736000) * D| = (3917551216986 * h / 2615348736000) * |D| := by
    rw [abs_mul, abs_of_nonneg hcD_nn]
  have habsE : |(6616420957428 * h / 2615348736000) * E| = (6616420957428 * h / 2615348736000) * |E| := by
    rw [abs_mul, abs_of_nonneg hcE_nn]
  have habsF : |(13465774256510 * h / 2615348736000) * F| = (13465774256510 * h / 2615348736000) * |F| := by
    rw [abs_mul, abs_of_nonneg hcF_nn]
  have habsG : |(21847538039895 * h / 2615348736000) * G| = (21847538039895 * h / 2615348736000) * |G| := by
    rw [abs_mul, abs_of_nonneg hcG_nn]
  have habsH : |(27345870698436 * h / 2615348736000) * H| = (27345870698436 * h / 2615348736000) * |H| := by
    rw [abs_mul, abs_of_nonneg hcH_nn]
  have habsI : |(26204344465152 * h / 2615348736000) * I| = (26204344465152 * h / 2615348736000) * |I| := by
    rw [abs_mul, abs_of_nonneg hcI_nn]
  have habsJ : |(19058185652796 * h / 2615348736000) * J| = (19058185652796 * h / 2615348736000) * |J| := by
    rw [abs_mul, abs_of_nonneg hcJ_nn]
  have habsK : |(10344711794985 * h / 2615348736000) * K| = (10344711794985 * h / 2615348736000) * |K| := by
    rw [abs_mul, abs_of_nonneg hcK_nn]
  have habsL : |(4063327863170 * h / 2615348736000) * L| = (4063327863170 * h / 2615348736000) * |L| := by
    rw [abs_mul, abs_of_nonneg hcL_nn]
  have habsM : |(1092096992268 * h / 2615348736000) * M| = (1092096992268 * h / 2615348736000) * |M| := by
    rw [abs_mul, abs_of_nonneg hcM_nn]
  have habsN : |(179842822566 * h / 2615348736000) * N| = (179842822566 * h / 2615348736000) * |N| := by
    rw [abs_mul, abs_of_nonneg hcN_nn]
  have htri := am12_residual_triangle_aux A B ((703604254357 * h / 2615348736000) * C) ((3917551216986 * h / 2615348736000) * D) ((6616420957428 * h / 2615348736000) * E) ((13465774256510 * h / 2615348736000) * F) ((21847538039895 * h / 2615348736000) * G) ((27345870698436 * h / 2615348736000) * H) ((26204344465152 * h / 2615348736000) * I) ((19058185652796 * h / 2615348736000) * J) ((10344711794985 * h / 2615348736000) * K) ((4063327863170 * h / 2615348736000) * L) ((1092096992268 * h / 2615348736000) * M) ((179842822566 * h / 2615348736000) * N)
  rw [habsC, habsD, habsE, habsF, habsG, habsH, habsI, habsJ, habsK, habsL, habsM, habsN] at htri
  exact htri


private lemma am12_residual_combine_aux
    (A B C D E F G H I J K L M N : ℝ) {Mb h : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ Mb)
    (hA_bd : |A| ≤ Mb / 87178291200 * (12 * h) ^ 14)
    (hB_bd : |B| ≤ Mb / 87178291200 * (11 * h) ^ 14)
    (hC_bd : |C| ≤ Mb / 6227020800 * (12 * h) ^ 13)
    (hD_bd : |D| ≤ Mb / 6227020800 * (11 * h) ^ 13)
    (hE_bd : |E| ≤ Mb / 6227020800 * (10 * h) ^ 13)
    (hF_bd : |F| ≤ Mb / 6227020800 * (9 * h) ^ 13)
    (hG_bd : |G| ≤ Mb / 6227020800 * (8 * h) ^ 13)
    (hH_bd : |H| ≤ Mb / 6227020800 * (7 * h) ^ 13)
    (hI_bd : |I| ≤ Mb / 6227020800 * (6 * h) ^ 13)
    (hJ_bd : |J| ≤ Mb / 6227020800 * (5 * h) ^ 13)
    (hK_bd : |K| ≤ Mb / 6227020800 * (4 * h) ^ 13)
    (hL_bd : |L| ≤ Mb / 6227020800 * (3 * h) ^ 13)
    (hM_bd : |M| ≤ Mb / 6227020800 * (2 * h) ^ 13)
    (hN_bd : |N| ≤ Mb / 6227020800 * h ^ 13)
    : |A - B - (703604254357 * h / 2615348736000) * C - (3917551216986 * h / 2615348736000) * D + (6616420957428 * h / 2615348736000) * E - (13465774256510 * h / 2615348736000) * F + (21847538039895 * h / 2615348736000) * G - (27345870698436 * h / 2615348736000) * H + (26204344465152 * h / 2615348736000) * I - (19058185652796 * h / 2615348736000) * J + (10344711794985 * h / 2615348736000) * K - (4063327863170 * h / 2615348736000) * L + (1092096992268 * h / 2615348736000) * M - (179842822566 * h / 2615348736000) * N| ≤ (39099 : ℝ) * Mb * h ^ 14 := by
  have htri := am12_residual_fourteen_term_triangle A B C D E F G H I J K L M N h hh
  have hcC_nn : 0 ≤ 703604254357 * h / 2615348736000 := by positivity
  have hcD_nn : 0 ≤ 3917551216986 * h / 2615348736000 := by positivity
  have hcE_nn : 0 ≤ 6616420957428 * h / 2615348736000 := by positivity
  have hcF_nn : 0 ≤ 13465774256510 * h / 2615348736000 := by positivity
  have hcG_nn : 0 ≤ 21847538039895 * h / 2615348736000 := by positivity
  have hcH_nn : 0 ≤ 27345870698436 * h / 2615348736000 := by positivity
  have hcI_nn : 0 ≤ 26204344465152 * h / 2615348736000 := by positivity
  have hcJ_nn : 0 ≤ 19058185652796 * h / 2615348736000 := by positivity
  have hcK_nn : 0 ≤ 10344711794985 * h / 2615348736000 := by positivity
  have hcL_nn : 0 ≤ 4063327863170 * h / 2615348736000 := by positivity
  have hcM_nn : 0 ≤ 1092096992268 * h / 2615348736000 := by positivity
  have hcN_nn : 0 ≤ 179842822566 * h / 2615348736000 := by positivity
  have hCbd_s : (703604254357 * h / 2615348736000) * |C|
      ≤ (703604254357 * h / 2615348736000) * (Mb / 6227020800 * (12 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hC_bd hcC_nn
  have hDbd_s : (3917551216986 * h / 2615348736000) * |D|
      ≤ (3917551216986 * h / 2615348736000) * (Mb / 6227020800 * (11 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hD_bd hcD_nn
  have hEbd_s : (6616420957428 * h / 2615348736000) * |E|
      ≤ (6616420957428 * h / 2615348736000) * (Mb / 6227020800 * (10 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hE_bd hcE_nn
  have hFbd_s : (13465774256510 * h / 2615348736000) * |F|
      ≤ (13465774256510 * h / 2615348736000) * (Mb / 6227020800 * (9 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hF_bd hcF_nn
  have hGbd_s : (21847538039895 * h / 2615348736000) * |G|
      ≤ (21847538039895 * h / 2615348736000) * (Mb / 6227020800 * (8 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hG_bd hcG_nn
  have hHbd_s : (27345870698436 * h / 2615348736000) * |H|
      ≤ (27345870698436 * h / 2615348736000) * (Mb / 6227020800 * (7 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hH_bd hcH_nn
  have hIbd_s : (26204344465152 * h / 2615348736000) * |I|
      ≤ (26204344465152 * h / 2615348736000) * (Mb / 6227020800 * (6 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hI_bd hcI_nn
  have hJbd_s : (19058185652796 * h / 2615348736000) * |J|
      ≤ (19058185652796 * h / 2615348736000) * (Mb / 6227020800 * (5 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hJ_bd hcJ_nn
  have hKbd_s : (10344711794985 * h / 2615348736000) * |K|
      ≤ (10344711794985 * h / 2615348736000) * (Mb / 6227020800 * (4 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hK_bd hcK_nn
  have hLbd_s : (4063327863170 * h / 2615348736000) * |L|
      ≤ (4063327863170 * h / 2615348736000) * (Mb / 6227020800 * (3 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hL_bd hcL_nn
  have hMbd_s : (1092096992268 * h / 2615348736000) * |M|
      ≤ (1092096992268 * h / 2615348736000) * (Mb / 6227020800 * (2 * h) ^ 13) :=
    mul_le_mul_of_nonneg_left hM_bd hcM_nn
  have hNbd_s : (179842822566 * h / 2615348736000) * |N|
      ≤ (179842822566 * h / 2615348736000) * (Mb / 6227020800 * h ^ 13) :=
    mul_le_mul_of_nonneg_left hN_bd hcN_nn
  have hbound_alg := am12_residual_bound_alg_identity Mb h
  have hh14_nn : 0 ≤ h ^ 14 := by positivity
  have hMh14_nn : 0 ≤ Mb * h ^ 14 := mul_nonneg hMnn hh14_nn
  have hslack : (414541158076267641095141 / 10602754543180800000 : ℝ) * Mb * h ^ 14
      ≤ 39099 * Mb * h ^ 14 := by
    rw [mul_assoc, mul_assoc (39099 : ℝ)]
    have hle : (414541158076267641095141 / 10602754543180800000 : ℝ) ≤ 39099 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh14_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hEbd_s, hFbd_s, hGbd_s, hHbd_s, hIbd_s, hJbd_s, hKbd_s, hLbd_s, hMbd_s, hNbd_s]


/-- Pointwise AM12 truncation residual bound. -/
theorem am12_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 14 y) {a b Mb : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 14 y t| ≤ Mb)
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
    |am12Residual h t y| ≤ (39099 : ℝ) * Mb * h ^ 14 := by
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
    y_fourteenth_order_taylor_remainder hy hbnd ht ht11h h11h
  have hRy12 :=
    y_fourteenth_order_taylor_remainder hy hbnd ht ht12h h12h
  have hRyp1 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht9h h9h
  have hRyp10 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht10h h10h
  have hRyp11 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht11h h11h
  have hRyp12 :=
    derivY_thirteenth_order_taylor_remainder hy hbnd ht ht12h h12h
  unfold am12Residual
  set y0 := y t with hy0_def
  set y11 := y (t + 11 * h) with hy11_def
  set y12 := y (t + 12 * h) with hy12_def
  set d0 := deriv y (t) with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set d6 := deriv y (t + 6 * h) with hd6_def
  set d7 := deriv y (t + 7 * h) with hd7_def
  set d8 := deriv y (t + 8 * h) with hd8_def
  set d9 := deriv y (t + 9 * h) with hd9_def
  set d10 := deriv y (t + 10 * h) with hd10_def
  set d11 := deriv y (t + 11 * h) with hd11_def
  set d12 := deriv y (t + 12 * h) with hd12_def
  set d2t := iteratedDeriv 2 y t with hd2t_def
  set d3t := iteratedDeriv 3 y t with hd3t_def
  set d4t := iteratedDeriv 4 y t with hd4t_def
  set d5t := iteratedDeriv 5 y t with hd5t_def
  set d6t := iteratedDeriv 6 y t with hd6t_def
  set d7t := iteratedDeriv 7 y t with hd7t_def
  set d8t := iteratedDeriv 8 y t with hd8t_def
  set d9t := iteratedDeriv 9 y t with hd9t_def
  set d10t := iteratedDeriv 10 y t with hd10t_def
  set d11t := iteratedDeriv 11 y t with hd11t_def
  set d12t := iteratedDeriv 12 y t with hd12t_def
  set d13t := iteratedDeriv 13 y t with hd13t_def
  clear_value y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12
    d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t
  set A := y12 - y0 - (12 * h) * d0
            - (12 * h) ^ 2 / 2 * d2t
            - (12 * h) ^ 3 / 6 * d3t
            - (12 * h) ^ 4 / 24 * d4t
            - (12 * h) ^ 5 / 120 * d5t
            - (12 * h) ^ 6 / 720 * d6t
            - (12 * h) ^ 7 / 5040 * d7t
            - (12 * h) ^ 8 / 40320 * d8t
            - (12 * h) ^ 9 / 362880 * d9t
            - (12 * h) ^ 10 / 3628800 * d10t
            - (12 * h) ^ 11 / 39916800 * d11t
            - (12 * h) ^ 12 / 479001600 * d12t
            - (12 * h) ^ 13 / 6227020800 * d13t with hA_def
  set B := y11 - y0 - (11 * h) * d0
            - (11 * h) ^ 2 / 2 * d2t
            - (11 * h) ^ 3 / 6 * d3t
            - (11 * h) ^ 4 / 24 * d4t
            - (11 * h) ^ 5 / 120 * d5t
            - (11 * h) ^ 6 / 720 * d6t
            - (11 * h) ^ 7 / 5040 * d7t
            - (11 * h) ^ 8 / 40320 * d8t
            - (11 * h) ^ 9 / 362880 * d9t
            - (11 * h) ^ 10 / 3628800 * d10t
            - (11 * h) ^ 11 / 39916800 * d11t
            - (11 * h) ^ 12 / 479001600 * d12t
            - (11 * h) ^ 13 / 6227020800 * d13t with hB_def
  set C := d12 - d0
                - (12 * h) * d2t
                - (12 * h) ^ 2 / 2 * d3t
                - (12 * h) ^ 3 / 6 * d4t
                - (12 * h) ^ 4 / 24 * d5t
                - (12 * h) ^ 5 / 120 * d6t
                - (12 * h) ^ 6 / 720 * d7t
                - (12 * h) ^ 7 / 5040 * d8t
                - (12 * h) ^ 8 / 40320 * d9t
                - (12 * h) ^ 9 / 362880 * d10t
                - (12 * h) ^ 10 / 3628800 * d11t
                - (12 * h) ^ 11 / 39916800 * d12t
                - (12 * h) ^ 12 / 479001600 * d13t with hC_def
  set D := d11 - d0
                - (11 * h) * d2t
                - (11 * h) ^ 2 / 2 * d3t
                - (11 * h) ^ 3 / 6 * d4t
                - (11 * h) ^ 4 / 24 * d5t
                - (11 * h) ^ 5 / 120 * d6t
                - (11 * h) ^ 6 / 720 * d7t
                - (11 * h) ^ 7 / 5040 * d8t
                - (11 * h) ^ 8 / 40320 * d9t
                - (11 * h) ^ 9 / 362880 * d10t
                - (11 * h) ^ 10 / 3628800 * d11t
                - (11 * h) ^ 11 / 39916800 * d12t
                - (11 * h) ^ 12 / 479001600 * d13t with hD_def
  set E := d10 - d0
                - (10 * h) * d2t
                - (10 * h) ^ 2 / 2 * d3t
                - (10 * h) ^ 3 / 6 * d4t
                - (10 * h) ^ 4 / 24 * d5t
                - (10 * h) ^ 5 / 120 * d6t
                - (10 * h) ^ 6 / 720 * d7t
                - (10 * h) ^ 7 / 5040 * d8t
                - (10 * h) ^ 8 / 40320 * d9t
                - (10 * h) ^ 9 / 362880 * d10t
                - (10 * h) ^ 10 / 3628800 * d11t
                - (10 * h) ^ 11 / 39916800 * d12t
                - (10 * h) ^ 12 / 479001600 * d13t with hE_def
  set F := d9 - d0
                - (9 * h) * d2t
                - (9 * h) ^ 2 / 2 * d3t
                - (9 * h) ^ 3 / 6 * d4t
                - (9 * h) ^ 4 / 24 * d5t
                - (9 * h) ^ 5 / 120 * d6t
                - (9 * h) ^ 6 / 720 * d7t
                - (9 * h) ^ 7 / 5040 * d8t
                - (9 * h) ^ 8 / 40320 * d9t
                - (9 * h) ^ 9 / 362880 * d10t
                - (9 * h) ^ 10 / 3628800 * d11t
                - (9 * h) ^ 11 / 39916800 * d12t
                - (9 * h) ^ 12 / 479001600 * d13t with hF_def
  set G := d8 - d0
                - (8 * h) * d2t
                - (8 * h) ^ 2 / 2 * d3t
                - (8 * h) ^ 3 / 6 * d4t
                - (8 * h) ^ 4 / 24 * d5t
                - (8 * h) ^ 5 / 120 * d6t
                - (8 * h) ^ 6 / 720 * d7t
                - (8 * h) ^ 7 / 5040 * d8t
                - (8 * h) ^ 8 / 40320 * d9t
                - (8 * h) ^ 9 / 362880 * d10t
                - (8 * h) ^ 10 / 3628800 * d11t
                - (8 * h) ^ 11 / 39916800 * d12t
                - (8 * h) ^ 12 / 479001600 * d13t with hG_def
  set H := d7 - d0
                - (7 * h) * d2t
                - (7 * h) ^ 2 / 2 * d3t
                - (7 * h) ^ 3 / 6 * d4t
                - (7 * h) ^ 4 / 24 * d5t
                - (7 * h) ^ 5 / 120 * d6t
                - (7 * h) ^ 6 / 720 * d7t
                - (7 * h) ^ 7 / 5040 * d8t
                - (7 * h) ^ 8 / 40320 * d9t
                - (7 * h) ^ 9 / 362880 * d10t
                - (7 * h) ^ 10 / 3628800 * d11t
                - (7 * h) ^ 11 / 39916800 * d12t
                - (7 * h) ^ 12 / 479001600 * d13t with hH_def
  set I := d6 - d0
                - (6 * h) * d2t
                - (6 * h) ^ 2 / 2 * d3t
                - (6 * h) ^ 3 / 6 * d4t
                - (6 * h) ^ 4 / 24 * d5t
                - (6 * h) ^ 5 / 120 * d6t
                - (6 * h) ^ 6 / 720 * d7t
                - (6 * h) ^ 7 / 5040 * d8t
                - (6 * h) ^ 8 / 40320 * d9t
                - (6 * h) ^ 9 / 362880 * d10t
                - (6 * h) ^ 10 / 3628800 * d11t
                - (6 * h) ^ 11 / 39916800 * d12t
                - (6 * h) ^ 12 / 479001600 * d13t with hI_def
  set J := d5 - d0
                - (5 * h) * d2t
                - (5 * h) ^ 2 / 2 * d3t
                - (5 * h) ^ 3 / 6 * d4t
                - (5 * h) ^ 4 / 24 * d5t
                - (5 * h) ^ 5 / 120 * d6t
                - (5 * h) ^ 6 / 720 * d7t
                - (5 * h) ^ 7 / 5040 * d8t
                - (5 * h) ^ 8 / 40320 * d9t
                - (5 * h) ^ 9 / 362880 * d10t
                - (5 * h) ^ 10 / 3628800 * d11t
                - (5 * h) ^ 11 / 39916800 * d12t
                - (5 * h) ^ 12 / 479001600 * d13t with hJ_def
  set K := d4 - d0
                - (4 * h) * d2t
                - (4 * h) ^ 2 / 2 * d3t
                - (4 * h) ^ 3 / 6 * d4t
                - (4 * h) ^ 4 / 24 * d5t
                - (4 * h) ^ 5 / 120 * d6t
                - (4 * h) ^ 6 / 720 * d7t
                - (4 * h) ^ 7 / 5040 * d8t
                - (4 * h) ^ 8 / 40320 * d9t
                - (4 * h) ^ 9 / 362880 * d10t
                - (4 * h) ^ 10 / 3628800 * d11t
                - (4 * h) ^ 11 / 39916800 * d12t
                - (4 * h) ^ 12 / 479001600 * d13t with hK_def
  set L := d3 - d0
                - (3 * h) * d2t
                - (3 * h) ^ 2 / 2 * d3t
                - (3 * h) ^ 3 / 6 * d4t
                - (3 * h) ^ 4 / 24 * d5t
                - (3 * h) ^ 5 / 120 * d6t
                - (3 * h) ^ 6 / 720 * d7t
                - (3 * h) ^ 7 / 5040 * d8t
                - (3 * h) ^ 8 / 40320 * d9t
                - (3 * h) ^ 9 / 362880 * d10t
                - (3 * h) ^ 10 / 3628800 * d11t
                - (3 * h) ^ 11 / 39916800 * d12t
                - (3 * h) ^ 12 / 479001600 * d13t with hL_def
  set M := d2 - d0
                - (2 * h) * d2t
                - (2 * h) ^ 2 / 2 * d3t
                - (2 * h) ^ 3 / 6 * d4t
                - (2 * h) ^ 4 / 24 * d5t
                - (2 * h) ^ 5 / 120 * d6t
                - (2 * h) ^ 6 / 720 * d7t
                - (2 * h) ^ 7 / 5040 * d8t
                - (2 * h) ^ 8 / 40320 * d9t
                - (2 * h) ^ 9 / 362880 * d10t
                - (2 * h) ^ 10 / 3628800 * d11t
                - (2 * h) ^ 11 / 39916800 * d12t
                - (2 * h) ^ 12 / 479001600 * d13t with hM_def
  set N := d1 - d0
                - h * d2t
                - h ^ 2 / 2 * d3t
                - h ^ 3 / 6 * d4t
                - h ^ 4 / 24 * d5t
                - h ^ 5 / 120 * d6t
                - h ^ 6 / 720 * d7t
                - h ^ 7 / 5040 * d8t
                - h ^ 8 / 40320 * d9t
                - h ^ 9 / 362880 * d10t
                - h ^ 10 / 3628800 * d11t
                - h ^ 11 / 39916800 * d12t
                - h ^ 12 / 479001600 * d13t with hN_def
  clear_value A B C D E F G H I J K L M N
  have hA_pack : A = y12 - y0 - am12_yPoly13 12 h d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hA_def]; unfold am12_yPoly13; ring
  have hB_pack : B = y11 - y0 - am12_yPoly13 11 h d0 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hB_def]; unfold am12_yPoly13; ring
  have hC_pack : C = d12 - d0 - am12_dPoly12 12 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hC_def]; unfold am12_dPoly12; ring
  have hD_pack : D = d11 - d0 - am12_dPoly12 11 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hD_def]; unfold am12_dPoly12; ring
  have hE_pack : E = d10 - d0 - am12_dPoly12 10 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hE_def]; unfold am12_dPoly12; ring
  have hF_pack : F = d9 - d0 - am12_dPoly12 9 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hF_def]; unfold am12_dPoly12; ring
  have hG_pack : G = d8 - d0 - am12_dPoly12 8 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hG_def]; unfold am12_dPoly12; ring
  have hH_pack : H = d7 - d0 - am12_dPoly12 7 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hH_def]; unfold am12_dPoly12; ring
  have hI_pack : I = d6 - d0 - am12_dPoly12 6 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hI_def]; unfold am12_dPoly12; ring
  have hJ_pack : J = d5 - d0 - am12_dPoly12 5 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hJ_def]; unfold am12_dPoly12; ring
  have hK_pack : K = d4 - d0 - am12_dPoly12 4 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hK_def]; unfold am12_dPoly12; ring
  have hL_pack : L = d3 - d0 - am12_dPoly12 3 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hL_def]; unfold am12_dPoly12; ring
  have hM_pack : M = d2 - d0 - am12_dPoly12 2 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hM_def]; unfold am12_dPoly12; ring
  have hN_pack : N = d1 - d0 - am12_dPoly12 1 h d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t := by
    rw [hN_def]; unfold am12_dPoly12; ring
  have hLTE_eq :=
    am12_residual_alg_identity y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t d13t h A B C D E F G H I J K L M N hA_pack hB_pack hC_pack hD_pack hE_pack hF_pack hG_pack hH_pack hI_pack hJ_pack hK_pack hL_pack hM_pack hN_pack
  have hres_eq :
      y12 - y11 - h * (∑ j : Fin 13,
          am12Coeff j * deriv y (t + (j : ℕ) * h))
        =
          y12 - y11
            - h * ((703604254357 / 2615348736000 : ℝ) * d12
                  + (3917551216986 / 2615348736000 : ℝ) * d11
                  - (6616420957428 / 2615348736000 : ℝ) * d10
                  + (13465774256510 / 2615348736000 : ℝ) * d9
                  - (21847538039895 / 2615348736000 : ℝ) * d8
                  + (27345870698436 / 2615348736000 : ℝ) * d7
                  - (26204344465152 / 2615348736000 : ℝ) * d6
                  + (19058185652796 / 2615348736000 : ℝ) * d5
                  - (10344711794985 / 2615348736000 : ℝ) * d4
                  + (4063327863170 / 2615348736000 : ℝ) * d3
                  - (1092096992268 / 2615348736000 : ℝ) * d2
                  + (179842822566 / 2615348736000 : ℝ) * d1
                  - (13695779093 / 2615348736000 : ℝ) * d0) := by
    simp [am12Coeff, Fin.sum_univ_succ, hd0_def, hd1_def, hd2_def, hd3_def, hd4_def, hd5_def, hd6_def, hd7_def, hd8_def, hd9_def, hd10_def, hd11_def, hd12_def]
    ring_nf
    norm_num
  rw [hres_eq, hLTE_eq]
  have hA_bd : |A| ≤ Mb / 87178291200 * (12 * h) ^ 14 := hRy12
  have hB_bd : |B| ≤ Mb / 87178291200 * (11 * h) ^ 14 := hRy11
  have hC_bd : |C| ≤ Mb / 6227020800 * (12 * h) ^ 13 := hRyp12
  have hD_bd : |D| ≤ Mb / 6227020800 * (11 * h) ^ 13 := hRyp11
  have hE_bd : |E| ≤ Mb / 6227020800 * (10 * h) ^ 13 := hRyp10
  have hF_bd : |F| ≤ Mb / 6227020800 * (9 * h) ^ 13 := hRyp9
  have hG_bd : |G| ≤ Mb / 6227020800 * (8 * h) ^ 13 := hRyp8
  have hH_bd : |H| ≤ Mb / 6227020800 * (7 * h) ^ 13 := hRyp7
  have hI_bd : |I| ≤ Mb / 6227020800 * (6 * h) ^ 13 := hRyp6
  have hJ_bd : |J| ≤ Mb / 6227020800 * (5 * h) ^ 13 := hRyp5
  have hK_bd : |K| ≤ Mb / 6227020800 * (4 * h) ^ 13 := hRyp4
  have hL_bd : |L| ≤ Mb / 6227020800 * (3 * h) ^ 13 := hRyp3
  have hM_bd : |M| ≤ Mb / 6227020800 * (2 * h) ^ 13 := hRyp2
  have hN_bd : |N| ≤ Mb / 6227020800 * h ^ 13 := hRyp1
  have hMnn : 0 ≤ Mb := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact am12_residual_combine_aux A B C D E F G H I J K L M N hh hMnn hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hH_bd hI_bd hJ_bd hK_bd hL_bd hM_bd hN_bd


/-- Uniform bound on the AM12 one-step truncation residual on a finite
horizon, given a `C^14` exact solution. -/
theorem am12_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 14 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 12) * h ≤ T →
        |adamsMoulton12.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 14 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_fourteen_bounded_on_Icc hy t₀ (t₀ + T + 1)
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
  have hpoint :=
    am12_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem ht10h_mem ht11h_mem ht12h_mem hh.le
  rw [am12_localTruncationError_eq]
  exact hpoint


/-- Headline AM12 global error bound. -/
theorem am12_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 14 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (703604254357 / 2615348736000 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsAM12Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      |yseq 2 - y (t₀ + 2 * h)| ≤ ε₀ →
      |yseq 3 - y (t₀ + 3 * h)| ≤ ε₀ →
      |yseq 4 - y (t₀ + 4 * h)| ≤ ε₀ →
      |yseq 5 - y (t₀ + 5 * h)| ≤ ε₀ →
      |yseq 6 - y (t₀ + 6 * h)| ≤ ε₀ →
      |yseq 7 - y (t₀ + 7 * h)| ≤ ε₀ →
      |yseq 8 - y (t₀ + 8 * h)| ≤ ε₀ →
      |yseq 9 - y (t₀ + 9 * h)| ≤ ε₀ →
      |yseq 10 - y (t₀ + 10 * h)| ≤ ε₀ →
      |yseq 11 - y (t₀ + 11 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 11) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((104 * L) * T) * ε₀ + K * h ^ 12 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am12_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((104 * L) * T) * (2 * C), min δ 1, ?_,
    lt_min hδ_pos (by norm_num), ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδg_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd he10_bd he11_bd N hNh
  have hδ_le : h ≤ δ := le_trans hδg_le (min_le_left δ 1)
  have h_le_one : h ≤ 1 := le_trans hδg_le (min_le_right δ 1)
  set EN : ℕ → ℝ := fun k => am12ErrWindow h t₀ yseq y k with hEN_def
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k => by
    simpa [hEN_def] using am12ErrWindow_nonneg h t₀ yseq y k
  have hEN0_le : EN 0 ≤ ε₀ := by
    unfold EN
    unfold am12ErrWindow
    apply Finset.sup'_le
    intro j _
    fin_cases j
    · simpa [am12Err] using he0_bd
    · simpa [am12Err] using he1_bd
    · simpa [am12Err] using he2_bd
    · simpa [am12Err] using he3_bd
    · simpa [am12Err] using he4_bd
    · simpa [am12Err] using he5_bd
    · simpa [am12Err] using he6_bd
    · simpa [am12Err] using he7_bd
    · simpa [am12Err] using he8_bd
    · simpa [am12Err] using he9_bd
    · simpa [am12Err] using he10_bd
    · simpa [am12Err] using he11_bd
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
      am12_one_step_error_pair_bound (h := h) (L := L) hh.le hL hsmall
        hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hres_arg
    have h2τ : 2 * |adamsMoulton12.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (2 * C) * h ^ 13 := by
      have h2res : 2 * |adamsMoulton12.localTruncationError h
          (t₀ + (n : ℝ) * h) y| ≤ 2 * (C * h ^ 14) :=
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
  have hpoint_le_window : am12Err h t₀ yseq y N ≤ EN N := by
    show am12Err h t₀ yseq y N ≤ am12ErrWindow h t₀ yseq y N
    unfold am12ErrWindow
    have hsup := Finset.le_sup' (b := (0 : Fin 12))
      (f := fun j : Fin 12 => am12Err h t₀ yseq y (N + (j : ℕ)))
      (Finset.mem_univ _)
    simpa using hsup
  calc
    |yseq N - y (t₀ + (N : ℝ) * h)|
        = am12Err h t₀ yseq y N := rfl
    _ ≤ EN N := hpoint_le_window
    _ ≤ Real.exp ((104 * L) * T) * ε₀
        + T * Real.exp ((104 * L) * T) * (2 * C) * h ^ 12 := hEN_bound



end LMM
