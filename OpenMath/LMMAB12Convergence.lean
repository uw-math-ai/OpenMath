import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB11Convergence

/-! ## Adams-Bashforth 12-step Scalar Convergence Chain (Iserles §1.2)

Order-12 explicit 12-step Adams-Bashforth scalar convergence scaffold. The
AB12 weights were computed by exact `Fraction` integration of the Lagrange
basis on nodes `0,...,11` over `[11, 12]`; their absolute sum is
`443892 / 385`.

The weights, ordered from `f_n` through `f_(n+11)`, are
`(-262747265, 3158642445, -17410248271, 58189107627, -131365867290,
211103573298, -247741639374, 214139355366, -135579356757, 61633227185,
-19433810163, 4527766399) / 958003200`.

This file also adds public thirteenth-order scalar Taylor helpers for future
AM11 / AB12-vector work.
-/

namespace LMM

/-! ### Thirteenth-order Taylor helpers (public, reusable for AM11 / AB12-vector) -/

/-- A `C^13` function has its thirteenth derivative bounded on every compact
interval `[a, b]`. -/
theorem iteratedDeriv_thirteen_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 13 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 13 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 13 y) :=
    hy.continuous_iteratedDeriv 13 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise thirteenth-order Taylor (Lagrange) remainder bound. -/
theorem y_thirteenth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 13 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 13 y t| ≤ M)
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
        - r ^ 12 / 479001600 * iteratedDeriv 12 y t|
      ≤ M / 6227020800 * r ^ 13 := by
  by_cases hr' : r = 0
  · subst hr'
    simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 12 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 13 y ξ * r ^ 13 / 6227020800 := by
    have hcdo : ContDiffOn ℝ 13 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 12) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 13 = r ^ 13 := by ring
    have hfact : (((12 + 1 : ℕ).factorial : ℝ)) = 6227020800 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval y 12 (Set.Icc t (t + r)) t (t + r)
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
              + r ^ 12 / 479001600 * iteratedDeriv 12 y t := by
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
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 13 y ξ| ≤ M := hbnd ξ hξ_in
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
        = iteratedDeriv 13 y ξ * r ^ 13 / 6227020800 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 13 y ξ * r ^ 13 / 6227020800
      = (iteratedDeriv 13 y ξ) * (r ^ 13 / 6227020800) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 13 / 6227020800)]
  calc |iteratedDeriv 13 y ξ| * (r ^ 13 / 6227020800)
      ≤ M * (r ^ 13 / 6227020800) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 6227020800 * r ^ 13 := by ring

/-- Pointwise twelfth-order Taylor (Lagrange) remainder bound for the
derivative. -/
theorem derivY_twelfth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 13 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 13 y t| ≤ M)
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
        - r ^ 11 / 39916800 * iteratedDeriv 12 y t|
      ≤ M / 479001600 * r ^ 12 := by
  by_cases hr' : r = 0
  · subst hr'
    simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  have hdy : ContDiff ℝ 12 (deriv y) := hy.deriv'
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r)
          - taylorWithinEval (deriv y) 11 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 12 (deriv y) ξ * r ^ 12 / 479001600 := by
    have hcdo : ContDiffOn ℝ 12 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 11) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 12 = r ^ 12 := by ring
    have hfact : (((11 + 1 : ℕ).factorial : ℝ)) = 479001600 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval (deriv y) 11 (Set.Icc t (t + r)) t (t + r)
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
              + r ^ 11 / 39916800 * iteratedDeriv 12 y t := by
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
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hidd_eq : iteratedDeriv 12 (deriv y) = iteratedDeriv 13 y := by
    have : iteratedDeriv 13 y = iteratedDeriv 12 (deriv y) :=
      iteratedDeriv_succ' (n := 12) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 13 y ξ| ≤ M := hbnd ξ hξ_in
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
        = iteratedDeriv 13 y ξ * r ^ 12 / 479001600 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 13 y ξ * r ^ 12 / 479001600
      = (iteratedDeriv 13 y ξ) * (r ^ 12 / 479001600) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 12 / 479001600)]
  calc |iteratedDeriv 13 y ξ| * (r ^ 12 / 479001600)
      ≤ M * (r ^ 12 / 479001600) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 479001600 * r ^ 12 := by ring

/-! ### AB12 coefficients and iteration -/

/-- AB12 coefficient vector for the generic AB scaffold, ordered from the
oldest sample `f_n` through `f_(n+11)`. -/
noncomputable def ab12GenericCoeff : Fin 12 → ℝ :=
  ![-(262747265 : ℝ) / 958003200, (3158642445 : ℝ) / 958003200, -(17410248271 : ℝ) / 958003200, (58189107627 : ℝ) / 958003200, -(131365867290 : ℝ) / 958003200, (211103573298 : ℝ) / 958003200, -(247741639374 : ℝ) / 958003200, (214139355366 : ℝ) / 958003200, -(135579356757 : ℝ) / 958003200, (61633227185 : ℝ) / 958003200, -(19433810163 : ℝ) / 958003200, (4527766399 : ℝ) / 958003200]

@[simp] lemma ab12GenericCoeff_zero :
    ab12GenericCoeff 0 = -(262747265 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_one :
    ab12GenericCoeff 1 = (3158642445 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_two :
    ab12GenericCoeff 2 = -(17410248271 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_three :
    ab12GenericCoeff 3 = (58189107627 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_four :
    ab12GenericCoeff 4 = -(131365867290 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_five :
    ab12GenericCoeff 5 = (211103573298 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_six :
    ab12GenericCoeff 6 = -(247741639374 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_seven :
    ab12GenericCoeff 7 = (214139355366 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_eight :
    ab12GenericCoeff 8 = -(135579356757 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_nine :
    ab12GenericCoeff 9 = (61633227185 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_ten :
    ab12GenericCoeff 10 = -(19433810163 : ℝ) / 958003200 := rfl
@[simp] lemma ab12GenericCoeff_eleven :
    ab12GenericCoeff 11 = (4527766399 : ℝ) / 958003200 := rfl

private lemma sum_univ_twelve_aux {α : Type*} [AddCommMonoid α] (f : Fin 12 → α) :
    ∑ j : Fin 12, f j
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp [Fin.sum_univ_succ]
  ac_rfl

/-- The AB12 absolute coefficient sum is `443892/385`. -/
lemma abLip_ab12GenericCoeff (L : ℝ) :
    abLip 12 ab12GenericCoeff L = (443892 / 385) * L := by
  rw [abLip, sum_univ_twelve_aux, ab12GenericCoeff_zero, ab12GenericCoeff_one,
    ab12GenericCoeff_two, ab12GenericCoeff_three, ab12GenericCoeff_four,
    ab12GenericCoeff_five, ab12GenericCoeff_six, ab12GenericCoeff_seven,
    ab12GenericCoeff_eight, ab12GenericCoeff_nine, ab12GenericCoeff_ten,
    ab12GenericCoeff_eleven]
  norm_num
  ring

/-- AB12 iteration with twelve starting samples. -/
noncomputable def ab12Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) : ℕ → ℝ :=
  abIter 12 ab12GenericCoeff h f t₀
    ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁]

@[simp] lemma ab12Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 0 = y₀ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 1 = y₁ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 2 = y₂ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_three
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 3 = y₃ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_four
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 4 = y₄ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_five
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 5 = y₅ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_six
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 6 = y₆ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_seven
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 7 = y₇ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_eight
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 8 = y₈ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_nine
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 9 = y₉ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_ten
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 10 = y₁₀ := by
  unfold ab12Iter abIter
  simp

@[simp] lemma ab12Iter_eleven
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ 11 = y₁₁ := by
  unfold ab12Iter abIter
  simp

lemma ab12Iter_succ_twelve
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ)
    (n : ℕ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 12)
      = ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + 11)
        + h * ∑ j : Fin 12,
            ab12GenericCoeff j *
              f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                (ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ (n + (j : ℕ))) := by
  simpa [ab12Iter] using
    (abIter_step 12 (by norm_num : 0 < 12) ab12GenericCoeff h f t₀
      ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] n)

/-! ### Truncation residual and one-step bounds -/

/-- AB12 local truncation operator reduces to the textbook residual. -/
theorem ab12_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth12.localTruncationError h t y
      = y (t + 12 * h) - y (t + 11 * h)
        - h * (             (4527766399 / 958003200 : ℝ) * deriv y (t + 11 * h)
             - (19433810163 / 958003200 : ℝ) * deriv y (t + 10 * h)
             + (61633227185 / 958003200 : ℝ) * deriv y (t + 9 * h)
             - (135579356757 / 958003200 : ℝ) * deriv y (t + 8 * h)
             + (214139355366 / 958003200 : ℝ) * deriv y (t + 7 * h)
             - (247741639374 / 958003200 : ℝ) * deriv y (t + 6 * h)
             + (211103573298 / 958003200 : ℝ) * deriv y (t + 5 * h)
             - (131365867290 / 958003200 : ℝ) * deriv y (t + 4 * h)
             + (58189107627 / 958003200 : ℝ) * deriv y (t + 3 * h)
             - (17410248271 / 958003200 : ℝ) * deriv y (t + 2 * h)
             + (3158642445 / 958003200 : ℝ) * deriv y (t + h)
             - (262747265 / 958003200 : ℝ) * deriv y (t)) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth12, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  norm_num
  ring

/-- Bridge: the AB12 scalar truncation residual at base point `t₀ + n · h`
equals the generic AB residual at index `n`. -/
lemma ab12Residual_eq_abResidual
    (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    adamsBashforth12.localTruncationError h (t₀ + (n : ℝ) * h) y
      = abResidual 12 ab12GenericCoeff h y t₀ n := by
  rw [ab12_localTruncationError_eq]
  unfold abResidual
  rw [sum_univ_twelve_aux, ab12GenericCoeff_zero, ab12GenericCoeff_one,
    ab12GenericCoeff_two, ab12GenericCoeff_three, ab12GenericCoeff_four,
    ab12GenericCoeff_five, ab12GenericCoeff_six, ab12GenericCoeff_seven,
    ab12GenericCoeff_eight, ab12GenericCoeff_nine, ab12GenericCoeff_ten,
    ab12GenericCoeff_eleven]
  norm_num
  ring_nf

/-- Generic-facing AB12 one-step Lipschitz recurrence. -/
theorem ab12_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindow (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y (n + 1)
      ≤ (1 + h * ((443892 / 385) * L))
          * abErrWindow (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y n
        + |adamsBashforth12.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  have hgen :=
    abIter_lipschitz_one_step (s := 12)
      (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff hh hL hf t₀
      ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y hyf n
  rw [abLip_ab12GenericCoeff L] at hgen
  rw [← ab12Residual_eq_abResidual h y t₀ n] at hgen
  exact hgen

/-- Max-window AB12 one-step error recurrence with effective constant
`(443892/385) * L`. -/
theorem ab12_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindow (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y (n + 1)
      ≤ (1 + h * ((443892 / 385) * L))
          * abErrWindow (by norm_num : (1 : ℕ) ≤ 12) ab12GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] y n
        + |adamsBashforth12.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  exact ab12_one_step_lipschitz hh hL hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y hyf n

/-! ### Residual bound -/

private lemma ab12_residual_alg_identity
    (y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d2t d3t d4t d5t d6t d7t d8t
      d9t d10t d11t d12t h : ℝ)
    (A B C D E F G H I J K L M : ℝ)
    (hA : A = y12 - y0 - (12 * h) * d0
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
            - (12 * h) ^ 12 / 479001600 * d12t)
    (hB : B = y11 - y0 - (11 * h) * d0
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
            - (11 * h) ^ 12 / 479001600 * d12t)
    (hC : C = d11 - d0 - (11 * h) * d2t
                - (11 * h) ^ 2 / 2 * d3t
                - (11 * h) ^ 3 / 6 * d4t
                - (11 * h) ^ 4 / 24 * d5t
                - (11 * h) ^ 5 / 120 * d6t
                - (11 * h) ^ 6 / 720 * d7t
                - (11 * h) ^ 7 / 5040 * d8t
                - (11 * h) ^ 8 / 40320 * d9t
                - (11 * h) ^ 9 / 362880 * d10t
                - (11 * h) ^ 10 / 3628800 * d11t
                - (11 * h) ^ 11 / 39916800 * d12t)
    (hD : D = d10 - d0 - (10 * h) * d2t
                - (10 * h) ^ 2 / 2 * d3t
                - (10 * h) ^ 3 / 6 * d4t
                - (10 * h) ^ 4 / 24 * d5t
                - (10 * h) ^ 5 / 120 * d6t
                - (10 * h) ^ 6 / 720 * d7t
                - (10 * h) ^ 7 / 5040 * d8t
                - (10 * h) ^ 8 / 40320 * d9t
                - (10 * h) ^ 9 / 362880 * d10t
                - (10 * h) ^ 10 / 3628800 * d11t
                - (10 * h) ^ 11 / 39916800 * d12t)
    (hE : E = d9 - d0 - (9 * h) * d2t
                - (9 * h) ^ 2 / 2 * d3t
                - (9 * h) ^ 3 / 6 * d4t
                - (9 * h) ^ 4 / 24 * d5t
                - (9 * h) ^ 5 / 120 * d6t
                - (9 * h) ^ 6 / 720 * d7t
                - (9 * h) ^ 7 / 5040 * d8t
                - (9 * h) ^ 8 / 40320 * d9t
                - (9 * h) ^ 9 / 362880 * d10t
                - (9 * h) ^ 10 / 3628800 * d11t
                - (9 * h) ^ 11 / 39916800 * d12t)
    (hF : F = d8 - d0 - (8 * h) * d2t
                - (8 * h) ^ 2 / 2 * d3t
                - (8 * h) ^ 3 / 6 * d4t
                - (8 * h) ^ 4 / 24 * d5t
                - (8 * h) ^ 5 / 120 * d6t
                - (8 * h) ^ 6 / 720 * d7t
                - (8 * h) ^ 7 / 5040 * d8t
                - (8 * h) ^ 8 / 40320 * d9t
                - (8 * h) ^ 9 / 362880 * d10t
                - (8 * h) ^ 10 / 3628800 * d11t
                - (8 * h) ^ 11 / 39916800 * d12t)
    (hG : G = d7 - d0 - (7 * h) * d2t
                - (7 * h) ^ 2 / 2 * d3t
                - (7 * h) ^ 3 / 6 * d4t
                - (7 * h) ^ 4 / 24 * d5t
                - (7 * h) ^ 5 / 120 * d6t
                - (7 * h) ^ 6 / 720 * d7t
                - (7 * h) ^ 7 / 5040 * d8t
                - (7 * h) ^ 8 / 40320 * d9t
                - (7 * h) ^ 9 / 362880 * d10t
                - (7 * h) ^ 10 / 3628800 * d11t
                - (7 * h) ^ 11 / 39916800 * d12t)
    (hH : H = d6 - d0 - (6 * h) * d2t
                - (6 * h) ^ 2 / 2 * d3t
                - (6 * h) ^ 3 / 6 * d4t
                - (6 * h) ^ 4 / 24 * d5t
                - (6 * h) ^ 5 / 120 * d6t
                - (6 * h) ^ 6 / 720 * d7t
                - (6 * h) ^ 7 / 5040 * d8t
                - (6 * h) ^ 8 / 40320 * d9t
                - (6 * h) ^ 9 / 362880 * d10t
                - (6 * h) ^ 10 / 3628800 * d11t
                - (6 * h) ^ 11 / 39916800 * d12t)
    (hI : I = d5 - d0 - (5 * h) * d2t
                - (5 * h) ^ 2 / 2 * d3t
                - (5 * h) ^ 3 / 6 * d4t
                - (5 * h) ^ 4 / 24 * d5t
                - (5 * h) ^ 5 / 120 * d6t
                - (5 * h) ^ 6 / 720 * d7t
                - (5 * h) ^ 7 / 5040 * d8t
                - (5 * h) ^ 8 / 40320 * d9t
                - (5 * h) ^ 9 / 362880 * d10t
                - (5 * h) ^ 10 / 3628800 * d11t
                - (5 * h) ^ 11 / 39916800 * d12t)
    (hJ : J = d4 - d0 - (4 * h) * d2t
                - (4 * h) ^ 2 / 2 * d3t
                - (4 * h) ^ 3 / 6 * d4t
                - (4 * h) ^ 4 / 24 * d5t
                - (4 * h) ^ 5 / 120 * d6t
                - (4 * h) ^ 6 / 720 * d7t
                - (4 * h) ^ 7 / 5040 * d8t
                - (4 * h) ^ 8 / 40320 * d9t
                - (4 * h) ^ 9 / 362880 * d10t
                - (4 * h) ^ 10 / 3628800 * d11t
                - (4 * h) ^ 11 / 39916800 * d12t)
    (hK : K = d3 - d0 - (3 * h) * d2t
                - (3 * h) ^ 2 / 2 * d3t
                - (3 * h) ^ 3 / 6 * d4t
                - (3 * h) ^ 4 / 24 * d5t
                - (3 * h) ^ 5 / 120 * d6t
                - (3 * h) ^ 6 / 720 * d7t
                - (3 * h) ^ 7 / 5040 * d8t
                - (3 * h) ^ 8 / 40320 * d9t
                - (3 * h) ^ 9 / 362880 * d10t
                - (3 * h) ^ 10 / 3628800 * d11t
                - (3 * h) ^ 11 / 39916800 * d12t)
    (hL : L = d2 - d0 - (2 * h) * d2t
                - (2 * h) ^ 2 / 2 * d3t
                - (2 * h) ^ 3 / 6 * d4t
                - (2 * h) ^ 4 / 24 * d5t
                - (2 * h) ^ 5 / 120 * d6t
                - (2 * h) ^ 6 / 720 * d7t
                - (2 * h) ^ 7 / 5040 * d8t
                - (2 * h) ^ 8 / 40320 * d9t
                - (2 * h) ^ 9 / 362880 * d10t
                - (2 * h) ^ 10 / 3628800 * d11t
                - (2 * h) ^ 11 / 39916800 * d12t)
    (hM : M = d1 - d0 - h * d2t
                - h ^ 2 / 2 * d3t
                - h ^ 3 / 6 * d4t
                - h ^ 4 / 24 * d5t
                - h ^ 5 / 120 * d6t
                - h ^ 6 / 720 * d7t
                - h ^ 7 / 5040 * d8t
                - h ^ 8 / 40320 * d9t
                - h ^ 9 / 362880 * d10t
                - h ^ 10 / 3628800 * d11t
                - h ^ 11 / 39916800 * d12t) :
    y12 - y11 - h * (                  (4527766399 / 958003200 : ℝ) * d11
                  - (19433810163 / 958003200 : ℝ) * d10
                  + (61633227185 / 958003200 : ℝ) * d9
                  - (135579356757 / 958003200 : ℝ) * d8
                  + (214139355366 / 958003200 : ℝ) * d7
                  - (247741639374 / 958003200 : ℝ) * d6
                  + (211103573298 / 958003200 : ℝ) * d5
                  - (131365867290 / 958003200 : ℝ) * d4
                  + (58189107627 / 958003200 : ℝ) * d3
                  - (17410248271 / 958003200 : ℝ) * d2
                  + (3158642445 / 958003200 : ℝ) * d1
                  - (262747265 / 958003200 : ℝ) * d0)
      = A - B
        - (4527766399 * h / 958003200) * C
        + (19433810163 * h / 958003200) * D
        - (61633227185 * h / 958003200) * E
        + (135579356757 * h / 958003200) * F
        - (214139355366 * h / 958003200) * G
        + (247741639374 * h / 958003200) * H
        - (211103573298 * h / 958003200) * I
        + (131365867290 * h / 958003200) * J
        - (58189107627 * h / 958003200) * K
        + (17410248271 * h / 958003200) * L
        - (3158642445 * h / 958003200) * M := by
  subst hA; subst hB; subst hC; subst hD; subst hE; subst hF; subst hG; subst hH; subst hI; subst hJ; subst hK; subst hL; subst hM
  ring

private lemma ab12_residual_bound_alg_identity (Mb h : ℝ) :
    Mb / 6227020800 * (12 * h) ^ 13
      + Mb / 6227020800 * (11 * h) ^ 13
      + (4527766399 * h / 958003200) * (Mb / 479001600 * (11 * h) ^ 12)
      + (19433810163 * h / 958003200) * (Mb / 479001600 * (10 * h) ^ 12)
      + (61633227185 * h / 958003200) * (Mb / 479001600 * (9 * h) ^ 12)
      + (135579356757 * h / 958003200) * (Mb / 479001600 * (8 * h) ^ 12)
      + (214139355366 * h / 958003200) * (Mb / 479001600 * (7 * h) ^ 12)
      + (247741639374 * h / 958003200) * (Mb / 479001600 * (6 * h) ^ 12)
      + (211103573298 * h / 958003200) * (Mb / 479001600 * (5 * h) ^ 12)
      + (131365867290 * h / 958003200) * (Mb / 479001600 * (4 * h) ^ 12)
      + (58189107627 * h / 958003200) * (Mb / 479001600 * (3 * h) ^ 12)
      + (17410248271 * h / 958003200) * (Mb / 479001600 * (2 * h) ^ 12)
      + (3158642445 * h / 958003200) * (Mb / 479001600 * h ^ 12)
      = (171625746494360048711 / 1059216238080000 : ℝ) * Mb * h ^ 13 := by
  ring

private lemma ab12_residual_triangle_aux
    (A B sC sD sE sF sG sH sI sJ sK sL sM : ℝ) :
    |A - B - sC + sD - sE + sF - sG + sH - sI + sJ - sK + sL - sM| ≤ |A| + |B| + |sC| + |sD| + |sE| + |sF| + |sG| + |sH| + |sI| + |sJ| + |sK| + |sL| + |sM| := by
  have h1 : |A - B - sC + sD - sE + sF - sG + sH - sI + sJ - sK + sL - sM|
      ≤ |A - B - sC + sD - sE + sF - sG + sH - sI + sJ - sK + sL| + |sM| := abs_sub _ _
  have h2 : |A - B - sC + sD - sE + sF - sG + sH - sI + sJ - sK + sL|
      ≤ |A - B - sC + sD - sE + sF - sG + sH - sI + sJ - sK| + |sL| := abs_add_le _ _
  have h3 : |A - B - sC + sD - sE + sF - sG + sH - sI + sJ - sK|
      ≤ |A - B - sC + sD - sE + sF - sG + sH - sI + sJ| + |sK| := abs_sub _ _
  have h4 : |A - B - sC + sD - sE + sF - sG + sH - sI + sJ|
      ≤ |A - B - sC + sD - sE + sF - sG + sH - sI| + |sJ| := abs_add_le _ _
  have h5 : |A - B - sC + sD - sE + sF - sG + sH - sI|
      ≤ |A - B - sC + sD - sE + sF - sG + sH| + |sI| := abs_sub _ _
  have h6 : |A - B - sC + sD - sE + sF - sG + sH|
      ≤ |A - B - sC + sD - sE + sF - sG| + |sH| := abs_add_le _ _
  have h7 : |A - B - sC + sD - sE + sF - sG|
      ≤ |A - B - sC + sD - sE + sF| + |sG| := abs_sub _ _
  have h8 : |A - B - sC + sD - sE + sF|
      ≤ |A - B - sC + sD - sE| + |sF| := abs_add_le _ _
  have h9 : |A - B - sC + sD - sE|
      ≤ |A - B - sC + sD| + |sE| := abs_sub _ _
  have h10 : |A - B - sC + sD|
      ≤ |A - B - sC| + |sD| := abs_add_le _ _
  have h11 : |A - B - sC|
      ≤ |A - B| + |sC| := abs_sub _ _
  have h12 : |A - B|
      ≤ |A| + |B| := abs_sub _ _
  linarith

private lemma ab12_residual_thirteen_term_triangle
    (A B C D E F G H I J K L M h : ℝ) (hh : 0 ≤ h) :
    |A - B - (4527766399 * h / 958003200) * C + (19433810163 * h / 958003200) * D - (61633227185 * h / 958003200) * E + (135579356757 * h / 958003200) * F - (214139355366 * h / 958003200) * G + (247741639374 * h / 958003200) * H - (211103573298 * h / 958003200) * I + (131365867290 * h / 958003200) * J - (58189107627 * h / 958003200) * K + (17410248271 * h / 958003200) * L - (3158642445 * h / 958003200) * M| ≤ |A| + |B| + (4527766399 * h / 958003200) * |C| + (19433810163 * h / 958003200) * |D| + (61633227185 * h / 958003200) * |E| + (135579356757 * h / 958003200) * |F| + (214139355366 * h / 958003200) * |G| + (247741639374 * h / 958003200) * |H| + (211103573298 * h / 958003200) * |I| + (131365867290 * h / 958003200) * |J| + (58189107627 * h / 958003200) * |K| + (17410248271 * h / 958003200) * |L| + (3158642445 * h / 958003200) * |M| := by
  have hcC_nn : 0 ≤ 4527766399 * h / 958003200 := by linarith
  have hcD_nn : 0 ≤ 19433810163 * h / 958003200 := by linarith
  have hcE_nn : 0 ≤ 61633227185 * h / 958003200 := by linarith
  have hcF_nn : 0 ≤ 135579356757 * h / 958003200 := by linarith
  have hcG_nn : 0 ≤ 214139355366 * h / 958003200 := by linarith
  have hcH_nn : 0 ≤ 247741639374 * h / 958003200 := by linarith
  have hcI_nn : 0 ≤ 211103573298 * h / 958003200 := by linarith
  have hcJ_nn : 0 ≤ 131365867290 * h / 958003200 := by linarith
  have hcK_nn : 0 ≤ 58189107627 * h / 958003200 := by linarith
  have hcL_nn : 0 ≤ 17410248271 * h / 958003200 := by linarith
  have hcM_nn : 0 ≤ 3158642445 * h / 958003200 := by linarith
  have habsC : |(4527766399 * h / 958003200) * C| = (4527766399 * h / 958003200) * |C| := by
    rw [abs_mul, abs_of_nonneg hcC_nn]
  have habsD : |(19433810163 * h / 958003200) * D| = (19433810163 * h / 958003200) * |D| := by
    rw [abs_mul, abs_of_nonneg hcD_nn]
  have habsE : |(61633227185 * h / 958003200) * E| = (61633227185 * h / 958003200) * |E| := by
    rw [abs_mul, abs_of_nonneg hcE_nn]
  have habsF : |(135579356757 * h / 958003200) * F| = (135579356757 * h / 958003200) * |F| := by
    rw [abs_mul, abs_of_nonneg hcF_nn]
  have habsG : |(214139355366 * h / 958003200) * G| = (214139355366 * h / 958003200) * |G| := by
    rw [abs_mul, abs_of_nonneg hcG_nn]
  have habsH : |(247741639374 * h / 958003200) * H| = (247741639374 * h / 958003200) * |H| := by
    rw [abs_mul, abs_of_nonneg hcH_nn]
  have habsI : |(211103573298 * h / 958003200) * I| = (211103573298 * h / 958003200) * |I| := by
    rw [abs_mul, abs_of_nonneg hcI_nn]
  have habsJ : |(131365867290 * h / 958003200) * J| = (131365867290 * h / 958003200) * |J| := by
    rw [abs_mul, abs_of_nonneg hcJ_nn]
  have habsK : |(58189107627 * h / 958003200) * K| = (58189107627 * h / 958003200) * |K| := by
    rw [abs_mul, abs_of_nonneg hcK_nn]
  have habsL : |(17410248271 * h / 958003200) * L| = (17410248271 * h / 958003200) * |L| := by
    rw [abs_mul, abs_of_nonneg hcL_nn]
  have habsM : |(3158642445 * h / 958003200) * M| = (3158642445 * h / 958003200) * |M| := by
    rw [abs_mul, abs_of_nonneg hcM_nn]
  have htri := ab12_residual_triangle_aux A B ((4527766399 * h / 958003200) * C) ((19433810163 * h / 958003200) * D) ((61633227185 * h / 958003200) * E) ((135579356757 * h / 958003200) * F) ((214139355366 * h / 958003200) * G) ((247741639374 * h / 958003200) * H) ((211103573298 * h / 958003200) * I) ((131365867290 * h / 958003200) * J) ((58189107627 * h / 958003200) * K) ((17410248271 * h / 958003200) * L) ((3158642445 * h / 958003200) * M)
  rw [habsC, habsD, habsE, habsF, habsG, habsH, habsI, habsJ, habsK, habsL, habsM] at htri
  exact htri

private lemma ab12_residual_combine_aux
    (A B C D E F G H I J K L M Mb h : ℝ) (hh : 0 ≤ h) (hMbnn : 0 ≤ Mb)
    (hA_bd : |A| ≤ Mb / 6227020800 * (12 * h) ^ 13)
    (hB_bd : |B| ≤ Mb / 6227020800 * (11 * h) ^ 13)
    (hC_bd : |C| ≤ Mb / 479001600 * (11 * h) ^ 12)
    (hD_bd : |D| ≤ Mb / 479001600 * (10 * h) ^ 12)
    (hE_bd : |E| ≤ Mb / 479001600 * (9 * h) ^ 12)
    (hF_bd : |F| ≤ Mb / 479001600 * (8 * h) ^ 12)
    (hG_bd : |G| ≤ Mb / 479001600 * (7 * h) ^ 12)
    (hH_bd : |H| ≤ Mb / 479001600 * (6 * h) ^ 12)
    (hI_bd : |I| ≤ Mb / 479001600 * (5 * h) ^ 12)
    (hJ_bd : |J| ≤ Mb / 479001600 * (4 * h) ^ 12)
    (hK_bd : |K| ≤ Mb / 479001600 * (3 * h) ^ 12)
    (hL_bd : |L| ≤ Mb / 479001600 * (2 * h) ^ 12)
    (hM_bd : |M| ≤ Mb / 479001600 * h ^ 12) :
    |A - B - (4527766399 * h / 958003200) * C + (19433810163 * h / 958003200) * D - (61633227185 * h / 958003200) * E + (135579356757 * h / 958003200) * F - (214139355366 * h / 958003200) * G + (247741639374 * h / 958003200) * H - (211103573298 * h / 958003200) * I + (131365867290 * h / 958003200) * J - (58189107627 * h / 958003200) * K + (17410248271 * h / 958003200) * L - (3158642445 * h / 958003200) * M| ≤ 162031 * Mb * h ^ 13 := by
  have htri := ab12_residual_thirteen_term_triangle A B C D E F G H I J K L M h hh
  have hcC_nn : 0 ≤ 4527766399 * h / 958003200 := by linarith
  have hcD_nn : 0 ≤ 19433810163 * h / 958003200 := by linarith
  have hcE_nn : 0 ≤ 61633227185 * h / 958003200 := by linarith
  have hcF_nn : 0 ≤ 135579356757 * h / 958003200 := by linarith
  have hcG_nn : 0 ≤ 214139355366 * h / 958003200 := by linarith
  have hcH_nn : 0 ≤ 247741639374 * h / 958003200 := by linarith
  have hcI_nn : 0 ≤ 211103573298 * h / 958003200 := by linarith
  have hcJ_nn : 0 ≤ 131365867290 * h / 958003200 := by linarith
  have hcK_nn : 0 ≤ 58189107627 * h / 958003200 := by linarith
  have hcL_nn : 0 ≤ 17410248271 * h / 958003200 := by linarith
  have hcM_nn : 0 ≤ 3158642445 * h / 958003200 := by linarith
  have hCbd_s : (4527766399 * h / 958003200) * |C|
      ≤ (4527766399 * h / 958003200) * (Mb / 479001600 * (11 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hC_bd hcC_nn
  have hDbd_s : (19433810163 * h / 958003200) * |D|
      ≤ (19433810163 * h / 958003200) * (Mb / 479001600 * (10 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hD_bd hcD_nn
  have hEbd_s : (61633227185 * h / 958003200) * |E|
      ≤ (61633227185 * h / 958003200) * (Mb / 479001600 * (9 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hE_bd hcE_nn
  have hFbd_s : (135579356757 * h / 958003200) * |F|
      ≤ (135579356757 * h / 958003200) * (Mb / 479001600 * (8 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hF_bd hcF_nn
  have hGbd_s : (214139355366 * h / 958003200) * |G|
      ≤ (214139355366 * h / 958003200) * (Mb / 479001600 * (7 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hG_bd hcG_nn
  have hHbd_s : (247741639374 * h / 958003200) * |H|
      ≤ (247741639374 * h / 958003200) * (Mb / 479001600 * (6 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hH_bd hcH_nn
  have hIbd_s : (211103573298 * h / 958003200) * |I|
      ≤ (211103573298 * h / 958003200) * (Mb / 479001600 * (5 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hI_bd hcI_nn
  have hJbd_s : (131365867290 * h / 958003200) * |J|
      ≤ (131365867290 * h / 958003200) * (Mb / 479001600 * (4 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hJ_bd hcJ_nn
  have hKbd_s : (58189107627 * h / 958003200) * |K|
      ≤ (58189107627 * h / 958003200) * (Mb / 479001600 * (3 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hK_bd hcK_nn
  have hLbd_s : (17410248271 * h / 958003200) * |L|
      ≤ (17410248271 * h / 958003200) * (Mb / 479001600 * (2 * h) ^ 12) :=
    mul_le_mul_of_nonneg_left hL_bd hcL_nn
  have hMbd_s : (3158642445 * h / 958003200) * |M|
      ≤ (3158642445 * h / 958003200) * (Mb / 479001600 * h ^ 12) :=
    mul_le_mul_of_nonneg_left hM_bd hcM_nn
  have hbound_alg := ab12_residual_bound_alg_identity Mb h
  have hh13_nn : 0 ≤ h ^ 13 := by positivity
  have hMbh13_nn : 0 ≤ Mb * h ^ 13 := mul_nonneg hMbnn hh13_nn
  have hslack : (171625746494360048711 / 1059216238080000 : ℝ) * Mb * h ^ 13
      ≤ 162031 * Mb * h ^ 13 := by
    rw [mul_assoc, mul_assoc (162031 : ℝ)]
    have hle : (171625746494360048711 / 1059216238080000 : ℝ) ≤ 162031 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMbh13_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hEbd_s, hFbd_s, hGbd_s, hHbd_s, hIbd_s, hJbd_s, hKbd_s, hLbd_s, hMbd_s]

theorem ab12_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 13 y) {a b Mb t h : ℝ}
    (hbnd : ∀ u ∈ Set.Icc a b, |iteratedDeriv 13 y u| ≤ Mb)
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
    |adamsBashforth12.localTruncationError h t y| ≤ (162031 : ℝ) * Mb * h ^ 13 := by
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
  have h11h : 0 ≤ 11 * h := by linarith
  have hRy11 :=
    y_thirteenth_order_taylor_remainder hy hbnd ht ht11h h11h
  have hRy12 :=
    y_thirteenth_order_taylor_remainder hy hbnd ht ht12h h12h
  have hRyp1 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht9h h9h
  have hRyp10 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht10h h10h
  have hRyp11 :=
    derivY_twelfth_order_taylor_remainder hy hbnd ht ht11h h11h
  rw [ab12_localTruncationError_eq]
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
  clear_value y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t
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
            - (12 * h) ^ 12 / 479001600 * d12t with hA_def
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
            - (11 * h) ^ 12 / 479001600 * d12t with hB_def
  set C := d11 - d0 - (11 * h) * d2t
                - (11 * h) ^ 2 / 2 * d3t
                - (11 * h) ^ 3 / 6 * d4t
                - (11 * h) ^ 4 / 24 * d5t
                - (11 * h) ^ 5 / 120 * d6t
                - (11 * h) ^ 6 / 720 * d7t
                - (11 * h) ^ 7 / 5040 * d8t
                - (11 * h) ^ 8 / 40320 * d9t
                - (11 * h) ^ 9 / 362880 * d10t
                - (11 * h) ^ 10 / 3628800 * d11t
                - (11 * h) ^ 11 / 39916800 * d12t with hC_def
  set D := d10 - d0 - (10 * h) * d2t
                - (10 * h) ^ 2 / 2 * d3t
                - (10 * h) ^ 3 / 6 * d4t
                - (10 * h) ^ 4 / 24 * d5t
                - (10 * h) ^ 5 / 120 * d6t
                - (10 * h) ^ 6 / 720 * d7t
                - (10 * h) ^ 7 / 5040 * d8t
                - (10 * h) ^ 8 / 40320 * d9t
                - (10 * h) ^ 9 / 362880 * d10t
                - (10 * h) ^ 10 / 3628800 * d11t
                - (10 * h) ^ 11 / 39916800 * d12t with hD_def
  set E := d9 - d0 - (9 * h) * d2t
                - (9 * h) ^ 2 / 2 * d3t
                - (9 * h) ^ 3 / 6 * d4t
                - (9 * h) ^ 4 / 24 * d5t
                - (9 * h) ^ 5 / 120 * d6t
                - (9 * h) ^ 6 / 720 * d7t
                - (9 * h) ^ 7 / 5040 * d8t
                - (9 * h) ^ 8 / 40320 * d9t
                - (9 * h) ^ 9 / 362880 * d10t
                - (9 * h) ^ 10 / 3628800 * d11t
                - (9 * h) ^ 11 / 39916800 * d12t with hE_def
  set F := d8 - d0 - (8 * h) * d2t
                - (8 * h) ^ 2 / 2 * d3t
                - (8 * h) ^ 3 / 6 * d4t
                - (8 * h) ^ 4 / 24 * d5t
                - (8 * h) ^ 5 / 120 * d6t
                - (8 * h) ^ 6 / 720 * d7t
                - (8 * h) ^ 7 / 5040 * d8t
                - (8 * h) ^ 8 / 40320 * d9t
                - (8 * h) ^ 9 / 362880 * d10t
                - (8 * h) ^ 10 / 3628800 * d11t
                - (8 * h) ^ 11 / 39916800 * d12t with hF_def
  set G := d7 - d0 - (7 * h) * d2t
                - (7 * h) ^ 2 / 2 * d3t
                - (7 * h) ^ 3 / 6 * d4t
                - (7 * h) ^ 4 / 24 * d5t
                - (7 * h) ^ 5 / 120 * d6t
                - (7 * h) ^ 6 / 720 * d7t
                - (7 * h) ^ 7 / 5040 * d8t
                - (7 * h) ^ 8 / 40320 * d9t
                - (7 * h) ^ 9 / 362880 * d10t
                - (7 * h) ^ 10 / 3628800 * d11t
                - (7 * h) ^ 11 / 39916800 * d12t with hG_def
  set H := d6 - d0 - (6 * h) * d2t
                - (6 * h) ^ 2 / 2 * d3t
                - (6 * h) ^ 3 / 6 * d4t
                - (6 * h) ^ 4 / 24 * d5t
                - (6 * h) ^ 5 / 120 * d6t
                - (6 * h) ^ 6 / 720 * d7t
                - (6 * h) ^ 7 / 5040 * d8t
                - (6 * h) ^ 8 / 40320 * d9t
                - (6 * h) ^ 9 / 362880 * d10t
                - (6 * h) ^ 10 / 3628800 * d11t
                - (6 * h) ^ 11 / 39916800 * d12t with hH_def
  set I := d5 - d0 - (5 * h) * d2t
                - (5 * h) ^ 2 / 2 * d3t
                - (5 * h) ^ 3 / 6 * d4t
                - (5 * h) ^ 4 / 24 * d5t
                - (5 * h) ^ 5 / 120 * d6t
                - (5 * h) ^ 6 / 720 * d7t
                - (5 * h) ^ 7 / 5040 * d8t
                - (5 * h) ^ 8 / 40320 * d9t
                - (5 * h) ^ 9 / 362880 * d10t
                - (5 * h) ^ 10 / 3628800 * d11t
                - (5 * h) ^ 11 / 39916800 * d12t with hI_def
  set J := d4 - d0 - (4 * h) * d2t
                - (4 * h) ^ 2 / 2 * d3t
                - (4 * h) ^ 3 / 6 * d4t
                - (4 * h) ^ 4 / 24 * d5t
                - (4 * h) ^ 5 / 120 * d6t
                - (4 * h) ^ 6 / 720 * d7t
                - (4 * h) ^ 7 / 5040 * d8t
                - (4 * h) ^ 8 / 40320 * d9t
                - (4 * h) ^ 9 / 362880 * d10t
                - (4 * h) ^ 10 / 3628800 * d11t
                - (4 * h) ^ 11 / 39916800 * d12t with hJ_def
  set K := d3 - d0 - (3 * h) * d2t
                - (3 * h) ^ 2 / 2 * d3t
                - (3 * h) ^ 3 / 6 * d4t
                - (3 * h) ^ 4 / 24 * d5t
                - (3 * h) ^ 5 / 120 * d6t
                - (3 * h) ^ 6 / 720 * d7t
                - (3 * h) ^ 7 / 5040 * d8t
                - (3 * h) ^ 8 / 40320 * d9t
                - (3 * h) ^ 9 / 362880 * d10t
                - (3 * h) ^ 10 / 3628800 * d11t
                - (3 * h) ^ 11 / 39916800 * d12t with hK_def
  set L := d2 - d0 - (2 * h) * d2t
                - (2 * h) ^ 2 / 2 * d3t
                - (2 * h) ^ 3 / 6 * d4t
                - (2 * h) ^ 4 / 24 * d5t
                - (2 * h) ^ 5 / 120 * d6t
                - (2 * h) ^ 6 / 720 * d7t
                - (2 * h) ^ 7 / 5040 * d8t
                - (2 * h) ^ 8 / 40320 * d9t
                - (2 * h) ^ 9 / 362880 * d10t
                - (2 * h) ^ 10 / 3628800 * d11t
                - (2 * h) ^ 11 / 39916800 * d12t with hL_def
  set M := d1 - d0 - h * d2t
                - h ^ 2 / 2 * d3t
                - h ^ 3 / 6 * d4t
                - h ^ 4 / 24 * d5t
                - h ^ 5 / 120 * d6t
                - h ^ 6 / 720 * d7t
                - h ^ 7 / 5040 * d8t
                - h ^ 8 / 40320 * d9t
                - h ^ 9 / 362880 * d10t
                - h ^ 10 / 3628800 * d11t
                - h ^ 11 / 39916800 * d12t with hM_def
  clear_value A B C D E F G H I J K L M
  have hLTE_eq :=
    ab12_residual_alg_identity y0 y11 y12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d2t d3t d4t d5t d6t d7t d8t d9t d10t d11t d12t h A B C D E F G H I J K L M hA_def hB_def hC_def hD_def hE_def hF_def hG_def hH_def hI_def hJ_def hK_def hL_def hM_def
  rw [hLTE_eq]
  have hA_bd : |A| ≤ Mb / 6227020800 * (12 * h) ^ 13 := hRy12
  have hB_bd : |B| ≤ Mb / 6227020800 * (11 * h) ^ 13 := hRy11
  have hC_bd : |C| ≤ Mb / 479001600 * (11 * h) ^ 12 := hRyp11
  have hD_bd : |D| ≤ Mb / 479001600 * (10 * h) ^ 12 := hRyp10
  have hE_bd : |E| ≤ Mb / 479001600 * (9 * h) ^ 12 := hRyp9
  have hF_bd : |F| ≤ Mb / 479001600 * (8 * h) ^ 12 := hRyp8
  have hG_bd : |G| ≤ Mb / 479001600 * (7 * h) ^ 12 := hRyp7
  have hH_bd : |H| ≤ Mb / 479001600 * (6 * h) ^ 12 := hRyp6
  have hI_bd : |I| ≤ Mb / 479001600 * (5 * h) ^ 12 := hRyp5
  have hJ_bd : |J| ≤ Mb / 479001600 * (4 * h) ^ 12 := hRyp4
  have hK_bd : |K| ≤ Mb / 479001600 * (3 * h) ^ 12 := hRyp3
  have hL_bd : |L| ≤ Mb / 479001600 * (2 * h) ^ 12 := hRyp2
  have hM_bd : |M| ≤ Mb / 479001600 * h ^ 12 := hRyp1
  have hMbnn : 0 ≤ Mb := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact ab12_residual_combine_aux A B C D E F G H I J K L M Mb h hh hMbnn
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hH_bd hI_bd hJ_bd hK_bd hL_bd hM_bd

theorem ab12_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 13 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 12) * h ≤ T →
        |adamsBashforth12.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 13 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_thirteen_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(162031 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 12) * h := by
        have hcoef : (n : ℝ) ≤ (n : ℝ) + 12 := by norm_num
        exact mul_le_mul_of_nonneg_right hcoef hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 1 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 9 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht10h_mem : t + 10 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 10 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht11h_mem : t + 11 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 11 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  have ht12h_mem : t + 12 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 12 * h ≤ ((n : ℝ) + 12) * h := by
      nlinarith [hh.le]
    linarith
  exact ab12_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem ht10h_mem ht11h_mem ht12h_mem hh.le

/-! ### Generic AB bridge and headline theorem -/

/-- Bridge: the AB12 scalar iteration is the generic AB iteration at `s = 12`. -/
lemma ab12Iter_eq_abIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ : ℝ)
    (n : ℕ) :
    ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ n
      = abIter 12 ab12GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁] n := by
  rfl

/-- Final AB12 global error bound on `[t₀, t₀ + T]`. -/
theorem ab12_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 13 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ →
      |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      |y₃ - y (t₀ + 3 * h)| ≤ ε₀ →
      |y₄ - y (t₀ + 4 * h)| ≤ ε₀ →
      |y₅ - y (t₀ + 5 * h)| ≤ ε₀ →
      |y₆ - y (t₀ + 6 * h)| ≤ ε₀ →
      |y₇ - y (t₀ + 7 * h)| ≤ ε₀ →
      |y₈ - y (t₀ + 8 * h)| ≤ ε₀ →
      |y₉ - y (t₀ + 9 * h)| ≤ ε₀ →
      |y₁₀ - y (t₀ + 10 * h)| ≤ ε₀ →
      |y₁₁ - y (t₀ + 11 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 11) * h ≤ T →
      |ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N
          - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((443892 / 385) * L * T) * ε₀ + K * h ^ 12 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab12_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((443892 / 385) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd he10_bd he11_bd N hNh
  set α : Fin 12 → ℝ := ab12GenericCoeff with hα_def
  set y₀_non : Fin 12 → ℝ := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁]
    with hy_non_def
  have hs : (1 : ℕ) ≤ 12 := by norm_num
  haveI : Nonempty (Fin 12) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIter 12 α h f t₀ y₀_non 0 = y₀ := by
    unfold abIter
    simp [hy_non_def]
  have hiter1 : abIter 12 α h f t₀ y₀_non 1 = y₁ := by
    unfold abIter
    simp [hy_non_def]
  have hiter2 : abIter 12 α h f t₀ y₀_non 2 = y₂ := by
    unfold abIter
    simp [hy_non_def]
  have hiter3 : abIter 12 α h f t₀ y₀_non 3 = y₃ := by
    unfold abIter
    simp [hy_non_def]
  have hiter4 : abIter 12 α h f t₀ y₀_non 4 = y₄ := by
    unfold abIter
    simp [hy_non_def]
  have hiter5 : abIter 12 α h f t₀ y₀_non 5 = y₅ := by
    unfold abIter
    simp [hy_non_def]
  have hiter6 : abIter 12 α h f t₀ y₀_non 6 = y₆ := by
    unfold abIter
    simp [hy_non_def]
  have hiter7 : abIter 12 α h f t₀ y₀_non 7 = y₇ := by
    unfold abIter
    simp [hy_non_def]
  have hiter8 : abIter 12 α h f t₀ y₀_non 8 = y₈ := by
    unfold abIter
    simp [hy_non_def]
  have hiter9 : abIter 12 α h f t₀ y₀_non 9 = y₉ := by
    unfold abIter
    simp [hy_non_def]
  have hiter10 : abIter 12 α h f t₀ y₀_non 10 = y₁₀ := by
    unfold abIter
    simp [hy_non_def]
  have hiter11 : abIter 12 α h f t₀ y₀_non 11 = y₁₁ := by
    unfold abIter
    simp [hy_non_def]
  have hstart : abErrWindow hs α h f t₀ y₀_non y 0 ≤ ε₀ := by
    unfold abErrWindow
    apply Finset.sup'_le
    intro j _
    show abErr 12 α h f t₀ y₀_non y (0 + (j : ℕ)) ≤ ε₀
    unfold abErr
    fin_cases j
    · show |abIter 12 α h f t₀ y₀_non 0
          - y (t₀ + ((0 + ((((0 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter0]
      have hval : (((0 : Fin 12)) : ℕ) = 0 := rfl
      have hcast : ((0 + ((((0 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he0_bd
    · show |abIter 12 α h f t₀ y₀_non 1
          - y (t₀ + ((0 + ((((1 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter1]
      have hval : (((1 : Fin 12)) : ℕ) = 1 := rfl
      have hcast : ((0 + ((((1 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he1_bd
    · show |abIter 12 α h f t₀ y₀_non 2
          - y (t₀ + ((0 + ((((2 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter2]
      have hval : (((2 : Fin 12)) : ℕ) = 2 := rfl
      have hcast : ((0 + ((((2 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he2_bd
    · show |abIter 12 α h f t₀ y₀_non 3
          - y (t₀ + ((0 + ((((3 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter3]
      have hval : (((3 : Fin 12)) : ℕ) = 3 := rfl
      have hcast : ((0 + ((((3 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he3_bd
    · show |abIter 12 α h f t₀ y₀_non 4
          - y (t₀ + ((0 + ((((4 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter4]
      have hval : (((4 : Fin 12)) : ℕ) = 4 := rfl
      have hcast : ((0 + ((((4 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he4_bd
    · show |abIter 12 α h f t₀ y₀_non 5
          - y (t₀ + ((0 + ((((5 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter5]
      have hval : (((5 : Fin 12)) : ℕ) = 5 := rfl
      have hcast : ((0 + ((((5 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he5_bd
    · show |abIter 12 α h f t₀ y₀_non 6
          - y (t₀ + ((0 + ((((6 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter6]
      have hval : (((6 : Fin 12)) : ℕ) = 6 := rfl
      have hcast : ((0 + ((((6 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 6 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he6_bd
    · show |abIter 12 α h f t₀ y₀_non 7
          - y (t₀ + ((0 + ((((7 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter7]
      have hval : (((7 : Fin 12)) : ℕ) = 7 := rfl
      have hcast : ((0 + ((((7 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 7 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he7_bd
    · show |abIter 12 α h f t₀ y₀_non 8
          - y (t₀ + ((0 + ((((8 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter8]
      have hval : (((8 : Fin 12)) : ℕ) = 8 := rfl
      have hcast : ((0 + ((((8 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 8 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he8_bd
    · show |abIter 12 α h f t₀ y₀_non 9
          - y (t₀ + ((0 + ((((9 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter9]
      have hval : (((9 : Fin 12)) : ℕ) = 9 := rfl
      have hcast : ((0 + ((((9 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 9 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he9_bd
    · show |abIter 12 α h f t₀ y₀_non 10
          - y (t₀ + ((0 + ((((10 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter10]
      have hval : (((10 : Fin 12)) : ℕ) = 10 := rfl
      have hcast : ((0 + ((((10 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 10 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he10_bd
    · show |abIter 12 α h f t₀ y₀_non 11
          - y (t₀ + ((0 + ((((11 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter11]
      have hval : (((11 : Fin 12)) : ℕ) = 11 := rfl
      have hcast : ((0 + ((((11 : Fin 12)) : ℕ) : ℕ) : ℕ) : ℝ) = 11 := by
        rw [hval]; norm_num
      rw [hcast]
      simpa using he11_bd
  have hres_gen : ∀ n : ℕ, n < N →
      |abResidual 12 α h y t₀ n| ≤ C * h ^ (12 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 12 ≤ (N : ℝ) + 11 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn12_le : ((n : ℝ) + 12) * h ≤ T := by
      have hmul : ((n : ℝ) + 12) * h ≤ ((N : ℝ) + 11) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn12_le
    rw [hα_def, ← ab12Residual_eq_abResidual h y t₀ n]
    have hpow : C * h ^ (12 + 1) = C * h ^ 13 := by norm_num
    rwa [hpow]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 11) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 11 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic (p := 12) hs α hh.le hL hC_nn hf t₀
      y₀_non y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 12 α L = (443892 / 385) * L from by
    rw [hα_def]; exact abLip_ab12GenericCoeff L] at hgeneric
  have hwindow_ge : abErr 12 α h f t₀ y₀_non y N
      ≤ abErrWindow hs α h f t₀ y₀_non y N := by
    show abErr 12 α h f t₀ y₀_non y (N + ((⟨0, hs⟩ : Fin 12) : ℕ))
        ≤ abErrWindow hs α h f t₀ y₀_non y N
    unfold abErrWindow
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 12 => abErr 12 α h f t₀ y₀_non y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIter 12 α h f t₀ y₀_non N
        = ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N := by
    rw [hα_def, hy_non_def]
    rfl
  have habsErr :
      abErr 12 α h f t₀ y₀_non y N
        = |ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N
            - y (t₀ + (N : ℝ) * h)| := by
    show |abIter 12 α h f t₀ y₀_non N - y (t₀ + (N : ℝ) * h)|
        = |ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N
            - y (t₀ + (N : ℝ) * h)|
    rw [hbridge]
  show |ab12Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ N
        - y (t₀ + (N : ℝ) * h)|
      ≤ Real.exp ((443892 / 385) * L * T) * ε₀
        + T * Real.exp ((443892 / 385) * L * T) * C * h ^ 12
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
