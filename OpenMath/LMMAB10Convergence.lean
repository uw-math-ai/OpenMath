import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAM8Convergence

/-! ## Adams–Bashforth 10-step Scalar Convergence Chain (Iserles §1.2)

Order-10 explicit 10-step LMM convergence scaffold. Mirrors the AB9 chain
in `OpenMath.LMMAB9Convergence` at the next order. This scalar half takes
ten starting samples and combines ten prior `f` evaluations. The
effective max-window Lipschitz constant is `(172570/567) · L`
(`= sum |β_k|`), the residual is `O(h^11)` and the headline global error
bound is `O(ε₀ + h^10)`.

Adds three public eleventh-order Taylor helpers reusable by AM9 / AB10-vector
(`iteratedDeriv_eleven_bounded_on_Icc`, `y_eleventh_order_taylor_remainder`,
`derivY_tenth_order_taylor_remainder`). -/

namespace LMM

/-! ### Eleventh-order Taylor helpers (public, reusable for AM9 / AB10-vector) -/

/-- A `C^11` function has its eleventh derivative bounded on every compact
interval `[a, b]`. -/
theorem iteratedDeriv_eleven_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 11 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 11 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 11 y) :=
    hy.continuous_iteratedDeriv 11 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise eleventh-order Taylor (Lagrange) remainder bound: if `y` is
`C^11` and `|iteratedDeriv 11 y| ≤ M` on `[a, b]`, then for `t, t + r ∈
[a, b]` with `r ≥ 0`,
`|y(t+r) - y(t) - r·y'(t) - r²/2·y''(t) - … - r¹⁰/10!·y⁽¹⁰⁾(t)|
  ≤ M/11! · r¹¹ = M/39916800 · r¹¹`. -/
theorem y_eleventh_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 11 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 11 y t| ≤ M)
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
        - r ^ 9 / 362880 * iteratedDeriv 9 y t
        - r ^ 10 / 3628800 * iteratedDeriv 10 y t|
      ≤ M / 39916800 * r ^ 11 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 10 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 11 y ξ * r ^ 11 / 39916800 := by
    have hcdo : ContDiffOn ℝ 11 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 10) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 11 = r ^ 11 := by ring
    have hfact : (((10 + 1 : ℕ).factorial : ℝ)) = 39916800 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval y 10 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t + r ^ 2 / 2 * iteratedDeriv 2 y t
              + r ^ 3 / 6 * iteratedDeriv 3 y t
              + r ^ 4 / 24 * iteratedDeriv 4 y t
              + r ^ 5 / 120 * iteratedDeriv 5 y t
              + r ^ 6 / 720 * iteratedDeriv 6 y t
              + r ^ 7 / 5040 * iteratedDeriv 7 y t
              + r ^ 8 / 40320 * iteratedDeriv 8 y t
              + r ^ 9 / 362880 * iteratedDeriv 9 y t
              + r ^ 10 / 3628800 * iteratedDeriv 10 y t := by
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
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 11 y ξ| ≤ M := hbnd ξ hξ_in
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
          - r ^ 10 / 3628800 * iteratedDeriv 10 y t
        = iteratedDeriv 11 y ξ * r ^ 11 / 39916800 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 11 y ξ * r ^ 11 / 39916800
      = (iteratedDeriv 11 y ξ) * (r ^ 11 / 39916800) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 11 / 39916800)]
  calc |iteratedDeriv 11 y ξ| * (r ^ 11 / 39916800)
      ≤ M * (r ^ 11 / 39916800) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 39916800 * r ^ 11 := by ring

/-- Pointwise tenth-order Taylor (Lagrange) remainder bound for the
derivative: if `y` is `C^11` and `|iteratedDeriv 11 y| ≤ M` on `[a, b]`,
then for `t, t + r ∈ [a, b]` with `r ≥ 0`,
`|y'(t+r) - y'(t) - r·y''(t) - … - r⁹/9!·y⁽¹⁰⁾(t)|
  ≤ M/10! · r¹⁰ = M/3628800 · r¹⁰`. -/
theorem derivY_tenth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 11 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 11 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t
        - r ^ 3 / 6 * iteratedDeriv 4 y t
        - r ^ 4 / 24 * iteratedDeriv 5 y t
        - r ^ 5 / 120 * iteratedDeriv 6 y t
        - r ^ 6 / 720 * iteratedDeriv 7 y t
        - r ^ 7 / 5040 * iteratedDeriv 8 y t
        - r ^ 8 / 40320 * iteratedDeriv 9 y t
        - r ^ 9 / 362880 * iteratedDeriv 10 y t|
      ≤ M / 3628800 * r ^ 10 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  have hdy : ContDiff ℝ 10 (deriv y) := hy.deriv'
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r)
          - taylorWithinEval (deriv y) 9 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 10 (deriv y) ξ * r ^ 10 / 3628800 := by
    have hcdo : ContDiffOn ℝ 10 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 9) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 10 = r ^ 10 := by ring
    have hfact : (((9 + 1 : ℕ).factorial : ℝ)) = 3628800 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  have h_taylor :
      taylorWithinEval (deriv y) 9 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t
              + r ^ 2 / 2 * iteratedDeriv 3 y t
              + r ^ 3 / 6 * iteratedDeriv 4 y t
              + r ^ 4 / 24 * iteratedDeriv 5 y t
              + r ^ 5 / 120 * iteratedDeriv 6 y t
              + r ^ 6 / 720 * iteratedDeriv 7 y t
              + r ^ 7 / 5040 * iteratedDeriv 8 y t
              + r ^ 8 / 40320 * iteratedDeriv 9 y t
              + r ^ 9 / 362880 * iteratedDeriv 10 y t := by
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
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    simp only [smul_eq_mul, Nat.cast_ofNat, Nat.cast_succ,
      pow_zero, pow_one, mul_one, zero_add, Nat.factorial]
    ring
  have hidd_eq : iteratedDeriv 10 (deriv y) = iteratedDeriv 11 y := by
    have : iteratedDeriv 11 y = iteratedDeriv 10 (deriv y) :=
      iteratedDeriv_succ' (n := 10) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 11 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
          - r ^ 2 / 2 * iteratedDeriv 3 y t
          - r ^ 3 / 6 * iteratedDeriv 4 y t
          - r ^ 4 / 24 * iteratedDeriv 5 y t
          - r ^ 5 / 120 * iteratedDeriv 6 y t
          - r ^ 6 / 720 * iteratedDeriv 7 y t
          - r ^ 7 / 5040 * iteratedDeriv 8 y t
          - r ^ 8 / 40320 * iteratedDeriv 9 y t
          - r ^ 9 / 362880 * iteratedDeriv 10 y t
        = iteratedDeriv 11 y ξ * r ^ 10 / 3628800 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 11 y ξ * r ^ 10 / 3628800
      = (iteratedDeriv 11 y ξ) * (r ^ 10 / 3628800) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 10 / 3628800)]
  calc |iteratedDeriv 11 y ξ| * (r ^ 10 / 3628800)
      ≤ M * (r ^ 10 / 3628800) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 3628800 * r ^ 10 := by ring

/-! ### AB10 iteration -/

/-- AB10 iteration with ten starting samples `y₀, y₁, …, y₉`:
`y_{n+10} = y_{n+9} + h · ((30277247/7257600) · f_{n+9}
  − (104995189/7257600) · f_{n+8} + (265932680/7257600) · f_{n+7}
  − (454661776/7257600) · f_{n+6} + (538363838/7257600) · f_{n+5}
  − (444772162/7257600) · f_{n+4} + (252618224/7257600) · f_{n+3}
  − (94307320/7257600) · f_{n+2} + (20884811/7257600) · f_{n+1}
  − (2082753/7257600) · f_n)`. -/
noncomputable def ab10Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | 6 => y₆
  | 7 => y₇
  | 8 => y₈
  | 9 => y₉
  | n + 10 =>
      ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9)
        + h * (30277247 / 7257600 * f (t₀ + ((n : ℝ) + 9) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9))
              - 104995189 / 7257600 * f (t₀ + ((n : ℝ) + 8) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8))
              + 265932680 / 7257600 * f (t₀ + ((n : ℝ) + 7) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7))
              - 454661776 / 7257600 * f (t₀ + ((n : ℝ) + 6) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6))
              + 538363838 / 7257600 * f (t₀ + ((n : ℝ) + 5) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5))
              - 444772162 / 7257600 * f (t₀ + ((n : ℝ) + 4) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4))
              + 252618224 / 7257600 * f (t₀ + ((n : ℝ) + 3) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3))
              - 94307320 / 7257600 * f (t₀ + ((n : ℝ) + 2) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2))
              + 20884811 / 7257600 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1))
              - 2082753 / 7257600 * f (t₀ + (n : ℝ) * h)
                (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n))

@[simp] lemma ab10Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 0 = y₀ := rfl

@[simp] lemma ab10Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 1 = y₁ := rfl

@[simp] lemma ab10Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 2 = y₂ := rfl

@[simp] lemma ab10Iter_three
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 3 = y₃ := rfl

@[simp] lemma ab10Iter_four
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 4 = y₄ := rfl

@[simp] lemma ab10Iter_five
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 5 = y₅ := rfl

@[simp] lemma ab10Iter_six
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 6 = y₆ := rfl

@[simp] lemma ab10Iter_seven
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 7 = y₇ := rfl

@[simp] lemma ab10Iter_eight
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 8 = y₈ := rfl

@[simp] lemma ab10Iter_nine
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 9 = y₉ := rfl

lemma ab10Iter_succ_ten
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) (n : ℕ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10)
      = ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9)
          + h * (30277247 / 7257600 * f (t₀ + ((n : ℝ) + 9) * h)
                  (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9))
                - 104995189 / 7257600 * f (t₀ + ((n : ℝ) + 8) * h)
                    (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8))
                + 265932680 / 7257600 * f (t₀ + ((n : ℝ) + 7) * h)
                    (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7))
                - 454661776 / 7257600 * f (t₀ + ((n : ℝ) + 6) * h)
                    (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6))
                + 538363838 / 7257600 * f (t₀ + ((n : ℝ) + 5) * h)
                    (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5))
                - 444772162 / 7257600 * f (t₀ + ((n : ℝ) + 4) * h)
                    (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4))
                + 252618224 / 7257600 * f (t₀ + ((n : ℝ) + 3) * h)
                    (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3))
                - 94307320 / 7257600 * f (t₀ + ((n : ℝ) + 2) * h)
                    (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2))
                + 20884811 / 7257600 * f (t₀ + ((n : ℝ) + 1) * h)
                    (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1))
                - 2082753 / 7257600 * f (t₀ + (n : ℝ) * h)
                    (ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n)) := rfl

/-- AB10 local truncation operator reduces to the textbook 10-step residual. -/
theorem ab10_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth10.localTruncationError h t y
      = y (t + 10 * h) - y (t + 9 * h)
          - h * (30277247 / 7257600 * deriv y (t + 9 * h)
                  - 104995189 / 7257600 * deriv y (t + 8 * h)
                  + 265932680 / 7257600 * deriv y (t + 7 * h)
                  - 454661776 / 7257600 * deriv y (t + 6 * h)
                  + 538363838 / 7257600 * deriv y (t + 5 * h)
                  - 444772162 / 7257600 * deriv y (t + 4 * h)
                  + 252618224 / 7257600 * deriv y (t + 3 * h)
                  - 94307320 / 7257600 * deriv y (t + 2 * h)
                  + 20884811 / 7257600 * deriv y (t + h)
                  - 2082753 / 7257600 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth10, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  norm_num
  ring

/-- Algebraic decomposition of the AB10 global-error increment. Pure
`ring` identity isolated to keep the kernel cost of
`ab10_one_step_lipschitz` manageable. -/
private lemma ab10_step_alg_decomp
    (h : ℝ) (yn9 zn9 zn10 τ : ℝ)
    (a9 a8 a7 a6 a5 a4 a3 a2 a1 a0 : ℝ)
    (next : ℝ)
    (hstep : next = yn9 + h * (30277247 / 7257600 * a9
                    - 104995189 / 7257600 * a8
                    + 265932680 / 7257600 * a7
                    - 454661776 / 7257600 * a6
                    + 538363838 / 7257600 * a5
                    - 444772162 / 7257600 * a4
                    + 252618224 / 7257600 * a3
                    - 94307320 / 7257600 * a2
                    + 20884811 / 7257600 * a1
                    - 2082753 / 7257600 * a0))
    (b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 : ℝ)
    (hτ_eq : τ = zn10 - zn9 - h * (30277247 / 7257600 * b9
                    - 104995189 / 7257600 * b8
                    + 265932680 / 7257600 * b7
                    - 454661776 / 7257600 * b6
                    + 538363838 / 7257600 * b5
                    - 444772162 / 7257600 * b4
                    + 252618224 / 7257600 * b3
                    - 94307320 / 7257600 * b2
                    + 20884811 / 7257600 * b1
                    - 2082753 / 7257600 * b0)) :
    next - zn10
      = (yn9 - zn9)
        + (30277247 / 7257600) * h * (a9 - b9)
        - (104995189 / 7257600) * h * (a8 - b8)
        + (265932680 / 7257600) * h * (a7 - b7)
        - (454661776 / 7257600) * h * (a6 - b6)
        + (538363838 / 7257600) * h * (a5 - b5)
        - (444772162 / 7257600) * h * (a4 - b4)
        + (252618224 / 7257600) * h * (a3 - b3)
        - (94307320 / 7257600) * h * (a2 - b2)
        + (20884811 / 7257600) * h * (a1 - b1)
        - (2082753 / 7257600) * h * (a0 - b0)
        - τ := by
  rw [hstep, hτ_eq]; ring

/-- Auxiliary triangle inequality for eleven abstract terms, matching the
sign pattern `A + B - C + D - E + F - G + H - I + J - K` of the AB10
one-step Lipschitz decomposition. Extracted to keep the kernel cost of
`ab10_one_step_lipschitz` manageable. -/
private lemma ab10_step_lipschitz_triangle
    (A B sC sD sE sF sG sH sI sJ sK : ℝ) :
    |A + B - sC + sD - sE + sF - sG + sH - sI + sJ - sK|
      ≤ |A| + |B| + |sC| + |sD| + |sE| + |sF| + |sG| + |sH|
          + |sI| + |sJ| + |sK| := by
  have h1 : |A + B - sC + sD - sE + sF - sG + sH - sI + sJ - sK|
      ≤ |A + B - sC + sD - sE + sF - sG + sH - sI + sJ| + |sK| := abs_sub _ _
  have h2 : |A + B - sC + sD - sE + sF - sG + sH - sI + sJ|
      ≤ |A + B - sC + sD - sE + sF - sG + sH - sI| + |sJ| := abs_add_le _ _
  have h3 : |A + B - sC + sD - sE + sF - sG + sH - sI|
      ≤ |A + B - sC + sD - sE + sF - sG + sH| + |sI| := abs_sub _ _
  have h4 : |A + B - sC + sD - sE + sF - sG + sH|
      ≤ |A + B - sC + sD - sE + sF - sG| + |sH| := abs_add_le _ _
  have h5 : |A + B - sC + sD - sE + sF - sG|
      ≤ |A + B - sC + sD - sE + sF| + |sG| := abs_sub _ _
  have h6 : |A + B - sC + sD - sE + sF|
      ≤ |A + B - sC + sD - sE| + |sF| := abs_add_le _ _
  have h7 : |A + B - sC + sD - sE|
      ≤ |A + B - sC + sD| + |sE| := abs_sub _ _
  have h8 : |A + B - sC + sD| ≤ |A + B - sC| + |sD| := abs_add_le _ _
  have h9 : |A + B - sC| ≤ |A + B| + |sC| := abs_sub _ _
  have h10 : |A + B| ≤ |A| + |B| := abs_add_le _ _
  linarith

/-- One-step AB10 Lipschitz step: a single linearised increment of the
global error from steps `n, n+1, …, n+9` to `n+10`, with ten Lipschitz
contributions and additive `|τ_n|`. -/
theorem ab10_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)|
      ≤ |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)|
        + (30277247 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9)
                - y (t₀ + ((n : ℝ) + 9) * h)|
        + (104995189 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8)
                - y (t₀ + ((n : ℝ) + 8) * h)|
        + (265932680 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7)
                - y (t₀ + ((n : ℝ) + 7) * h)|
        + (454661776 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6)
                - y (t₀ + ((n : ℝ) + 6) * h)|
        + (538363838 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)|
        + (444772162 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)|
        + (252618224 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)|
        + (94307320 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|
        + (20884811 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
        + (2082753 / 7257600) * h * L
            * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n - y (t₀ + (n : ℝ) * h)|
        + |adamsBashforth10.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n with hyn_def
  set yn1 : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1) with hyn1_def
  set yn2 : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2) with hyn2_def
  set yn3 : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3) with hyn3_def
  set yn4 : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4) with hyn4_def
  set yn5 : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5) with hyn5_def
  set yn6 : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6) with hyn6_def
  set yn7 : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7) with hyn7_def
  set yn8 : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8) with hyn8_def
  set yn9 : ℝ := ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9) with hyn9_def
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
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set zn6 : ℝ := y tn6 with hzn6_def
  set zn7 : ℝ := y tn7 with hzn7_def
  set zn8 : ℝ := y tn8 with hzn8_def
  set zn9 : ℝ := y tn9 with hzn9_def
  set zn10 : ℝ := y tn10 with hzn10_def
  set τ : ℝ := adamsBashforth10.localTruncationError h tn y with hτ_def
  -- AB10 step formula.
  have hstep : ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10)
      = yn9 + h * (30277247 / 7257600 * f tn9 yn9
                    - 104995189 / 7257600 * f tn8 yn8
                    + 265932680 / 7257600 * f tn7 yn7
                    - 454661776 / 7257600 * f tn6 yn6
                    + 538363838 / 7257600 * f tn5 yn5
                    - 444772162 / 7257600 * f tn4 yn4
                    + 252618224 / 7257600 * f tn3 yn3
                    - 94307320 / 7257600 * f tn2 yn2
                    + 20884811 / 7257600 * f tn1 yn1
                    - 2082753 / 7257600 * f tn yn) := by
    show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10) = _
    rw [ab10Iter_succ_ten]
  -- Time arithmetic.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  have htn_6h : tn + 6 * h = tn6 := by simp [htn_def, htn6_def]; ring
  have htn_7h : tn + 7 * h = tn7 := by simp [htn_def, htn7_def]; ring
  have htn_8h : tn + 8 * h = tn8 := by simp [htn_def, htn8_def]; ring
  have htn_9h : tn + 9 * h = tn9 := by simp [htn_def, htn9_def]; ring
  have htn_10h : tn + 10 * h = tn10 := by simp [htn_def, htn10_def]; ring
  -- LTE residual at `tn`, expressed via `f` along the trajectory.
  have hτ_eq : τ = zn10 - zn9
        - h * (30277247 / 7257600 * f tn9 zn9 - 104995189 / 7257600 * f tn8 zn8
              + 265932680 / 7257600 * f tn7 zn7 - 454661776 / 7257600 * f tn6 zn6
              + 538363838 / 7257600 * f tn5 zn5 - 444772162 / 7257600 * f tn4 zn4
              + 252618224 / 7257600 * f tn3 zn3 - 94307320 / 7257600 * f tn2 zn2
              + 20884811 / 7257600 * f tn1 zn1 - 2082753 / 7257600 * f tn zn) := by
    show adamsBashforth10.localTruncationError h tn y = _
    rw [ab10_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h, htn_5h,
      htn_6h, htn_7h, htn_8h, htn_9h, htn_10h, hyf tn9, hyf tn8, hyf tn7, hyf tn6,
      hyf tn5, hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the global error increment.
  have halg : ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10) - zn10
      = (yn9 - zn9)
        + (30277247 / 7257600) * h * (f tn9 yn9 - f tn9 zn9)
        - (104995189 / 7257600) * h * (f tn8 yn8 - f tn8 zn8)
        + (265932680 / 7257600) * h * (f tn7 yn7 - f tn7 zn7)
        - (454661776 / 7257600) * h * (f tn6 yn6 - f tn6 zn6)
        + (538363838 / 7257600) * h * (f tn5 yn5 - f tn5 zn5)
        - (444772162 / 7257600) * h * (f tn4 yn4 - f tn4 zn4)
        + (252618224 / 7257600) * h * (f tn3 yn3 - f tn3 zn3)
        - (94307320 / 7257600) * h * (f tn2 yn2 - f tn2 zn2)
        + (20884811 / 7257600) * h * (f tn1 yn1 - f tn1 zn1)
        - (2082753 / 7257600) * h * (f tn yn - f tn zn)
        - τ :=
    ab10_step_alg_decomp h yn9 zn9 zn10 τ
      (f tn9 yn9) (f tn8 yn8) (f tn7 yn7) (f tn6 yn6) (f tn5 yn5) (f tn4 yn4)
      (f tn3 yn3) (f tn2 yn2) (f tn1 yn1) (f tn yn) _ hstep
      (f tn9 zn9) (f tn8 zn8) (f tn7 zn7) (f tn6 zn6) (f tn5 zn5) (f tn4 zn4)
      (f tn3 zn3) (f tn2 zn2) (f tn1 zn1) (f tn zn) hτ_eq
  clear_value yn yn1 yn2 yn3 yn4 yn5 yn6 yn7 yn8 yn9
    tn tn1 tn2 tn3 tn4 tn5 tn6 tn7 tn8 tn9 tn10
    zn zn1 zn2 zn3 zn4 zn5 zn6 zn7 zn8 zn9 zn10 τ
  -- Lipschitz bounds.
  have hLip9 : |f tn9 yn9 - f tn9 zn9| ≤ L * |yn9 - zn9| := hf tn9 yn9 zn9
  have hLip8 : |f tn8 yn8 - f tn8 zn8| ≤ L * |yn8 - zn8| := hf tn8 yn8 zn8
  have hLip7 : |f tn7 yn7 - f tn7 zn7| ≤ L * |yn7 - zn7| := hf tn7 yn7 zn7
  have hLip6 : |f tn6 yn6 - f tn6 zn6| ≤ L * |yn6 - zn6| := hf tn6 yn6 zn6
  have hLip5 : |f tn5 yn5 - f tn5 zn5| ≤ L * |yn5 - zn5| := hf tn5 yn5 zn5
  have hLip4 : |f tn4 yn4 - f tn4 zn4| ≤ L * |yn4 - zn4| := hf tn4 yn4 zn4
  have hLip3 : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| := hf tn3 yn3 zn3
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| := hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| := hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  have c9_nn : 0 ≤ (30277247 / 7257600) * h := by linarith
  have c8_nn : 0 ≤ (104995189 / 7257600) * h := by linarith
  have c7_nn : 0 ≤ (265932680 / 7257600) * h := by linarith
  have c6_nn : 0 ≤ (454661776 / 7257600) * h := by linarith
  have c5_nn : 0 ≤ (538363838 / 7257600) * h := by linarith
  have c4_nn : 0 ≤ (444772162 / 7257600) * h := by linarith
  have c3_nn : 0 ≤ (252618224 / 7257600) * h := by linarith
  have c2_nn : 0 ≤ (94307320 / 7257600) * h := by linarith
  have c1_nn : 0 ≤ (20884811 / 7257600) * h := by linarith
  have c0_nn : 0 ≤ (2082753 / 7257600) * h := by linarith
  have h9_abs : |(30277247 / 7257600) * h * (f tn9 yn9 - f tn9 zn9)|
      ≤ (30277247 / 7257600) * h * L * |yn9 - zn9| := by
    rw [abs_mul, abs_of_nonneg c9_nn]
    calc (30277247 / 7257600) * h * |f tn9 yn9 - f tn9 zn9|
        ≤ (30277247 / 7257600) * h * (L * |yn9 - zn9|) :=
          mul_le_mul_of_nonneg_left hLip9 c9_nn
      _ = (30277247 / 7257600) * h * L * |yn9 - zn9| := by ring
  have h8_abs : |(104995189 / 7257600) * h * (f tn8 yn8 - f tn8 zn8)|
      ≤ (104995189 / 7257600) * h * L * |yn8 - zn8| := by
    rw [abs_mul, abs_of_nonneg c8_nn]
    calc (104995189 / 7257600) * h * |f tn8 yn8 - f tn8 zn8|
        ≤ (104995189 / 7257600) * h * (L * |yn8 - zn8|) :=
          mul_le_mul_of_nonneg_left hLip8 c8_nn
      _ = (104995189 / 7257600) * h * L * |yn8 - zn8| := by ring
  have h7_abs : |(265932680 / 7257600) * h * (f tn7 yn7 - f tn7 zn7)|
      ≤ (265932680 / 7257600) * h * L * |yn7 - zn7| := by
    rw [abs_mul, abs_of_nonneg c7_nn]
    calc (265932680 / 7257600) * h * |f tn7 yn7 - f tn7 zn7|
        ≤ (265932680 / 7257600) * h * (L * |yn7 - zn7|) :=
          mul_le_mul_of_nonneg_left hLip7 c7_nn
      _ = (265932680 / 7257600) * h * L * |yn7 - zn7| := by ring
  have h6_abs : |(454661776 / 7257600) * h * (f tn6 yn6 - f tn6 zn6)|
      ≤ (454661776 / 7257600) * h * L * |yn6 - zn6| := by
    rw [abs_mul, abs_of_nonneg c6_nn]
    calc (454661776 / 7257600) * h * |f tn6 yn6 - f tn6 zn6|
        ≤ (454661776 / 7257600) * h * (L * |yn6 - zn6|) :=
          mul_le_mul_of_nonneg_left hLip6 c6_nn
      _ = (454661776 / 7257600) * h * L * |yn6 - zn6| := by ring
  have h5_abs : |(538363838 / 7257600) * h * (f tn5 yn5 - f tn5 zn5)|
      ≤ (538363838 / 7257600) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg c5_nn]
    calc (538363838 / 7257600) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (538363838 / 7257600) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip5 c5_nn
      _ = (538363838 / 7257600) * h * L * |yn5 - zn5| := by ring
  have h4_abs : |(444772162 / 7257600) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (444772162 / 7257600) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg c4_nn]
    calc (444772162 / 7257600) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (444772162 / 7257600) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 c4_nn
      _ = (444772162 / 7257600) * h * L * |yn4 - zn4| := by ring
  have h3_abs : |(252618224 / 7257600) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (252618224 / 7257600) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg c3_nn]
    calc (252618224 / 7257600) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (252618224 / 7257600) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 c3_nn
      _ = (252618224 / 7257600) * h * L * |yn3 - zn3| := by ring
  have h2_abs : |(94307320 / 7257600) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (94307320 / 7257600) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg c2_nn]
    calc (94307320 / 7257600) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (94307320 / 7257600) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 c2_nn
      _ = (94307320 / 7257600) * h * L * |yn2 - zn2| := by ring
  have h1_abs : |(20884811 / 7257600) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (20884811 / 7257600) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg c1_nn]
    calc (20884811 / 7257600) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (20884811 / 7257600) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 c1_nn
      _ = (20884811 / 7257600) * h * L * |yn1 - zn1| := by ring
  have h0_abs : |(2082753 / 7257600) * h * (f tn yn - f tn zn)|
      ≤ (2082753 / 7257600) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg c0_nn]
    calc (2082753 / 7257600) * h * |f tn yn - f tn zn|
        ≤ (2082753 / 7257600) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 c0_nn
      _ = (2082753 / 7257600) * h * L * |yn - zn| := by ring
  -- Triangle inequality (chained ten times).
  set S := (yn9 - zn9)
        + (30277247 / 7257600) * h * (f tn9 yn9 - f tn9 zn9)
        - (104995189 / 7257600) * h * (f tn8 yn8 - f tn8 zn8)
        + (265932680 / 7257600) * h * (f tn7 yn7 - f tn7 zn7)
        - (454661776 / 7257600) * h * (f tn6 yn6 - f tn6 zn6)
        + (538363838 / 7257600) * h * (f tn5 yn5 - f tn5 zn5)
        - (444772162 / 7257600) * h * (f tn4 yn4 - f tn4 zn4)
        + (252618224 / 7257600) * h * (f tn3 yn3 - f tn3 zn3)
        - (94307320 / 7257600) * h * (f tn2 yn2 - f tn2 zn2)
        + (20884811 / 7257600) * h * (f tn1 yn1 - f tn1 zn1)
        - (2082753 / 7257600) * h * (f tn yn - f tn zn) with hS_def
  have hcalc : ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10) - zn10 = S - τ :=
    halg
  have htri_S : |S| ≤ |yn9 - zn9|
              + |(30277247 / 7257600) * h * (f tn9 yn9 - f tn9 zn9)|
              + |(104995189 / 7257600) * h * (f tn8 yn8 - f tn8 zn8)|
              + |(265932680 / 7257600) * h * (f tn7 yn7 - f tn7 zn7)|
              + |(454661776 / 7257600) * h * (f tn6 yn6 - f tn6 zn6)|
              + |(538363838 / 7257600) * h * (f tn5 yn5 - f tn5 zn5)|
              + |(444772162 / 7257600) * h * (f tn4 yn4 - f tn4 zn4)|
              + |(252618224 / 7257600) * h * (f tn3 yn3 - f tn3 zn3)|
              + |(94307320 / 7257600) * h * (f tn2 yn2 - f tn2 zn2)|
              + |(20884811 / 7257600) * h * (f tn1 yn1 - f tn1 zn1)|
              + |(2082753 / 7257600) * h * (f tn yn - f tn zn)| := by
    have htri := ab10_step_lipschitz_triangle (yn9 - zn9)
      ((30277247 / 7257600) * h * (f tn9 yn9 - f tn9 zn9))
      ((104995189 / 7257600) * h * (f tn8 yn8 - f tn8 zn8))
      ((265932680 / 7257600) * h * (f tn7 yn7 - f tn7 zn7))
      ((454661776 / 7257600) * h * (f tn6 yn6 - f tn6 zn6))
      ((538363838 / 7257600) * h * (f tn5 yn5 - f tn5 zn5))
      ((444772162 / 7257600) * h * (f tn4 yn4 - f tn4 zn4))
      ((252618224 / 7257600) * h * (f tn3 yn3 - f tn3 zn3))
      ((94307320 / 7257600) * h * (f tn2 yn2 - f tn2 zn2))
      ((20884811 / 7257600) * h * (f tn1 yn1 - f tn1 zn1))
      ((2082753 / 7257600) * h * (f tn yn - f tn zn))
    rw [hS_def]
    linarith
  have htri : |S - τ| ≤ |S| + |τ| := abs_sub _ _
  have heq : |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10) - zn10|
      = |S - τ| := by rw [hcalc]
  rw [heq]
  linarith [htri, htri_S, h9_abs, h8_abs, h7_abs, h6_abs, h5_abs, h4_abs,
    h3_abs, h2_abs, h1_abs, h0_abs]

/-! ### Residual chain -/

/-- Algebraic identity decomposing the AB10 local truncation residual into
two y 11th-order Taylor remainders (at `9h` and `10h`) and nine y'
10th-order Taylor remainders (at `h, 2h, …, 9h`). Pure `ring` identity. -/
private lemma ab10_residual_alg_identity
    (y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 dd ddd dddd ddddd dddddd
      ddddddd dddddddd ddddddddd dddddddddd h : ℝ) :
    y10 - y9 - h * ((30277247 / 7257600) * d9 - (104995189 / 7257600) * d8
                  + (265932680 / 7257600) * d7 - (454661776 / 7257600) * d6
                  + (538363838 / 7257600) * d5 - (444772162 / 7257600) * d4
                  + (252618224 / 7257600) * d3 - (94307320 / 7257600) * d2
                  + (20884811 / 7257600) * d1 - (2082753 / 7257600) * d0)
      = (y10 - y0 - (10 * h) * d0
            - (10 * h) ^ 2 / 2 * dd
            - (10 * h) ^ 3 / 6 * ddd
            - (10 * h) ^ 4 / 24 * dddd
            - (10 * h) ^ 5 / 120 * ddddd
            - (10 * h) ^ 6 / 720 * dddddd
            - (10 * h) ^ 7 / 5040 * ddddddd
            - (10 * h) ^ 8 / 40320 * dddddddd
            - (10 * h) ^ 9 / 362880 * ddddddddd
            - (10 * h) ^ 10 / 3628800 * dddddddddd)
        - (y9 - y0 - (9 * h) * d0
            - (9 * h) ^ 2 / 2 * dd
            - (9 * h) ^ 3 / 6 * ddd
            - (9 * h) ^ 4 / 24 * dddd
            - (9 * h) ^ 5 / 120 * ddddd
            - (9 * h) ^ 6 / 720 * dddddd
            - (9 * h) ^ 7 / 5040 * ddddddd
            - (9 * h) ^ 8 / 40320 * dddddddd
            - (9 * h) ^ 9 / 362880 * ddddddddd
            - (9 * h) ^ 10 / 3628800 * dddddddddd)
        - (30277247 * h / 7257600)
            * (d9 - d0 - (9 * h) * dd
                - (9 * h) ^ 2 / 2 * ddd
                - (9 * h) ^ 3 / 6 * dddd
                - (9 * h) ^ 4 / 24 * ddddd
                - (9 * h) ^ 5 / 120 * dddddd
                - (9 * h) ^ 6 / 720 * ddddddd
                - (9 * h) ^ 7 / 5040 * dddddddd
                - (9 * h) ^ 8 / 40320 * ddddddddd
                - (9 * h) ^ 9 / 362880 * dddddddddd)
        + (104995189 * h / 7257600)
            * (d8 - d0 - (8 * h) * dd
                - (8 * h) ^ 2 / 2 * ddd
                - (8 * h) ^ 3 / 6 * dddd
                - (8 * h) ^ 4 / 24 * ddddd
                - (8 * h) ^ 5 / 120 * dddddd
                - (8 * h) ^ 6 / 720 * ddddddd
                - (8 * h) ^ 7 / 5040 * dddddddd
                - (8 * h) ^ 8 / 40320 * ddddddddd
                - (8 * h) ^ 9 / 362880 * dddddddddd)
        - (265932680 * h / 7257600)
            * (d7 - d0 - (7 * h) * dd
                - (7 * h) ^ 2 / 2 * ddd
                - (7 * h) ^ 3 / 6 * dddd
                - (7 * h) ^ 4 / 24 * ddddd
                - (7 * h) ^ 5 / 120 * dddddd
                - (7 * h) ^ 6 / 720 * ddddddd
                - (7 * h) ^ 7 / 5040 * dddddddd
                - (7 * h) ^ 8 / 40320 * ddddddddd
                - (7 * h) ^ 9 / 362880 * dddddddddd)
        + (454661776 * h / 7257600)
            * (d6 - d0 - (6 * h) * dd
                - (6 * h) ^ 2 / 2 * ddd
                - (6 * h) ^ 3 / 6 * dddd
                - (6 * h) ^ 4 / 24 * ddddd
                - (6 * h) ^ 5 / 120 * dddddd
                - (6 * h) ^ 6 / 720 * ddddddd
                - (6 * h) ^ 7 / 5040 * dddddddd
                - (6 * h) ^ 8 / 40320 * ddddddddd
                - (6 * h) ^ 9 / 362880 * dddddddddd)
        - (538363838 * h / 7257600)
            * (d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd
                - (5 * h) ^ 6 / 720 * ddddddd
                - (5 * h) ^ 7 / 5040 * dddddddd
                - (5 * h) ^ 8 / 40320 * ddddddddd
                - (5 * h) ^ 9 / 362880 * dddddddddd)
        + (444772162 * h / 7257600)
            * (d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd
                - (4 * h) ^ 6 / 720 * ddddddd
                - (4 * h) ^ 7 / 5040 * dddddddd
                - (4 * h) ^ 8 / 40320 * ddddddddd
                - (4 * h) ^ 9 / 362880 * dddddddddd)
        - (252618224 * h / 7257600)
            * (d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd
                - (3 * h) ^ 6 / 720 * ddddddd
                - (3 * h) ^ 7 / 5040 * dddddddd
                - (3 * h) ^ 8 / 40320 * ddddddddd
                - (3 * h) ^ 9 / 362880 * dddddddddd)
        + (94307320 * h / 7257600)
            * (d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd
                - (2 * h) ^ 6 / 720 * ddddddd
                - (2 * h) ^ 7 / 5040 * dddddddd
                - (2 * h) ^ 8 / 40320 * ddddddddd
                - (2 * h) ^ 9 / 362880 * dddddddddd)
        - (20884811 * h / 7257600)
            * (d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd
                - h ^ 6 / 720 * ddddddd
                - h ^ 7 / 5040 * dddddddd
                - h ^ 8 / 40320 * ddddddddd
                - h ^ 9 / 362880 * dddddddddd) := by
  ring

/-- Pure algebraic identity: the sum of the eleven scaled Lagrange remainder
bounds equals a fixed rational coefficient times `M · h^11`. -/
private lemma ab10_residual_bound_alg_identity (M h : ℝ) :
    M / 39916800 * (10 * h) ^ 11 + M / 39916800 * (9 * h) ^ 11
      + (30277247 * h / 7257600) * (M / 3628800 * (9 * h) ^ 10)
      + (104995189 * h / 7257600) * (M / 3628800 * (8 * h) ^ 10)
      + (265932680 * h / 7257600) * (M / 3628800 * (7 * h) ^ 10)
      + (454661776 * h / 7257600) * (M / 3628800 * (6 * h) ^ 10)
      + (538363838 * h / 7257600) * (M / 3628800 * (5 * h) ^ 10)
      + (444772162 * h / 7257600) * (M / 3628800 * (4 * h) ^ 10)
      + (252618224 * h / 7257600) * (M / 3628800 * (3 * h) ^ 10)
      + (94307320 * h / 7257600) * (M / 3628800 * (2 * h) ^ 10)
      + (20884811 * h / 7257600) * (M / 3628800 * h ^ 10)
      = (11840488855359257 / 754427520000 : ℝ) * M * h ^ 11 := by
  ring

/-- Auxiliary triangle inequality for eleven abstract terms with the AB10
residual sign pattern `A - B - C + D - E + F - G + H - I + J - K`. -/
private lemma ab10_residual_triangle_aux
    (A B sC sD sE sF sG sH sI sJ sK : ℝ) :
    |A - B - sC + sD - sE + sF - sG + sH - sI + sJ - sK|
      ≤ |A| + |B| + |sC| + |sD| + |sE| + |sF| + |sG| + |sH|
          + |sI| + |sJ| + |sK| := by
  have h1 : |A - B - sC + sD - sE + sF - sG + sH - sI + sJ - sK|
      ≤ |A - B - sC + sD - sE + sF - sG + sH - sI + sJ| + |sK| := abs_sub _ _
  have h2 : |A - B - sC + sD - sE + sF - sG + sH - sI + sJ|
      ≤ |A - B - sC + sD - sE + sF - sG + sH - sI| + |sJ| := abs_add_le _ _
  have h3 : |A - B - sC + sD - sE + sF - sG + sH - sI|
      ≤ |A - B - sC + sD - sE + sF - sG + sH| + |sI| := abs_sub _ _
  have h4 : |A - B - sC + sD - sE + sF - sG + sH|
      ≤ |A - B - sC + sD - sE + sF - sG| + |sH| := abs_add_le _ _
  have h5 : |A - B - sC + sD - sE + sF - sG|
      ≤ |A - B - sC + sD - sE + sF| + |sG| := abs_sub _ _
  have h6 : |A - B - sC + sD - sE + sF|
      ≤ |A - B - sC + sD - sE| + |sF| := abs_add_le _ _
  have h7 : |A - B - sC + sD - sE|
      ≤ |A - B - sC + sD| + |sE| := abs_sub _ _
  have h8 : |A - B - sC + sD| ≤ |A - B - sC| + |sD| := abs_add_le _ _
  have h9 : |A - B - sC| ≤ |A - B| + |sC| := abs_sub _ _
  have h10 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith

/-- Triangle inequality for the eleven-term AB10 residual chunk. -/
private lemma ab10_residual_eleven_term_triangle
    (A B C D E F G H I J K h : ℝ) (hh : 0 ≤ h) :
    |A - B - (30277247 * h / 7257600) * C + (104995189 * h / 7257600) * D
        - (265932680 * h / 7257600) * E + (454661776 * h / 7257600) * F
        - (538363838 * h / 7257600) * G + (444772162 * h / 7257600) * H
        - (252618224 * h / 7257600) * I + (94307320 * h / 7257600) * J
        - (20884811 * h / 7257600) * K|
      ≤ |A| + |B| + (30277247 * h / 7257600) * |C|
          + (104995189 * h / 7257600) * |D|
          + (265932680 * h / 7257600) * |E|
          + (454661776 * h / 7257600) * |F|
          + (538363838 * h / 7257600) * |G|
          + (444772162 * h / 7257600) * |H|
          + (252618224 * h / 7257600) * |I|
          + (94307320 * h / 7257600) * |J|
          + (20884811 * h / 7257600) * |K| := by
  have hc9_nn : 0 ≤ 30277247 * h / 7257600 := by linarith
  have hc8_nn : 0 ≤ 104995189 * h / 7257600 := by linarith
  have hc7_nn : 0 ≤ 265932680 * h / 7257600 := by linarith
  have hc6_nn : 0 ≤ 454661776 * h / 7257600 := by linarith
  have hc5_nn : 0 ≤ 538363838 * h / 7257600 := by linarith
  have hc4_nn : 0 ≤ 444772162 * h / 7257600 := by linarith
  have hc3_nn : 0 ≤ 252618224 * h / 7257600 := by linarith
  have hc2_nn : 0 ≤ 94307320 * h / 7257600 := by linarith
  have hc1_nn : 0 ≤ 20884811 * h / 7257600 := by linarith
  have habsC : |(30277247 * h / 7257600) * C| = (30277247 * h / 7257600) * |C| := by
    rw [abs_mul, abs_of_nonneg hc9_nn]
  have habsD : |(104995189 * h / 7257600) * D| = (104995189 * h / 7257600) * |D| := by
    rw [abs_mul, abs_of_nonneg hc8_nn]
  have habsE : |(265932680 * h / 7257600) * E| = (265932680 * h / 7257600) * |E| := by
    rw [abs_mul, abs_of_nonneg hc7_nn]
  have habsF : |(454661776 * h / 7257600) * F| = (454661776 * h / 7257600) * |F| := by
    rw [abs_mul, abs_of_nonneg hc6_nn]
  have habsG : |(538363838 * h / 7257600) * G| = (538363838 * h / 7257600) * |G| := by
    rw [abs_mul, abs_of_nonneg hc5_nn]
  have habsH : |(444772162 * h / 7257600) * H| = (444772162 * h / 7257600) * |H| := by
    rw [abs_mul, abs_of_nonneg hc4_nn]
  have habsI : |(252618224 * h / 7257600) * I| = (252618224 * h / 7257600) * |I| := by
    rw [abs_mul, abs_of_nonneg hc3_nn]
  have habsJ : |(94307320 * h / 7257600) * J| = (94307320 * h / 7257600) * |J| := by
    rw [abs_mul, abs_of_nonneg hc2_nn]
  have habsK : |(20884811 * h / 7257600) * K| = (20884811 * h / 7257600) * |K| := by
    rw [abs_mul, abs_of_nonneg hc1_nn]
  have htri := ab10_residual_triangle_aux A B
    ((30277247 * h / 7257600) * C) ((104995189 * h / 7257600) * D)
    ((265932680 * h / 7257600) * E) ((454661776 * h / 7257600) * F)
    ((538363838 * h / 7257600) * G) ((444772162 * h / 7257600) * H)
    ((252618224 * h / 7257600) * I) ((94307320 * h / 7257600) * J)
    ((20884811 * h / 7257600) * K)
  rw [habsC, habsD, habsE, habsF, habsG, habsH, habsI, habsJ, habsK] at htri
  exact htri

/-- Combine the eleven Taylor-remainder bounds into the final residual estimate.
Given abstract Taylor remainders `A,B,…,K` with bounds in terms of `M`, the
scaled triangle inequality and the bound algebraic identity, conclude
`≤ 15695 · M · h^11`. -/
private lemma ab10_residual_combine_aux
    (A B C D E F G H I J K M h : ℝ) (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (hA_bd : |A| ≤ M / 39916800 * (10 * h) ^ 11)
    (hB_bd : |B| ≤ M / 39916800 * (9 * h) ^ 11)
    (hC_bd : |C| ≤ M / 3628800 * (9 * h) ^ 10)
    (hD_bd : |D| ≤ M / 3628800 * (8 * h) ^ 10)
    (hE_bd : |E| ≤ M / 3628800 * (7 * h) ^ 10)
    (hF_bd : |F| ≤ M / 3628800 * (6 * h) ^ 10)
    (hG_bd : |G| ≤ M / 3628800 * (5 * h) ^ 10)
    (hH_bd : |H| ≤ M / 3628800 * (4 * h) ^ 10)
    (hI_bd : |I| ≤ M / 3628800 * (3 * h) ^ 10)
    (hJ_bd : |J| ≤ M / 3628800 * (2 * h) ^ 10)
    (hK_bd : |K| ≤ M / 3628800 * h ^ 10) :
    |A - B - (30277247 * h / 7257600) * C + (104995189 * h / 7257600) * D
        - (265932680 * h / 7257600) * E + (454661776 * h / 7257600) * F
        - (538363838 * h / 7257600) * G + (444772162 * h / 7257600) * H
        - (252618224 * h / 7257600) * I + (94307320 * h / 7257600) * J
        - (20884811 * h / 7257600) * K|
      ≤ 15695 * M * h ^ 11 := by
  have htri := ab10_residual_eleven_term_triangle A B C D E F G H I J K h hh
  have hc9_nn : 0 ≤ 30277247 * h / 7257600 := by linarith
  have hc8_nn : 0 ≤ 104995189 * h / 7257600 := by linarith
  have hc7_nn : 0 ≤ 265932680 * h / 7257600 := by linarith
  have hc6_nn : 0 ≤ 454661776 * h / 7257600 := by linarith
  have hc5_nn : 0 ≤ 538363838 * h / 7257600 := by linarith
  have hc4_nn : 0 ≤ 444772162 * h / 7257600 := by linarith
  have hc3_nn : 0 ≤ 252618224 * h / 7257600 := by linarith
  have hc2_nn : 0 ≤ 94307320 * h / 7257600 := by linarith
  have hc1_nn : 0 ≤ 20884811 * h / 7257600 := by linarith
  have hCbd_s : (30277247 * h / 7257600) * |C|
      ≤ (30277247 * h / 7257600) * (M / 3628800 * (9 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hC_bd hc9_nn
  have hDbd_s : (104995189 * h / 7257600) * |D|
      ≤ (104995189 * h / 7257600) * (M / 3628800 * (8 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hD_bd hc8_nn
  have hEbd_s : (265932680 * h / 7257600) * |E|
      ≤ (265932680 * h / 7257600) * (M / 3628800 * (7 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hE_bd hc7_nn
  have hFbd_s : (454661776 * h / 7257600) * |F|
      ≤ (454661776 * h / 7257600) * (M / 3628800 * (6 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hF_bd hc6_nn
  have hGbd_s : (538363838 * h / 7257600) * |G|
      ≤ (538363838 * h / 7257600) * (M / 3628800 * (5 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hG_bd hc5_nn
  have hHbd_s : (444772162 * h / 7257600) * |H|
      ≤ (444772162 * h / 7257600) * (M / 3628800 * (4 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hH_bd hc4_nn
  have hIbd_s : (252618224 * h / 7257600) * |I|
      ≤ (252618224 * h / 7257600) * (M / 3628800 * (3 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hI_bd hc3_nn
  have hJbd_s : (94307320 * h / 7257600) * |J|
      ≤ (94307320 * h / 7257600) * (M / 3628800 * (2 * h) ^ 10) :=
    mul_le_mul_of_nonneg_left hJ_bd hc2_nn
  have hKbd_s : (20884811 * h / 7257600) * |K|
      ≤ (20884811 * h / 7257600) * (M / 3628800 * h ^ 10) :=
    mul_le_mul_of_nonneg_left hK_bd hc1_nn
  have hbound_alg := ab10_residual_bound_alg_identity M h
  have hh11_nn : 0 ≤ h ^ 11 := by positivity
  have hMh11_nn : 0 ≤ M * h ^ 11 := mul_nonneg hMnn hh11_nn
  have hslack : (11840488855359257 / 754427520000 : ℝ) * M * h ^ 11
      ≤ 15695 * M * h ^ 11 := by
    rw [mul_assoc, mul_assoc (15695 : ℝ)]
    have hle : (11840488855359257 / 754427520000 : ℝ) ≤ 15695 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh11_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hEbd_s,
    hFbd_s, hGbd_s, hHbd_s, hIbd_s, hJbd_s, hKbd_s]

/-- AB10 residual at a single base point `t` is `O(M · h^11)`, where `M`
bounds the 11th derivative of the exact solution on a window covering
`[t, t + 10h]`. Decomposes the residual into eleven Taylor remainders
(two y 11th-order, nine y' 10th-order). -/
private theorem ab10_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 11 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 11 y t| ≤ M)
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
    (hh : 0 ≤ h) :
    |y (t + 10 * h) - y (t + 9 * h)
        - h * ((30277247 / 7257600) * deriv y (t + 9 * h)
              - (104995189 / 7257600) * deriv y (t + 8 * h)
              + (265932680 / 7257600) * deriv y (t + 7 * h)
              - (454661776 / 7257600) * deriv y (t + 6 * h)
              + (538363838 / 7257600) * deriv y (t + 5 * h)
              - (444772162 / 7257600) * deriv y (t + 4 * h)
              + (252618224 / 7257600) * deriv y (t + 3 * h)
              - (94307320 / 7257600) * deriv y (t + 2 * h)
              + (20884811 / 7257600) * deriv y (t + h)
              - (2082753 / 7257600) * deriv y t)|
      ≤ (15695 : ℝ) * M * h ^ 11 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have h9h : 0 ≤ 9 * h := by linarith
  have h10h : 0 ≤ 10 * h := by linarith
  -- R_y(9), R_y(10): y Taylor remainders at order 11.
  have hRy9 :=
    y_eleventh_order_taylor_remainder hy hbnd ht ht9h h9h
  have hRy10 :=
    y_eleventh_order_taylor_remainder hy hbnd ht ht10h h10h
  -- R_y'(1), …, R_y'(9): y' Taylor remainders at order 10.
  have hRyp1 :=
    derivY_tenth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_tenth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_tenth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_tenth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_tenth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_tenth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_tenth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_tenth_order_taylor_remainder hy hbnd ht ht8h h8h
  have hRyp9 :=
    derivY_tenth_order_taylor_remainder hy hbnd ht ht9h h9h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y9 := y (t + 9 * h) with hy9_def
  set y10 := y (t + 10 * h) with hy10_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set d6 := deriv y (t + 6 * h) with hd6_def
  set d7 := deriv y (t + 7 * h) with hd7_def
  set d8 := deriv y (t + 8 * h) with hd8_def
  set d9 := deriv y (t + 9 * h) with hd9_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd := iteratedDeriv 8 y t with hdddddddd_def
  set ddddddddd := iteratedDeriv 9 y t with hddddddddd_def
  set dddddddddd := iteratedDeriv 10 y t with hdddddddddd_def
  clear_value y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
    dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd dddddddddd
  -- Algebraic identity for the residual.
  have hLTE_eq :=
    ab10_residual_alg_identity y0 y9 y10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
      dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd dddddddddd h
  rw [hLTE_eq]
  -- Triangle inequality (chained).
  set A := y10 - y0 - (10 * h) * d0
            - (10 * h) ^ 2 / 2 * dd
            - (10 * h) ^ 3 / 6 * ddd
            - (10 * h) ^ 4 / 24 * dddd
            - (10 * h) ^ 5 / 120 * ddddd
            - (10 * h) ^ 6 / 720 * dddddd
            - (10 * h) ^ 7 / 5040 * ddddddd
            - (10 * h) ^ 8 / 40320 * dddddddd
            - (10 * h) ^ 9 / 362880 * ddddddddd
            - (10 * h) ^ 10 / 3628800 * dddddddddd with hA_def
  set B := y9 - y0 - (9 * h) * d0
            - (9 * h) ^ 2 / 2 * dd
            - (9 * h) ^ 3 / 6 * ddd
            - (9 * h) ^ 4 / 24 * dddd
            - (9 * h) ^ 5 / 120 * ddddd
            - (9 * h) ^ 6 / 720 * dddddd
            - (9 * h) ^ 7 / 5040 * ddddddd
            - (9 * h) ^ 8 / 40320 * dddddddd
            - (9 * h) ^ 9 / 362880 * ddddddddd
            - (9 * h) ^ 10 / 3628800 * dddddddddd with hB_def
  set C := d9 - d0 - (9 * h) * dd
            - (9 * h) ^ 2 / 2 * ddd
            - (9 * h) ^ 3 / 6 * dddd
            - (9 * h) ^ 4 / 24 * ddddd
            - (9 * h) ^ 5 / 120 * dddddd
            - (9 * h) ^ 6 / 720 * ddddddd
            - (9 * h) ^ 7 / 5040 * dddddddd
            - (9 * h) ^ 8 / 40320 * ddddddddd
            - (9 * h) ^ 9 / 362880 * dddddddddd with hC_def
  set D := d8 - d0 - (8 * h) * dd
            - (8 * h) ^ 2 / 2 * ddd
            - (8 * h) ^ 3 / 6 * dddd
            - (8 * h) ^ 4 / 24 * ddddd
            - (8 * h) ^ 5 / 120 * dddddd
            - (8 * h) ^ 6 / 720 * ddddddd
            - (8 * h) ^ 7 / 5040 * dddddddd
            - (8 * h) ^ 8 / 40320 * ddddddddd
            - (8 * h) ^ 9 / 362880 * dddddddddd with hD_def
  set E := d7 - d0 - (7 * h) * dd
            - (7 * h) ^ 2 / 2 * ddd
            - (7 * h) ^ 3 / 6 * dddd
            - (7 * h) ^ 4 / 24 * ddddd
            - (7 * h) ^ 5 / 120 * dddddd
            - (7 * h) ^ 6 / 720 * ddddddd
            - (7 * h) ^ 7 / 5040 * dddddddd
            - (7 * h) ^ 8 / 40320 * ddddddddd
            - (7 * h) ^ 9 / 362880 * dddddddddd with hE_def
  set F := d6 - d0 - (6 * h) * dd
            - (6 * h) ^ 2 / 2 * ddd
            - (6 * h) ^ 3 / 6 * dddd
            - (6 * h) ^ 4 / 24 * ddddd
            - (6 * h) ^ 5 / 120 * dddddd
            - (6 * h) ^ 6 / 720 * ddddddd
            - (6 * h) ^ 7 / 5040 * dddddddd
            - (6 * h) ^ 8 / 40320 * ddddddddd
            - (6 * h) ^ 9 / 362880 * dddddddddd with hF_def
  set G := d5 - d0 - (5 * h) * dd
            - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd
            - (5 * h) ^ 5 / 120 * dddddd
            - (5 * h) ^ 6 / 720 * ddddddd
            - (5 * h) ^ 7 / 5040 * dddddddd
            - (5 * h) ^ 8 / 40320 * ddddddddd
            - (5 * h) ^ 9 / 362880 * dddddddddd with hG_def
  set H := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd
            - (4 * h) ^ 5 / 120 * dddddd
            - (4 * h) ^ 6 / 720 * ddddddd
            - (4 * h) ^ 7 / 5040 * dddddddd
            - (4 * h) ^ 8 / 40320 * ddddddddd
            - (4 * h) ^ 9 / 362880 * dddddddddd with hH_def
  set I := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd
            - (3 * h) ^ 5 / 120 * dddddd
            - (3 * h) ^ 6 / 720 * ddddddd
            - (3 * h) ^ 7 / 5040 * dddddddd
            - (3 * h) ^ 8 / 40320 * ddddddddd
            - (3 * h) ^ 9 / 362880 * dddddddddd with hI_def
  set J := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd
            - (2 * h) ^ 5 / 120 * dddddd
            - (2 * h) ^ 6 / 720 * ddddddd
            - (2 * h) ^ 7 / 5040 * dddddddd
            - (2 * h) ^ 8 / 40320 * ddddddddd
            - (2 * h) ^ 9 / 362880 * dddddddddd with hJ_def
  set K := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd
            - h ^ 5 / 120 * dddddd
            - h ^ 6 / 720 * ddddddd
            - h ^ 7 / 5040 * dddddddd
            - h ^ 8 / 40320 * ddddddddd
            - h ^ 9 / 362880 * dddddddddd with hK_def
  clear_value A B C D E F G H I J K
  have hA_bd : |A| ≤ M / 39916800 * (10 * h) ^ 11 := hRy10
  have hB_bd : |B| ≤ M / 39916800 * (9 * h) ^ 11 := hRy9
  have hC_bd : |C| ≤ M / 3628800 * (9 * h) ^ 10 := hRyp9
  have hD_bd : |D| ≤ M / 3628800 * (8 * h) ^ 10 := hRyp8
  have hE_bd : |E| ≤ M / 3628800 * (7 * h) ^ 10 := hRyp7
  have hF_bd : |F| ≤ M / 3628800 * (6 * h) ^ 10 := hRyp6
  have hG_bd : |G| ≤ M / 3628800 * (5 * h) ^ 10 := hRyp5
  have hH_bd : |H| ≤ M / 3628800 * (4 * h) ^ 10 := hRyp4
  have hI_bd : |I| ≤ M / 3628800 * (3 * h) ^ 10 := hRyp3
  have hJ_bd : |J| ≤ M / 3628800 * (2 * h) ^ 10 := hRyp2
  have hK_bd : |K| ≤ M / 3628800 * h ^ 10 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact ab10_residual_combine_aux A B C D E F G H I J K M h hh hMnn
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hH_bd hI_bd hJ_bd hK_bd

/-- Uniform bound on the AB10 one-step truncation residual on a finite
horizon, given a `C^11` exact solution. -/
theorem ab10_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 11 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 10) * h ≤ T →
        |adamsBashforth10.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 11 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_eleven_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(15695 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 10) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 9 * h ≤ ((n : ℝ) + 10) * h := by nlinarith
    linarith
  have ht10h_mem : t + 10 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 10 * h = ((n : ℝ) + 10) * h := by ring
    linarith
  rw [ab10_localTruncationError_eq]
  show |y (t + 10 * h) - y (t + 9 * h)
      - h * (30277247 / 7257600 * deriv y (t + 9 * h)
              - 104995189 / 7257600 * deriv y (t + 8 * h)
              + 265932680 / 7257600 * deriv y (t + 7 * h)
              - 454661776 / 7257600 * deriv y (t + 6 * h)
              + 538363838 / 7257600 * deriv y (t + 5 * h)
              - 444772162 / 7257600 * deriv y (t + 4 * h)
              + 252618224 / 7257600 * deriv y (t + 3 * h)
              - 94307320 / 7257600 * deriv y (t + 2 * h)
              + 20884811 / 7257600 * deriv y (t + h)
              - 2082753 / 7257600 * deriv y t)|
    ≤ 15695 * M * h ^ 11
  have hreshape :
      h * (30277247 / 7257600 * deriv y (t + 9 * h)
            - 104995189 / 7257600 * deriv y (t + 8 * h)
            + 265932680 / 7257600 * deriv y (t + 7 * h)
            - 454661776 / 7257600 * deriv y (t + 6 * h)
            + 538363838 / 7257600 * deriv y (t + 5 * h)
            - 444772162 / 7257600 * deriv y (t + 4 * h)
            + 252618224 / 7257600 * deriv y (t + 3 * h)
            - 94307320 / 7257600 * deriv y (t + 2 * h)
            + 20884811 / 7257600 * deriv y (t + h)
            - 2082753 / 7257600 * deriv y t)
        = h * ((30277247 / 7257600) * deriv y (t + 9 * h)
              - (104995189 / 7257600) * deriv y (t + 8 * h)
              + (265932680 / 7257600) * deriv y (t + 7 * h)
              - (454661776 / 7257600) * deriv y (t + 6 * h)
              + (538363838 / 7257600) * deriv y (t + 5 * h)
              - (444772162 / 7257600) * deriv y (t + 4 * h)
              + (252618224 / 7257600) * deriv y (t + 3 * h)
              - (94307320 / 7257600) * deriv y (t + 2 * h)
              + (20884811 / 7257600) * deriv y (t + h)
              - (2082753 / 7257600) * deriv y t) := by ring
  rw [hreshape]
  exact ab10_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem ht10h_mem hh.le

/-- Max-norm one-step error recurrence for AB10 with Lipschitz constant
`L`. With `eN k := |y_k − y(t_k)|` and a 10-window max
`EN k := max (eN k, eN (k+1), …, eN (k+9))`,
`EN (n+1) ≤ (1 + h · (172570/567) · L) · EN n + |τ_n|`. The
`(172570/567)` factor is the ℓ¹-norm of the AB10 coefficient vector. -/
theorem ab10_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max (max (max
          |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
          |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
          |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
          |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|)
          |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|)
          |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|)
          |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)|)
        |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)|
      ≤ (1 + h * ((172570 / 567) * L))
            * max (max (max (max (max (max (max (max (max
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n
                      - y (t₀ + (n : ℝ) * h)|
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)|)
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)|)
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5)
                      - y (t₀ + ((n : ℝ) + 5) * h)|)
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6)
                      - y (t₀ + ((n : ℝ) + 6) * h)|)
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7)
                      - y (t₀ + ((n : ℝ) + 7) * h)|)
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8)
                      - y (t₀ + ((n : ℝ) + 8) * h)|)
                  |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9)
                      - y (t₀ + ((n : ℝ) + 9) * h)|
        + |adamsBashforth10.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n - y (t₀ + (n : ℝ) * h)|
    with hen_def
  set en1 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
    with hen1_def
  set en2 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
    with hen2_def
  set en3 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
    with hen3_def
  set en4 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
    with hen4_def
  set en5 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
    with hen5_def
  set en6 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
    with hen6_def
  set en7 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
    with hen7_def
  set en8 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
    with hen8_def
  set en9 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)|
    with hen9_def
  set en10 : ℝ :=
    |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)|
    with hen10_def
  set τabs : ℝ :=
    |adamsBashforth10.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hen7_nn : 0 ≤ en7 := abs_nonneg _
  have hen8_nn : 0 ≤ en8 := abs_nonneg _
  have hen9_nn : 0 ≤ en9 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  -- One-step Lipschitz bound (from `ab10_one_step_lipschitz`).
  have hstep :
      en10 ≤ en9 + (30277247 / 7257600) * h * L * en9
                + (104995189 / 7257600) * h * L * en8
                + (265932680 / 7257600) * h * L * en7
                + (454661776 / 7257600) * h * L * en6
                + (538363838 / 7257600) * h * L * en5
                + (444772162 / 7257600) * h * L * en4
                + (252618224 / 7257600) * h * L * en3
                + (94307320 / 7257600) * h * L * en2
                + (20884811 / 7257600) * h * L * en1
                + (2082753 / 7257600) * h * L * en + τabs := by
    have := ab10_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y hyf n
    show |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 10) - y (t₀ + ((n : ℝ) + 10) * h)|
        ≤ |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)|
          + (30277247 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 9)
                  - y (t₀ + ((n : ℝ) + 9) * h)|
          + (104995189 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 8)
                  - y (t₀ + ((n : ℝ) + 8) * h)|
          + (265932680 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 7)
                  - y (t₀ + ((n : ℝ) + 7) * h)|
          + (454661776 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 6)
                  - y (t₀ + ((n : ℝ) + 6) * h)|
          + (538363838 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 5)
                  - y (t₀ + ((n : ℝ) + 5) * h)|
          + (444772162 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)|
          + (252618224 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)|
          + (94307320 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)|
          + (20884811 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)|
          + (2082753 / 7257600) * h * L
              * |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n - y (t₀ + (n : ℝ) * h)|
          + |adamsBashforth10.localTruncationError h (t₀ + (n : ℝ) * h) y|
    exact this
  set EN_n : ℝ :=
    max (max (max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7) en8) en9
    with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen5_le_EN : en5 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)
  have hen6_le_EN : en6 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen7_le_EN : en7 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen8_le_EN : en8 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen9_le_EN : en9 ≤ EN_n := le_max_right _ _
  have hc9_nn : 0 ≤ (30277247 / 7257600) * h * L := by positivity
  have hc8_nn : 0 ≤ (104995189 / 7257600) * h * L := by positivity
  have hc7_nn : 0 ≤ (265932680 / 7257600) * h * L := by positivity
  have hc6_nn : 0 ≤ (454661776 / 7257600) * h * L := by positivity
  have hc5_nn : 0 ≤ (538363838 / 7257600) * h * L := by positivity
  have hc4_nn : 0 ≤ (444772162 / 7257600) * h * L := by positivity
  have hc3_nn : 0 ≤ (252618224 / 7257600) * h * L := by positivity
  have hc2_nn : 0 ≤ (94307320 / 7257600) * h * L := by positivity
  have hc1_nn : 0 ≤ (20884811 / 7257600) * h * L := by positivity
  have hc0_nn : 0 ≤ (2082753 / 7257600) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((172570 / 567) * L) := by positivity
  have hen10_bd : en10 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    have h1 : (30277247 / 7257600) * h * L * en9 ≤ (30277247 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen9_le_EN hc9_nn
    have h2 : (104995189 / 7257600) * h * L * en8 ≤ (104995189 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen8_le_EN hc8_nn
    have h3 : (265932680 / 7257600) * h * L * en7 ≤ (265932680 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen7_le_EN hc7_nn
    have h4 : (454661776 / 7257600) * h * L * en6 ≤ (454661776 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen6_le_EN hc6_nn
    have h5 : (538363838 / 7257600) * h * L * en5 ≤ (538363838 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen5_le_EN hc5_nn
    have h6 : (444772162 / 7257600) * h * L * en4 ≤ (444772162 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN hc4_nn
    have h7 : (252618224 / 7257600) * h * L * en3 ≤ (252618224 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN hc3_nn
    have h8 : (94307320 / 7257600) * h * L * en2 ≤ (94307320 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN hc2_nn
    have h9 : (20884811 / 7257600) * h * L * en1 ≤ (20884811 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN hc1_nn
    have h10 : (2082753 / 7257600) * h * L * en ≤ (2082753 / 7257600) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN hc0_nn
    have h_alg :
        EN_n + (30277247 / 7257600) * h * L * EN_n
              + (104995189 / 7257600) * h * L * EN_n
              + (265932680 / 7257600) * h * L * EN_n
              + (454661776 / 7257600) * h * L * EN_n
              + (538363838 / 7257600) * h * L * EN_n
              + (444772162 / 7257600) * h * L * EN_n
              + (252618224 / 7257600) * h * L * EN_n
              + (94307320 / 7257600) * h * L * EN_n
              + (20884811 / 7257600) * h * L * EN_n
              + (2082753 / 7257600) * h * L * EN_n + τabs
          = (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen9_le_EN, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h_alg.le]
  have hEN_le_grow : EN_n ≤ (1 + h * ((172570 / 567) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((172570 / 567) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  have hen5_bd : en5 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    linarith [hen5_le_EN, hEN_le_grow]
  have hen6_bd : en6 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    linarith [hen6_le_EN, hEN_le_grow]
  have hen7_bd : en7 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    linarith [hen7_le_EN, hEN_le_grow]
  have hen8_bd : en8 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    linarith [hen8_le_EN, hEN_le_grow]
  have hen9_bd : en9 ≤ (1 + h * ((172570 / 567) * L)) * EN_n + τabs := by
    linarith [hen9_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd)
    hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd) hen9_bd) hen10_bd

/-! ### Headline: AB10 global error bound via the generic AB scaffold

Routes the scalar AB10 headline through the generic AB scaffold at `s = 10`. -/

/-- AB10 coefficient vector for the generic AB scaffold, ordered from the
oldest to newest sample in the ten-step window. -/
noncomputable def ab10GenericCoeff : Fin 10 → ℝ :=
  ![-(2082753 : ℝ) / 7257600, (20884811 : ℝ) / 7257600,
    -(94307320 : ℝ) / 7257600, (252618224 : ℝ) / 7257600,
    -(444772162 : ℝ) / 7257600, (538363838 : ℝ) / 7257600,
    -(454661776 : ℝ) / 7257600, (265932680 : ℝ) / 7257600,
    -(104995189 : ℝ) / 7257600, (30277247 : ℝ) / 7257600]

@[simp] lemma ab10GenericCoeff_zero :
    ab10GenericCoeff 0 = -(2082753 : ℝ) / 7257600 := rfl

@[simp] lemma ab10GenericCoeff_one :
    ab10GenericCoeff 1 = (20884811 : ℝ) / 7257600 := rfl

@[simp] lemma ab10GenericCoeff_two :
    ab10GenericCoeff 2 = -(94307320 : ℝ) / 7257600 := rfl

@[simp] lemma ab10GenericCoeff_three :
    ab10GenericCoeff 3 = (252618224 : ℝ) / 7257600 := rfl

@[simp] lemma ab10GenericCoeff_four :
    ab10GenericCoeff 4 = -(444772162 : ℝ) / 7257600 := rfl

@[simp] lemma ab10GenericCoeff_five :
    ab10GenericCoeff 5 = (538363838 : ℝ) / 7257600 := rfl

@[simp] lemma ab10GenericCoeff_six :
    ab10GenericCoeff 6 = -(454661776 : ℝ) / 7257600 := rfl

@[simp] lemma ab10GenericCoeff_seven :
    ab10GenericCoeff 7 = (265932680 : ℝ) / 7257600 := rfl

@[simp] lemma ab10GenericCoeff_eight :
    ab10GenericCoeff 8 = -(104995189 : ℝ) / 7257600 := rfl

@[simp] lemma ab10GenericCoeff_nine :
    ab10GenericCoeff 9 = (30277247 : ℝ) / 7257600 := rfl

/-- Helper: expand `∑ i : Fin 10, f i` as ten summands. -/
private lemma sum_univ_ten_aux {α : Type*} [AddCommMonoid α] (f : Fin 10 → α) :
    ∑ i : Fin 10, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

/-- The effective Lipschitz constant for the generic AB scaffold at the
AB10 coefficient tuple is `(172570/567) · L`. -/
lemma abLip_ab10GenericCoeff (L : ℝ) :
    abLip 10 ab10GenericCoeff L = (172570 / 567) * L := by
  rw [abLip, sum_univ_ten_aux, ab10GenericCoeff_zero, ab10GenericCoeff_one,
    ab10GenericCoeff_two, ab10GenericCoeff_three, ab10GenericCoeff_four,
    ab10GenericCoeff_five, ab10GenericCoeff_six, ab10GenericCoeff_seven,
    ab10GenericCoeff_eight, ab10GenericCoeff_nine]
  rw [show |(-(2082753 : ℝ) / 7257600)| = (2082753 : ℝ) / 7257600 by norm_num,
      show |((20884811 : ℝ) / 7257600)| = (20884811 : ℝ) / 7257600 by norm_num,
      show |(-(94307320 : ℝ) / 7257600)| = (94307320 : ℝ) / 7257600 by norm_num,
      show |((252618224 : ℝ) / 7257600)| = (252618224 : ℝ) / 7257600 by norm_num,
      show |(-(444772162 : ℝ) / 7257600)| = (444772162 : ℝ) / 7257600 by norm_num,
      show |((538363838 : ℝ) / 7257600)| = (538363838 : ℝ) / 7257600 by norm_num,
      show |(-(454661776 : ℝ) / 7257600)| = (454661776 : ℝ) / 7257600 by norm_num,
      show |((265932680 : ℝ) / 7257600)| = (265932680 : ℝ) / 7257600 by norm_num,
      show |(-(104995189 : ℝ) / 7257600)| = (104995189 : ℝ) / 7257600 by norm_num,
      show |((30277247 : ℝ) / 7257600)| = (30277247 : ℝ) / 7257600 by norm_num]
  ring

/-- Bridge: the AB10 scalar iteration is the generic AB iteration
at `s = 10` with `α = ab10GenericCoeff` and starting samples
`![y₀, y₁, …, y₉]`. -/
lemma ab10Iter_eq_abIter
    (h : ℝ) (f : ℝ → ℝ → ℝ)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ) (n : ℕ) :
    ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ n
      = abIter 10 ab10GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 0 = _
      rw [ab10Iter_zero]
      unfold abIter
      simp
    | 1 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 1 = _
      rw [ab10Iter_one]
      unfold abIter
      simp
    | 2 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 2 = _
      rw [ab10Iter_two]
      unfold abIter
      simp
    | 3 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 3 = _
      rw [ab10Iter_three]
      unfold abIter
      simp
    | 4 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 4 = _
      rw [ab10Iter_four]
      unfold abIter
      simp
    | 5 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 5 = _
      rw [ab10Iter_five]
      unfold abIter
      simp
    | 6 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 6 = _
      rw [ab10Iter_six]
      unfold abIter
      simp
    | 7 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 7 = _
      rw [ab10Iter_seven]
      unfold abIter
      simp
    | 8 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 8 = _
      rw [ab10Iter_eight]
      unfold abIter
      simp
    | 9 =>
      show ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ 9 = _
      rw [ab10Iter_nine]
      unfold abIter
      simp
    | k + 10 =>
      rw [ab10Iter_succ_ten]
      rw [abIter_step (s := 10) (by norm_num)
          ab10GenericCoeff h f t₀
            ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉] k]
      rw [show (k + 10 - 1 : ℕ) = k + 9 from by omega]
      rw [sum_univ_ten_aux]
      have hval3 : ((3 : Fin 10) : ℕ) = 3 := rfl
      have hval4 : ((4 : Fin 10) : ℕ) = 4 := rfl
      have hval5 : ((5 : Fin 10) : ℕ) = 5 := rfl
      have hval6 : ((6 : Fin 10) : ℕ) = 6 := rfl
      have hval7 : ((7 : Fin 10) : ℕ) = 7 := rfl
      have hval8 : ((8 : Fin 10) : ℕ) = 8 := rfl
      have hval9 : ((9 : Fin 10) : ℕ) = 9 := rfl
      simp only [ab10GenericCoeff_zero, ab10GenericCoeff_one,
        ab10GenericCoeff_two, ab10GenericCoeff_three, ab10GenericCoeff_four,
        ab10GenericCoeff_five, ab10GenericCoeff_six, ab10GenericCoeff_seven,
        ab10GenericCoeff_eight, ab10GenericCoeff_nine,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5, hval6,
        hval7, hval8, hval9, Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega), ← ih (k + 4) (by omega),
        ← ih (k + 5) (by omega), ← ih (k + 6) (by omega),
        ← ih (k + 7) (by omega), ← ih (k + 8) (by omega),
        ← ih (k + 9) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring,
        show ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 by push_cast; ring,
        show ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring,
        show ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 by push_cast; ring,
        show ((k + 7 : ℕ) : ℝ) = (k : ℝ) + 7 by push_cast; ring,
        show ((k + 8 : ℕ) : ℝ) = (k : ℝ) + 8 by push_cast; ring,
        show ((k + 9 : ℕ) : ℝ) = (k : ℝ) + 9 by push_cast; ring]
      ring

/-- Bridge: the AB10 scalar truncation residual at base point `t₀ + n · h`
equals the generic AB residual at index `n`. -/
lemma ab10Residual_eq_abResidual
    (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    y (t₀ + (n : ℝ) * h + 10 * h) - y (t₀ + (n : ℝ) * h + 9 * h)
        - h * (30277247 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 9 * h)
              - 104995189 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 8 * h)
              + 265932680 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 7 * h)
              - 454661776 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 6 * h)
              + 538363838 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              - 444772162 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              + 252618224 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              - 94307320 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              + 20884811 / 7257600 * deriv y (t₀ + (n : ℝ) * h + h)
              - 2082753 / 7257600 * deriv y (t₀ + (n : ℝ) * h))
      = abResidual 10 ab10GenericCoeff h y t₀ n := by
  unfold abResidual
  rw [sum_univ_ten_aux, ab10GenericCoeff_zero, ab10GenericCoeff_one,
    ab10GenericCoeff_two, ab10GenericCoeff_three, ab10GenericCoeff_four,
    ab10GenericCoeff_five, ab10GenericCoeff_six, ab10GenericCoeff_seven,
    ab10GenericCoeff_eight, ab10GenericCoeff_nine]
  have eA : t₀ + (n : ℝ) * h + 10 * h = t₀ + ((n + 10 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 9 * h = t₀ + ((n + 10 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 10 - 1 : ℕ) = n + 9 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 10) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 10) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 10) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 10) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  have eJ : t₀ + (n : ℝ) * h + 7 * h
      = t₀ + ((n + ((7 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((7 : Fin 10) : ℕ) = 7 := rfl
    rw [this]; push_cast; ring
  have eK : t₀ + (n : ℝ) * h + 8 * h
      = t₀ + ((n + ((8 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((8 : Fin 10) : ℕ) = 8 := rfl
    rw [this]; push_cast; ring
  have eL : t₀ + (n : ℝ) * h + 9 * h
      = t₀ + ((n + ((9 : Fin 10) : ℕ) : ℕ) : ℝ) * h := by
    have : ((9 : Fin 10) : ℕ) = 9 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI, ← eJ, ← eK, ← eL]
  ring

/-- Final AB10 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
`C^11` exact solution `y` with `deriv y t = f t (y t)`, and starting
errors `|y_i - y(t_i)| ≤ ε₀` for `i = 0, 1, …, 9`, the AB10 iterate error
obeys `O(ε₀ + h^10)` on a finite horizon. -/
theorem ab10_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 11 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      |y₃ - y (t₀ + 3 * h)| ≤ ε₀ →
      |y₄ - y (t₀ + 4 * h)| ≤ ε₀ →
      |y₅ - y (t₀ + 5 * h)| ≤ ε₀ →
      |y₆ - y (t₀ + 6 * h)| ≤ ε₀ →
      |y₇ - y (t₀ + 7 * h)| ≤ ε₀ →
      |y₈ - y (t₀ + 8 * h)| ≤ ε₀ →
      |y₉ - y (t₀ + 9 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 9) * h ≤ T →
      |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((172570 / 567) * L * T) * ε₀ + K * h ^ 10 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab10_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((172570 / 567) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd N hNh
  set α : Fin 10 → ℝ := ab10GenericCoeff with hα_def
  set y₀_non : Fin 10 → ℝ := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉]
    with hy_non_def
  have hs : (1 : ℕ) ≤ 10 := by norm_num
  haveI : Nonempty (Fin 10) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIter 10 α h f t₀ y₀_non 0 = y₀ := by
    unfold abIter; simp [hy_non_def]
  have hiter1 : abIter 10 α h f t₀ y₀_non 1 = y₁ := by
    unfold abIter; simp [hy_non_def]
  have hiter2 : abIter 10 α h f t₀ y₀_non 2 = y₂ := by
    unfold abIter; simp [hy_non_def]
  have hiter3 : abIter 10 α h f t₀ y₀_non 3 = y₃ := by
    unfold abIter; simp [hy_non_def]
  have hiter4 : abIter 10 α h f t₀ y₀_non 4 = y₄ := by
    unfold abIter; simp [hy_non_def]
  have hiter5 : abIter 10 α h f t₀ y₀_non 5 = y₅ := by
    unfold abIter; simp [hy_non_def]
  have hiter6 : abIter 10 α h f t₀ y₀_non 6 = y₆ := by
    unfold abIter; simp [hy_non_def]
  have hiter7 : abIter 10 α h f t₀ y₀_non 7 = y₇ := by
    unfold abIter; simp [hy_non_def]
  have hiter8 : abIter 10 α h f t₀ y₀_non 8 = y₈ := by
    unfold abIter; simp [hy_non_def]
  have hiter9 : abIter 10 α h f t₀ y₀_non 9 = y₉ := by
    unfold abIter; simp [hy_non_def]
  have hstart : abErrWindow hs α h f t₀ y₀_non y 0 ≤ ε₀ := by
    unfold abErrWindow
    apply Finset.sup'_le
    intro j _
    show abErr 10 α h f t₀ y₀_non y (0 + (j : ℕ)) ≤ ε₀
    unfold abErr
    fin_cases j
    · show |abIter 10 α h f t₀ y₀_non 0
          - y (t₀ + ((0 + (((0 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]; exact he0_bd
    · show |abIter 10 α h f t₀ y₀_non 1
          - y (t₀ + ((0 + (((1 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]; exact he1_bd
    · show |abIter 10 α h f t₀ y₀_non 2
          - y (t₀ + ((0 + (((2 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]; exact he2_bd
    · show |abIter 10 α h f t₀ y₀_non 3
          - y (t₀ + ((0 + (((3 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 10) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]; exact he3_bd
    · show |abIter 10 α h f t₀ y₀_non 4
          - y (t₀ + ((0 + (((4 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter4]
      have hval4 : ((4 : Fin 10) : ℕ) = 4 := rfl
      have : ((0 + (((4 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval4]; push_cast; ring
      rw [this]; exact he4_bd
    · show |abIter 10 α h f t₀ y₀_non 5
          - y (t₀ + ((0 + (((5 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter5]
      have hval5 : ((5 : Fin 10) : ℕ) = 5 := rfl
      have : ((0 + (((5 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval5]; push_cast; ring
      rw [this]; exact he5_bd
    · show |abIter 10 α h f t₀ y₀_non 6
          - y (t₀ + ((0 + (((6 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter6]
      have hval6 : ((6 : Fin 10) : ℕ) = 6 := rfl
      have : ((0 + (((6 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 6 := by
        rw [hval6]; push_cast; ring
      rw [this]; exact he6_bd
    · show |abIter 10 α h f t₀ y₀_non 7
          - y (t₀ + ((0 + (((7 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter7]
      have hval7 : ((7 : Fin 10) : ℕ) = 7 := rfl
      have : ((0 + (((7 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 7 := by
        rw [hval7]; push_cast; ring
      rw [this]; exact he7_bd
    · show |abIter 10 α h f t₀ y₀_non 8
          - y (t₀ + ((0 + (((8 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter8]
      have hval8 : ((8 : Fin 10) : ℕ) = 8 := rfl
      have : ((0 + (((8 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 8 := by
        rw [hval8]; push_cast; ring
      rw [this]; exact he8_bd
    · show |abIter 10 α h f t₀ y₀_non 9
          - y (t₀ + ((0 + (((9 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter9]
      have hval9 : ((9 : Fin 10) : ℕ) = 9 := rfl
      have : ((0 + (((9 : Fin 10) : ℕ) : ℕ) : ℕ) : ℝ) = 9 := by
        rw [hval9]; push_cast; ring
      rw [this]; exact he9_bd
  have hres_gen : ∀ n : ℕ, n < N →
      |abResidual 10 α h y t₀ n| ≤ C * h ^ (10 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 10 ≤ (N : ℝ) + 9 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn10_le : ((n : ℝ) + 10) * h ≤ T := by
      have hmul : ((n : ℝ) + 10) * h ≤ ((N : ℝ) + 9) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn10_le
    have hLTE_eq := ab10_localTruncationError_eq h (t₀ + (n : ℝ) * h) y
    have hbridge := ab10Residual_eq_abResidual h y t₀ n
    have hpow : C * h ^ (10 + 1) = C * h ^ 11 := by norm_num
    rw [hα_def, ← hbridge]
    have hreshape :
        h * ((30277247 / 7257600) * deriv y (t₀ + (n : ℝ) * h + 9 * h)
              - (104995189 / 7257600) * deriv y (t₀ + (n : ℝ) * h + 8 * h)
              + (265932680 / 7257600) * deriv y (t₀ + (n : ℝ) * h + 7 * h)
              - (454661776 / 7257600) * deriv y (t₀ + (n : ℝ) * h + 6 * h)
              + (538363838 / 7257600) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              - (444772162 / 7257600) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              + (252618224 / 7257600) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              - (94307320 / 7257600) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              + (20884811 / 7257600) * deriv y (t₀ + (n : ℝ) * h + h)
              - (2082753 / 7257600) * deriv y (t₀ + (n : ℝ) * h))
          = h * (30277247 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 9 * h)
                - 104995189 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 8 * h)
                + 265932680 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 7 * h)
                - 454661776 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 6 * h)
                + 538363838 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 5 * h)
                - 444772162 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 4 * h)
                + 252618224 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 3 * h)
                - 94307320 / 7257600 * deriv y (t₀ + (n : ℝ) * h + 2 * h)
                + 20884811 / 7257600 * deriv y (t₀ + (n : ℝ) * h + h)
                - 2082753 / 7257600 * deriv y (t₀ + (n : ℝ) * h)) := by ring
    rw [hreshape, ← hLTE_eq]
    linarith [hres, hpow.symm.le, hpow.le]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 9) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 9 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic (p := 10) hs α hh.le hL hC_nn hf t₀
      y₀_non y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 10 α L = (172570 / 567) * L from by
    rw [hα_def]; exact abLip_ab10GenericCoeff L] at hgeneric
  have hwindow_ge : abErr 10 α h f t₀ y₀_non y N
      ≤ abErrWindow hs α h f t₀ y₀_non y N := by
    show abErr 10 α h f t₀ y₀_non y (N + ((⟨0, hs⟩ : Fin 10) : ℕ))
        ≤ abErrWindow hs α h f t₀ y₀_non y N
    unfold abErrWindow
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 10 => abErr 10 α h f t₀ y₀_non y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIter 10 α h f t₀ y₀_non N
        = ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N := by
    rw [hα_def, hy_non_def]
    exact (ab10Iter_eq_abIter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N).symm
  have habsErr :
      abErr 10 α h f t₀ y₀_non y N
        = |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N
            - y (t₀ + (N : ℝ) * h)| := by
    show |abIter 10 α h f t₀ y₀_non N - y (t₀ + (N : ℝ) * h)|
        = |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N
            - y (t₀ + (N : ℝ) * h)|
    rw [hbridge]
  show |ab10Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ N
        - y (t₀ + (N : ℝ) * h)|
      ≤ Real.exp ((172570 / 567) * L * T) * ε₀
        + T * Real.exp ((172570 / 567) * L * T) * C * h ^ 10
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
