import OpenMath.Basic

/-!
# Theorem 213A: Convergence of the Euler Method

The Euler method has order-1 convergence: when the local truncation error per unit
time is C = M·h (proportional to stepsize), the Gronwall bound from Theorem 212A
is O(h), proving convergence as h → 0.

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 1.1, Theorem 213A.
-/

open Finset Real Filter Topology

/-! ## Part 1: Gronwall bound algebra — substituting C = M·h -/

/-- When L > 0 and initial error is zero, gronwallBound 0 L (M*h) T = (M/L)(e^{LT}-1)·h.
This shows the error bound is linear in h (first-order convergence). -/
theorem gronwallBound_linear_in_h_pos (L T M h : ℝ) (hL_pos : 0 < L) :
    gronwallBound 0 L (M * h) T = M / L * (exp (L * T) - 1) * h := by
  simp [gronwallBound_of_K_ne_0 (ne_of_gt hL_pos)]; ring

/-- When L = 0 and initial error is zero, gronwallBound 0 0 (M*h) T = M·T·h.
This shows the error bound is linear in h. -/
theorem gronwallBound_linear_in_h_zero (T M h : ℝ) :
    gronwallBound 0 0 (M * h) T = M * T * h := by
  simp [gronwallBound_K0]; ring

/-- **Theorem 213A (order of convergence).** The Euler method is first-order convergent:
there exists K ≥ 0 (depending on L, T, M but not h) such that
gronwallBound 0 L (M·h) T ≤ K·h for all h ≥ 0.

This is the textbook statement: the global error is O(h), so h → 0 implies error → 0. -/
theorem euler_convergence_order1 (L T M : ℝ)
    (hL_nonneg : 0 ≤ L) (hT_nonneg : 0 ≤ T) (hM_nonneg : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 ≤ h →
    gronwallBound 0 L (M * h) T ≤ K * h := by
  rcases eq_or_lt_of_le hL_nonneg with rfl | hL_pos
  · -- Case L = 0: use K = M * T
    exact ⟨M * T, mul_nonneg hM_nonneg hT_nonneg, fun h hh => by
      exact le_of_eq (gronwallBound_linear_in_h_zero T M h)⟩
  · -- Case L > 0: use K = M / L * (exp(L*T) - 1)
    refine ⟨M / L * (exp (L * T) - 1), ?_, fun h hh => ?_⟩
    · -- K ≥ 0
      apply mul_nonneg
      · exact div_nonneg hM_nonneg (le_of_lt hL_pos)
      · linarith [Real.one_le_exp (mul_nonneg (le_of_lt hL_pos) hT_nonneg)]
    · -- bound ≤ K * h
      rw [gronwallBound_linear_in_h_pos L T M h hL_pos]

/-! ## Part 2: Convergence as a limit -/

/-- As δ → 0 and ε → 0, gronwallBound δ L ε T → 0. -/
theorem gronwallBound_tendsto_zero_seq (L T : ℝ) (hL_nonneg : 0 ≤ L)
    (δ ε : ℕ → ℝ)
    (hδ : Tendsto δ atTop (nhds 0))
    (hε : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n => gronwallBound (δ n) L (ε n) T) atTop (nhds 0) := by
  rcases eq_or_lt_of_le hL_nonneg with rfl | hL_pos
  · -- L = 0: gronwallBound δ_n 0 ε_n T = δ_n + ε_n * T
    simp_rw [gronwallBound_K0]
    have : Tendsto (fun n => δ n + ε n * T) atTop (nhds (0 + 0 * T)) :=
      hδ.add (hε.mul_const T)
    simpa using this
  · -- L > 0: gronwallBound δ_n L ε_n T = δ_n * exp(L*T) + ε_n/L * (exp(L*T) - 1)
    simp_rw [gronwallBound_of_K_ne_0 (ne_of_gt hL_pos)]
    have : Tendsto (fun n => δ n * exp (L * T) + ε n / L * (exp (L * T) - 1))
        atTop (nhds (0 * exp (L * T) + 0 / L * (exp (L * T) - 1))) :=
      (hδ.mul_const _).add ((hε.div_const _).mul_const _)
    simpa using this

/-- Corollary: if step sizes h_n → 0 and initial errors δ_n → 0, the
Gronwall bound → 0 (convergence of the Euler method). -/
theorem euler_convergence_tendsto (L T M : ℝ) (hL_nonneg : 0 ≤ L)
    (δ : ℕ → ℝ) (hseq : ℕ → ℝ)
    (hδ_lim : Tendsto δ atTop (nhds 0))
    (hh_lim : Tendsto hseq atTop (nhds 0)) :
    Tendsto (fun n => gronwallBound (δ n) L (M * hseq n) T) atTop (nhds 0) := by
  have h1 : Tendsto (fun n => M * hseq n) atTop (nhds 0) := by
    simpa using hh_lim.const_mul M
  exact gronwallBound_tendsto_zero_seq L T hL_nonneg δ _ hδ_lim h1
