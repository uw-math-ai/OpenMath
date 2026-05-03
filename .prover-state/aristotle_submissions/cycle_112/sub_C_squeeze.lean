import Mathlib

/-! Cycle 112 — Aristotle batch for `aux_515D_output_tendsto` (Butcher §515D).

Self-contained file with sub-lemma C: the **squeeze step** of the
discrete-Grönwall convergence argument.

Given the closed-form Grönwall bound
  `δ n ≤ exp(α · Δx) · δ0_seq n + (exp(α · Δx) - 1) · (β · Δx / n / α)`
(from sub-lemma B, which feeds into sub-lemma C), and `δ0_seq → 0`
(from the starting-procedure consistency `hφ`), conclude
`δ n → 0` as `n → ∞`.

This is pure Mathlib Tendsto plumbing — `squeeze_zero` plus
`tendsto_one_div_atTop_nhds_zero_nat` plus `Tendsto.const_mul`.
-/

open Filter Topology

namespace AristotleBatch112

/-- **Sub-lemma C** — squeeze argument for the discrete-Grönwall bound.

If `δ n ≥ 0` and `δ` is bounded above by `exp(α·Δx)·δ0_seq n + (exp(α·Δx)-1)·(β·Δx/n/α)`,
where `δ0_seq → 0` and `α > 0`, then `δ n → 0`. -/
theorem aux_515D_squeeze
    {α β : ℝ} (hα_pos : 0 < α) (hβ_nn : 0 ≤ β)
    (Δx : ℝ) (hΔx_pos : 0 < Δx)
    (δ : ℕ → ℝ) (δ0_seq : ℕ → ℝ)
    (hδ_nn : ∀ n, 0 ≤ δ n)
    (hδ0_tendsto : Filter.Tendsto δ0_seq Filter.atTop (nhds 0))
    (h_bound : ∀ n : ℕ, 0 < n →
      δ n ≤ Real.exp (α * Δx) * δ0_seq n
            + (Real.exp (α * Δx) - 1) * (β * (Δx / (n : ℝ)) / α)) :
    Filter.Tendsto δ Filter.atTop (nhds 0) := by
  sorry

end AristotleBatch112
