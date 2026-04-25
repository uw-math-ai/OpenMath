import OpenMath.LMMAB3Convergence

/-! Cycle 418, Job E: uniform AB3 local residual bound on a finite
horizon `[t₀, t₀ + T]`, given a `C^4` solution `y`.

Mirror of `ab2_local_residual_bound` from
`OpenMath/LMMAB2Convergence.lean` (lines 498–535). Use the `ab3_pointwise
_residual_bound` algebraic identity (Job D), the `iteratedDeriv_four
_bounded_on_Icc` uniform `M`-bound (Job A), the AB3 LTE rewrite
`ab3_localTruncationError_eq` already in `OpenMath.LMMAB3Convergence`,
and restrict `h ≤ 1` so that `t + 3h ∈ [t₀, t₀ + T + 1]` whenever
`(n + 3) * h ≤ T`. Constants: `(C, δ) = (7 * M, 1)` (matching Job D's
over-estimate). -/

namespace LMM

theorem cycle418_ab3_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 3) * h ≤ T →
        |adamsBashforth3.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 4 := by
  sorry

end LMM
