import Mathlib

open scoped NNReal Topology

/-- **Positivity of the `bOf` limit (cycle 062, helper for §406D).**

The limit of `bOf M Θ L h` as `h → 0` is
`(Θ + 1) · L · (|β 0| · Σ|α(i+1)| + Σ|β(i+1)|) + 1`. The trailing
`+ 1` makes positivity unconditional given `Θ, L ≥ 0`. Used by
`globalError_outer_squeeze_c_term` which needs `0 < bInf` to divide
by `bInf · k`. -/
private lemma bOf_limit_pos
    {k : ℕ} (α β : Fin (k + 1) → ℝ) (Θ L : ℝ)
    (hΘ_nn : 0 ≤ Θ) (hL : 0 ≤ L) :
    0 < (Θ + 1) *
            (L * (|β 0| * (∑ i : Fin k, |α i.succ|)
                  + ∑ i : Fin k, |β i.succ|))
          + 1 := by
  sorry
