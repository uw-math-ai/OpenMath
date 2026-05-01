import Mathlib

open scoped NNReal Topology

/-- **`exp(p h) - 1 → 0` when `p → 0` (cycle 057).**

If `Tendsto p (nhds 0) (nhds 0)`, then
`Tendsto (fun h => Real.exp (p h) - 1) (nhds 0) (nhds 0)`.

Standard combinator: `exp` is continuous so `Real.exp (p h) → exp 0 = 1`,
then subtract 1 to land at 0. Used by §406D outer assembly to bound the
`(exp(b · k · n · h) - 1)` factor when threading the squeeze through
the autonomous closed-form bound. -/
private lemma tendsto_exp_sub_one_at_zero_aux
    {p : ℝ → ℝ} (hp : Filter.Tendsto p (nhds 0) (nhds 0)) :
    Filter.Tendsto (fun h : ℝ => Real.exp (p h) - 1) (nhds 0) (nhds 0) := by
  sorry
