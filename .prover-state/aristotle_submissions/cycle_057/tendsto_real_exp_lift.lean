import Mathlib

open scoped NNReal Topology

/-- **Real-exp Tendsto lift (cycle 057).**

If `Tendsto g (nhds 0) (nhds c)`, then
`Tendsto (Real.exp ∘ g) (nhds 0) (nhds (Real.exp c))`.

One-line `(Real.continuous_exp.continuousAt.tendsto).comp hg`-style
fact, or `(tendsto_real_exp_at c).comp hg`. Used by §406D outer
assembly to lift the squeeze through the `exp(b · k · n · h)`
term once `b · k · n · h` has been shown to converge. -/
private lemma tendsto_real_exp_lift
    {g : ℝ → ℝ} {c : ℝ}
    (hg : Filter.Tendsto g (nhds 0) (nhds c)) :
    Filter.Tendsto (fun h : ℝ => Real.exp (g h)) (nhds 0)
      (nhds (Real.exp c)) := by
  sorry
