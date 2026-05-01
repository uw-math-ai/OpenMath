import Mathlib

open scoped NNReal Topology

/-- **Real exp is continuous at every point (cycle 055/056 helper).**

Used by §406D outer assembly: the closed-form bound contains
`exp(b · k · n · h)` where `n · h = x − x₀` is constant and `b → b∞`
as `h → 0`. We need `Tendsto exp` at points other than 0 to handle
this. Stated for general `c` for reusability. -/
private lemma tendsto_real_exp_at (c : ℝ) :
    Filter.Tendsto Real.exp (nhds c) (nhds (Real.exp c)) := by
  sorry
