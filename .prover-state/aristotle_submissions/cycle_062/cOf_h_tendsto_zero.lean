import Mathlib

open scoped NNReal Topology

/-- **`f(h) · h → 0` lifted (cycle 062, helper for §406D).**

If `f h → c` (any finite `c`) as `h → 0`, then `f h · h → 0`. Same as
`tendsto_const_mul_h_zero` from cycle 057, restated here as an
Aristotle hedge for cycle 062's `cOf · h → 0` use site. -/
private lemma cOf_h_tendsto_zero
    (f : ℝ → ℝ) (c : ℝ)
    (hf : Filter.Tendsto f (nhds 0) (nhds c)) :
    Filter.Tendsto (fun h : ℝ => f h * h) (nhds 0) (nhds 0) := by
  sorry
