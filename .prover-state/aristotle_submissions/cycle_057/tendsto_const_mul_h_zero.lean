import Mathlib

open scoped NNReal Topology

/-- **Generic `f · h → 0` (cycle 057).**

If `f h → c` (any finite `c`) as `h → 0`, then `(fun h => f h * h) → 0`.

Pure Tendsto/limit fact via `Tendsto.mul` against `Filter.tendsto_id`.
Used by §406D outer assembly to flatten `Cbase(h) · h · k` and
`b(h) · h` in the squeeze step. -/
private lemma tendsto_const_mul_h_zero
    (f : ℝ → ℝ) (c : ℝ)
    (hf : Filter.Tendsto f (nhds 0) (nhds c)) :
    Filter.Tendsto (fun h : ℝ => f h * h) (nhds 0) (nhds 0) := by
  sorry
