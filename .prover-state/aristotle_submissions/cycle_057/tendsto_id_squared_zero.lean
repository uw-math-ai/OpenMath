import Mathlib

open scoped NNReal Topology

/-- **Generic `f · h^2 → 0` (cycle 057).**

If `f h → c` (any finite `c`) as `h → 0`, then `(fun h => f h * h^2) → 0`.

Pure Tendsto/limit fact. Used by §406D outer assembly to handle the
`c · h^2` shape generically — instances include `b · h^2`, `Cbase · h^2`,
`Dbase · h^2`. Two-step combinator: `Tendsto.mul` against
`tendsto_h_squared_zero`, then arithmetic to flatten `c · 0 = 0`. -/
private lemma tendsto_id_squared_zero
    (f : ℝ → ℝ) (c : ℝ)
    (hf : Filter.Tendsto f (nhds 0) (nhds c)) :
    Filter.Tendsto (fun h : ℝ => f h * h ^ 2) (nhds 0) (nhds 0) := by
  sorry
