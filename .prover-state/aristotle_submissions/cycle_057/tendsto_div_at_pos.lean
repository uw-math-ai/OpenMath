import Mathlib

open scoped NNReal Topology

/-- **`f / g → 0` when `f → 0`, `g → c > 0` (cycle 057).**

If `Tendsto f (nhds 0) (nhds 0)` and `Tendsto g (nhds 0) (nhds c)`
with `c > 0`, then `Tendsto (fun h => f h / g h) (nhds 0) (nhds 0)`.

Standard `Tendsto.div`-flavoured fact. The hypothesis `c > 0` ensures
`c ≠ 0`, so the quotient is continuous on a neighborhood of `h = 0`.
Used by §406D outer assembly to bound `c · h / (b · k)` in the
squeeze: as `h → 0` the numerator vanishes while the denominator
tends to a strictly positive limit. -/
private lemma tendsto_div_at_pos
    {f g : ℝ → ℝ} {c : ℝ}
    (hf : Filter.Tendsto f (nhds 0) (nhds 0))
    (hg : Filter.Tendsto g (nhds 0) (nhds c))
    (hc : 0 < c) :
    Filter.Tendsto (fun h : ℝ => f h / g h) (nhds 0) (nhds 0) := by
  sorry
