import Mathlib

open scoped NNReal Topology

/-- **Tendsto of constant-over-affine helper (cycle 055).**

If `c` is a constant and `1 - h · a → 1` (since `h → 0`), then
`c / (1 - h · a) → c`. Used by §406D outer assembly to handle the
`Cbase` and `Dbase` shapes' denominator. -/
private lemma tendsto_const_div_one_sub_mul (c a : ℝ) :
    Filter.Tendsto
      (fun h : ℝ => c / (1 - h * a))
      (nhds 0)
      (nhds c) := by
  sorry
