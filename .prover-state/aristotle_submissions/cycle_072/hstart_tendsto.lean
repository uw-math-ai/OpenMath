import Mathlib

open scoped Topology

/-! # Cycle 072 — `hstart_tendsto` for `thm:405A`

Self-contained Aristotle submission for the lone remaining sorry in
`Section405.lean:145` inside `convergent_isStable`.

Mathematical content: given an unbounded `ζ : ℕ → ℝ` (more precisely,
`Tendsto ζ atTop atTop`), the piecewise function

  start h := if 0 < h then c / ζ (Nat.ceil (1 / h)) else 0

tends to `0` as `h → 0` (two-sided).

The argument:
* Right tail (`h > 0`): `1/h → ∞`, so `Nat.ceil (1/h) → ∞`, so
  `ζ (Nat.ceil (1/h)) → ∞`, so `c / ζ (Nat.ceil (1/h)) → 0`.
* Left tail (`h ≤ 0`): the if-branch is `else`, so `start h = 0`.
* Combine via `nhdsWithin_Iic_sup_Ioi`-style decomposition.
-/

namespace AristotleCycle072

/-- Helper used in cycle 072: a piecewise quotient by an
unbounded denominator tends to 0. -/
theorem const_div_unbounded_at_zero
    (ζ : ℕ → ℝ) (hζ_atTop : Filter.Tendsto ζ Filter.atTop Filter.atTop)
    (c : ℝ) :
    Filter.Tendsto
      (fun h : ℝ => if 0 < h then c / ζ (Nat.ceil (1 / h)) else 0)
      (nhds 0) (nhds 0) := by
  sorry

end AristotleCycle072
