# Cycle 606 Results

## Worked on

Pivoted off the §38 `bSeriesConvAug` unital associativity depth ladder
(six consecutive low-value cycles per the strategy) and landed
**Butcher §250 — Taylor series methods** as a fresh tracked module
`OpenMath/TaylorSeriesMethod.lean`.

## Approach

Followed the strategy verbatim:

1. Confirmed `OpenMath/OneStepConvergence.lean` exposes `OneStepMethod`
   at the file-top (no enclosing namespace) with `IsConsistent` inside
   `namespace OneStepMethod`. The `import OpenMath.OneStepConvergence`
   line in the new module suffices; no namespace gymnastics needed.
2. Confirmed there is no umbrella `OpenMath.lean` import for
   `OneStepConvergence`, so the new sibling module also stays out of
   the umbrella per strategy guidance.
3. Wrote the four-declaration scaffold (`increment`, `toOneStepMethod`,
   `increment_one`, `increment_two`, `isConsistent_of_first_derivative`)
   with `sorry` for each proof body and verified it compiled with
   `lake env lean OpenMath/TaylorSeriesMethod.lean`.
4. Closed the three sorrys one at a time, re-checking the file after
   each edit.

## Result

SUCCESS — `OpenMath/TaylorSeriesMethod.lean` compiles cleanly with
**zero sorrys and zero warnings**.

Final proof bodies:

- `increment_one`: `simp [increment, Nat.factorial]`. The
  `Finset.sum_range_one` rewrite suggested by the strategy was unused
  (the simp normal form already collapses `range 1` summands), so it
  was dropped to silence the `unusedSimpArgs` linter.
- `increment_two`:
  `simp [increment, Finset.sum_range_succ, Nat.factorial]; norm_num`.
  The `simp` peels both summands and reduces the factorials; `norm_num`
  then turns the residual `(h / (1 + 1)) • D 2 x y` into
  `(h / 2) • D 2 x y`.
- `isConsistent_of_first_derivative`: pattern `p = q + 1` via
  `Nat.exists_eq_succ_of_ne_zero`, then
  `Finset.sum_range_succ'` peels off the `k = 0` summand at the front,
  leaving a tail `Finset.sum_eq_zero` argument that all
  `(0^(k+1) / (k+2)!) • D (k+2) x y` summands vanish by
  `zero_pow (Nat.succ_ne_zero _)`. The remaining head simplifies via
  `Nat.factorial` and the `D 1 = f` hypothesis.

## Dead ends

None this cycle — every proof landed on the first or second attempt
because the strategy already laid out the concrete close-out steps.
The only minor adjustment was dropping the unused
`Finset.sum_range_one` simp lemma in `increment_one` after Lean's
`unusedSimpArgs` linter pointed it out.

## Discovery

`Finset.sum_range_succ'` is the cleanest tool for "peel off the
`k = 0` summand from `range (q + 1)`": it leaves a tail
`∑ k ∈ range q, f (k + 1)` plus the `k = 0` head, which is exactly the
structure needed when proving things about Taylor sums whose first
term is the dominant one. Worth remembering for §254 follow-up.

## Suggested next approach

Two natural follow-ups, in priority order:

1. **§254 The use of f-derivatives.** Build the recursion
   `y^{(k+1)} = (∂_x + f · ∂_y) y^{(k)}` for sufficiently smooth `f`,
   yielding a concrete `D : ℕ → ℝ → E → E` for each ODE. This is the
   missing piece that connects the abstract `TaylorSeriesMethod` to
   actual specific-`f` consistency / order arguments in Lean. It
   needs Mathlib `iteratedFDeriv` and `ContDiff` plumbing; not trivial
   but well-scoped.
2. **Order-`p` Taylor LTE bound.** Once §254 is in place, prove that
   when `y` solves `y' = f(x, y)` and `f` is `C^p` enough,
   `localTruncationError (toOneStepMethod p D) y x h = O(h^p)`. This
   would give the standard order theorem for Taylor methods and slot
   directly into `one_step_global_error_bound_exp` for a full
   convergence statement.

§38 should remain paused until someone schedules a dedicated cycle for
the cut-associativity Hopf identity (option 1 in
`section386aug_strong_induction_obstruction.md`). Adding more
depth-ladder shapes is busywork.
