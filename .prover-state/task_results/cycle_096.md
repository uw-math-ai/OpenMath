# Cycle 096 Results

## Worked on
Closed the last sorry in the codebase: `PicardLindelof.exists_solution` (general case where `L * (b - a) ≥ 1`).

## Approach
Incorporated the Aristotle result `da85ce79` which provided a complete, sorry-free proof via bisection induction.

The proof structure:
1. **`exists_solution_short`** — local existence when `L * (b - a) < 1`, taking `a ≤ b` (not `a < b`). Constructs `IsPicardLindelof` data and applies `exists_eq_forall_mem_Icc_hasDerivWithinAt₀`.
2. **`exists_solution_concat`** — glues solutions on `[a,c]` and `[c,b]` into `[a,b]` using a piecewise function `fun t => if t ≤ c then y t else z t`. Proves continuity via `ContinuousOn.if` and derivatives by case analysis at the junction point.
3. **`exists_solution_induct`** — induction on `n : ℕ` where `L * (b - a) < n + 1`. Base case uses `exists_solution_short`, inductive step bisects at midpoint and applies `exists_solution_concat`.
4. **`exists_solution`** — obtains `n` from `exists_nat_gt`, delegates to `exists_solution_induct`.

Also added `IsLipschitzInSecondVar.mono_Icc` for restricting the Lipschitz condition to sub-intervals.

## Result
SUCCESS — The project is now completely sorry-free.

All files compile. `OpenMath/PicardLindelof.lean` has only harmless linter warnings (unused simp args, unused variables in the original `exists_solution_small` which is kept for reference).

## Dead ends
None — the Aristotle proof compiled on first attempt.

## Discovery
- `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` is the clean API for local existence, simpler than the `exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn` used in the original `exists_solution_small`.
- The bisection approach (halving the interval) is cleaner than a uniform grid subdivision — it avoids needing to track grid points and works naturally with induction.
- `grind +locals` and `simp +decide` from the Aristotle proof work in Lean 4.28.0.

## Suggested next approach
- The project is sorry-free. Consider:
  1. Moving to the next chapter/section in Iserles
  2. Cleaning up linter warnings
  3. Removing the now-redundant `exists_solution_small` (the new `exists_solution_short` subsumes it)
  4. Adding more theorems from Iserles Chapter 1
