# Issue: Picard-Lindelof subdivision and gluing still blocks global existence

## Blocker
`PicardLindelof.exists_solution` is no longer blocked on local existence. The remaining blocker is the finite subdivision argument for the case `¬ (L * (b - a) < 1)`: construct local solutions on short intervals, prove adjacent pieces agree at shared endpoints, and glue them into one function on `Icc a b` with both `ContinuousOn` and `HasDerivWithinAt`.

## Context
- File: `OpenMath/PicardLindelof.lean`
- Current state:
  - `exists_solution_small` is proved and compiles.
  - `exists_solution` now has a solved small-interval branch and one remaining `sorry` in the general branch.
- Relevant Mathlib API:
  - `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`
  - `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`
  - `ODE_solution_unique_of_mem_Icc_right` / local wrapper `PicardLindelof.unique`

## What was tried
- Searched Mathlib for a direct global existence theorem under the current hypotheses. None was found.
- Proved the short-interval case directly in Lean using `IsPicardLindelof`.
- Submitted Aristotle jobs for:
  - subdivision count,
  - grid-point membership,
  - piecewise gluing,
  - full chaining.
- After the required 30-minute wait:
  - arithmetic jobs completed,
  - the gluing job completed but used `maxHeartbeats 800000`,
  - the full chaining job was still in progress.

## Possible solutions
- Add a small family of helper lemmas to support a recursive construction:
  - choose `N > 0` with `L * ((b - a) / N) < 1`,
  - define `x_k = a + k * h`,
  - prove `x_k ∈ Icc a b` and `x_k ≤ x_{k+1}`.
- Build local solutions on `[x_k, x_{k+1}]` recursively, taking the previous endpoint value as the next initial value.
- Use `PicardLindelof.unique` on each overlap to prove the endpoint match needed for gluing.
- For the final assembly, prefer a finite recursive/piecewise definition over a single large `if` chain, and split derivative gluing into endpoint and interior lemmas to stay under heartbeat limits.
