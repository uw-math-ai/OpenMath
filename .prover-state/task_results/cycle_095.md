# Cycle 095 Results

## Worked on
- `OpenMath/PicardLindelof.lean`, specifically `PicardLindelof.exists_solution`
- Small-interval Picard-Lindelof existence helper
- Subdivision/gluing support via Aristotle batch jobs

## Approach
- Read the current strategy and `OpenMath/PicardLindelof.lean`.
- Checked the previously listed Aristotle result directories; they were unrelated to `PicardLindelof.lean`, consistent with the planner note that they were already superseded.
- Searched Mathlib's ODE API and confirmed the usable existence entry points are based on `IsPicardLindelof`.
- Proved a new private helper `exists_solution_small` for the case `L * (b - a) < 1` by:
  - bounding `t ↦ f t y₀` on `Icc a b`,
  - choosing a radius `R = C * (b - a) / (1 - L * (b - a))`,
  - constructing `IsPicardLindelof` with `t₀ = a` and `r = 0`,
  - extracting a solution and `ContinuousOn` from Mathlib's flow theorem.
- Replaced the old monolithic `exists_solution` sorry with a two-branch structure:
  - small-interval branch closed by `exists_solution_small`,
  - general subdivision branch left as the remaining sorry.
- Submitted 5 Aristotle jobs after the sorry-first restructuring:
  - `36cd6ffc-81c3-4441-83df-70ab410df0b1` — small-interval existence
  - `28be6fdd-b7d1-4424-af32-7bc151a77449` — subdivision count
  - `f8fd17f4-dea5-46b0-af9b-7a366ce05bf2` — grid membership
  - `ef7474f5-1f31-4f3f-8ca0-5aa9b477a792` — piecewise gluing
  - `54cb7170-f748-46c1-8dd7-64db449d94ab` — full chaining proof
- Slept 30 minutes, then refreshed status once and inspected the completed outputs.

## Result
- SUCCESS: `exists_solution_small` is now proved in the codebase and `OpenMath/PicardLindelof.lean` compiles.
- PARTIAL: `exists_solution` is decomposed, but the general interval-subdivision branch still has one `sorry`.
- Aristotle status after the mandated wait:
  - `36cd6ffc...` COMPLETE
  - `28be6fdd...` COMPLETE
  - `f8fd17f4...` COMPLETE
  - `ef7474f5...` COMPLETE
  - `54cb7170...` IN_PROGRESS at the time of the single post-wait check

## Dead ends
- There is no hidden global-Lipschitz finite-interval existence wrapper in Mathlib that bypasses the subdivision argument for this theorem statement.
- The Aristotle gluing result used `set_option maxHeartbeats 800000`, which violates project rules, so it was not directly usable.
- The full chaining Aristotle job did not finish within the mandated 30-minute window, so it could not be incorporated this cycle.

## Discovery
- The local existence proof is substantially simpler using
  `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`
  than reconstructing continuity from derivative facts afterward.
- The remaining difficulty is not local existence but the finite recursive assembly of local solutions into a single global function on `Icc a b`.
- Arithmetic support for the subdivision count and grid-point membership is now available in Aristotle outputs and can be ported if needed next cycle.

## Suggested next approach
- Introduce explicit helper lemmas in `OpenMath/PicardLindelof.lean` for:
  - existence of a positive `N` with `L * ((b - a) / N) < 1`,
  - membership of grid points `a + k * h` in `Icc a b`,
  - gluing continuity/derivative data across adjacent subintervals.
- Build the global solution by finite recursion on subinterval index, using `unique` to prove compatibility at joins.
- Avoid any gluing proof that requires `maxHeartbeats > 200000`; if the derivative gluing lemma is expensive, break it into endpoint/interior cases.
