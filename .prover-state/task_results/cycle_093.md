# Cycle 093 Results

## Worked on
- `OpenMath/Stiffness.lean`
- `def:112A` one-sided Lipschitz condition
- `thm:112B` exponential bound on solution differences
- Supporting lemmas: `lipschitzWith_implies_oneSidedLipschitz`, `oneSidedLipschitz_nonpos_implies_contractive`

## Approach
- Added a new stiffness file over real inner product spaces.
- Used the sorry-first workflow to lay out five proof obligations and verified the skeleton with `lake env lean OpenMath/Stiffness.lean`.
- Submitted five Aristotle jobs targeting the five sorry sites:
  - `6c151f42-536a-41c0-991c-343671e0f458`
  - `e87e0c66-50ee-4c23-af20-7f1e3cfcba98`
  - `a958d9ac-4d70-4a47-a88f-82c3c8720bf6`
  - `36e5d061-84fe-4614-8c3f-fd15dd5e6014`
  - `75b314d9-824b-48e4-bea1-007983b98dd5`
- Proved the results manually by defining the weighted energy
  `exp (-2 l (x - x0)) * ‖y x - z x‖^2`, showing its derivative is nonpositive on the interval,
  using `antitoneOn_of_hasDerivWithinAt_nonpos`, then extracting the textbook exponential bound.

## Result
- SUCCESS
- `OpenMath/Stiffness.lean` now compiles sorry-free.
- `plan.md` was updated to mark the Chapter 3 stiffness definition target complete.
- `extraction/formalization_data/lean_status.json` now marks `def:112A` and `thm:112B` as formalized.

## Dead ends
- The existing Mathlib Gronwall API is set up for bounds of the form `‖u'‖ ≤ K‖u‖ + ε`, which does not directly match the one-sided inner-product inequality.
- A direct Gronwall proof was more awkward than the weighted-energy monotonicity argument.

## Discovery
- The clean Lean proof route is:
  1. Differentiate `‖y - z‖^2` via `HasDerivAt.inner`.
  2. Differentiate the weighted quantity `exp (-2 l (x - x0)) * ‖y - z‖^2`.
  3. Prove antitonicity on `Icc x0 x1` using `antitoneOn_of_hasDerivWithinAt_nonpos`.
  4. Convert the squared estimate back to a norm estimate with `le_of_sq_le_sq`.
- Aristotle status after a single refresh:
  - `e87e0c66-50ee-4c23-af20-7f1e3cfcba98`: `COMPLETE`
  - `6c151f42-536a-41c0-991c-343671e0f458`: `COMPLETE_WITH_ERRORS`
  - `a958d9ac-4d70-4a47-a88f-82c3c8720bf6`: `IN_PROGRESS`
  - `36e5d061-84fe-4614-8c3f-fd15dd5e6014`: `IN_PROGRESS`
  - `75b314d9-824b-48e4-bea1-007983b98dd5`: `IN_PROGRESS`
- No Aristotle output was incorporated because the manual proofs had already closed all sorrys before the jobs completed.

## Suggested next approach
- Move to the next planner target: the one-step convergence theorem from Section 1.3.
- If Chapter 3 is extended next, build on `OpenMath/Stiffness.lean` rather than redoing the perturbation estimate infrastructure.
