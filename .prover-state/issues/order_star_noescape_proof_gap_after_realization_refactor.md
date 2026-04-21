# Issue: No-escape proof still lacks the analytic contradiction after the realization refactor

## Blocker
After cycle 272 introduced `RealizesInfinityCounts R data`, the no-infinity seam in
`OpenMath/OrderStars.lean` is now statement-correct, but the remaining proofs still
lack the actual contradiction that rules out a concrete escaping order-web branch.

The stuck theorems are:
- `noDownArrowEscapesToInfinity_of_rationalApprox`
- `noUpArrowEscapesToInfinity_of_rationalApprox`

Each theorem now reduces to extracting a witness branch from
`RealizesInfinityCounts R data` and then proving that the resulting
`EscapesEveryClosedBall` hypothesis is impossible. The repo still has no theorem
that supplies that contradiction.

## Context
- `IsRationalApproxToExp data` now carries only:
  - `order_le`
  - `localRegularity`
- `RealizesInfinityCounts R data` only says that every counted infinity endpoint is
  witnessed by a concrete global branch of `orderWeb R` escaping every closed ball.
- The proof shape in both no-escape theorems is now:
  1. assume the infinity count is nonzero,
  2. choose `i : Fin data.downArrowsAtInfinity` or `Fin data.upArrowsAtInfinity`,
  3. extract `⟨branch, hescape⟩` from the realization structure,
  4. derive a contradiction from `hescape`.

Step 4 is the missing mathematics.

## What was tried
- Inspected the cycle-271 Aristotle outputs. All four completed outputs were rejected
  because they introduced forbidden surrogate fields such as:
  - `branch.dichotomy`
  - `branch.converges_in_alexandroff`
  - `branch.isBounded`
- Refactored the live file so the no-escape theorems are count-level and mention the
  `R ↔ data` bridge explicitly.
- Submitted a new cycle-272 Aristotle batch on the refactored statements. On the
  one allowed refresh this cycle, those jobs were still queued or in progress.

## Possible solutions
- Prove a concrete theorem for the relevant rational-approximation order web saying
  that a counted infinity witness branch cannot satisfy `EscapesEveryClosedBall`.
- If one additional bridge theorem is needed, add a single theorem connecting the
  rational-approximation asymptotics of `R` to the extracted branch witness. Do not
  hide the gap inside a larger axiom bundle or extra structure fields.
