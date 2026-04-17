# Issue: Cycle 087 Dahlquist Barrier Blockers

## Blocker
- `hGtCancelled` is reduced to a C₃ reversed-polynomial derivative identity that is not yet proved in Lean.
- `continuousOn_Gtilde_closedBall` appears unprovable from the current hypotheses because `rhoC` may have unit-circle roots other than `1`, creating denominator zeros on the boundary.

## Context
- File: `OpenMath/MultistepMethods.lean`
- Current remaining sorrys are in the Dahlquist barrier section.
- The derivative proof now has the following local chain available:
  `Qpoly = Q₃`
  `Q₃.eval 1 = Q₂.derivative.eval 1`
  `Q₂.derivative.eval 1 = Q₁.derivative.derivative.eval 1 / 2`
- Missing step:
  `Q₁.derivative.derivative.eval 1 = -m.rhoCDeriv 1 / 3`
  via a new helper `reversed_poly_C3_condition`.

## What was tried
- Mirrored the existing `reversed_poly_C2_condition` proof structure and inserted a `reversed_poly_C3_condition` skeleton.
- Decomposed `hGtCancelled` into quotient-rule and factor-chain helper steps.
- Submitted 5 Aristotle jobs on the updated file, including the full derivative theorem and the missing C₃ helper.
- Per workflow, checked once later; all jobs were still `QUEUED`.

## Possible solutions
- Prove `reversed_poly_C3_condition` by expanding third derivatives at `1`, reindexing through `Fin.rev`, and combining `orderCondVal 3 = 0` with the lower-order consistency identities exactly as in the C₂ lemma.
- Once that identity is available, finish the scalar reduction in `hGtCancelled` and then simplify the quotient-rule derivative using `convert` or `simpa`.
- Strengthen `continuousOn_Gtilde_closedBall` with the hypothesis that any unit-circle root of `rhoC` is `1`, or derive that fact separately from the analytic stability assumptions before reattempting continuity on the closed disk.
