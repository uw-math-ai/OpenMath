# Cycle 278 Results

## Worked on
- `OpenMath/OrderStars.lean`
- `.prover-state/issues/order_star_realized_infinity_branch_contradiction_shape.md`
- `.prover-state/aristotle/cycle_278/01_realizedDownArrowInfinityBranch_contradiction.lean`
- `.prover-state/aristotle/cycle_278/02_realizedUpArrowInfinityBranch_contradiction.lean`
- `.prover-state/aristotle/cycle_278/03_concreteRationalApproxToExp_builder.lean`

## Approach
- Followed the cycle-278 strategy exactly:
  - kept the live `OrderStars` seam unchanged,
  - wrote the new contradiction statements in fresh cycle-278 scratch files,
  - submitted a fresh Aristotle batch,
  - waited once for 30 minutes,
  - checked once,
  - only then decided what was safe to integrate.
- Added only small sorry-free helper lemmas to `OpenMath/OrderStars.lean` that
  directly support the branch contradiction work:
  - `mem_orderWeb_of_mem_globalOrderArrowBranch_support`
  - `exists_mem_support_norm_gt_of_escapesEveryClosedBall`
  - `exists_mem_inter_rayConeNearOrigin_of_branchTracksRayNearOrigin`
  - `exists_mem_support_unit_level_of_connected_orderWeb_branch`
- Used Lean proof search to verify that the connectedness crossing helper closes
  in the live file via `IsPreconnected.intermediate_value`.

## Result
SUCCESS

The live file remains sorry-free and now contains a new helper theorem directly
advancing the concrete contradiction below `ConcreteRationalApproxToExp`:
`exists_mem_support_unit_level_of_connected_orderWeb_branch`.

The cycle-278 scratch batch now records a stable theorem-local hypothesis list
for the down-arrow contradiction, the up-arrow contradiction, and the combined
builder for `ConcreteRationalApproxToExp R data`.

The blocker is narrower than before: the missing work is no longer a generic
connectedness lemma, but deriving the scratch theorem-local analytic hypotheses
from the concrete rational approximation `R`.

## Dead ends
- Aristotle did not return directly incorporable proofs.
  - `3187363b-ba74-497e-a8c9-966db1aa874f`: `COMPLETE_WITH_ERRORS`
  - `6e6eb7ac-2bc5-4667-9411-f1ca5f8e2f8b`: `COMPLETE_WITH_ERRORS`
  - `85dab4bf-8050-4378-9cac-b875e9ef491c`: `COMPLETE_WITH_ERRORS`
- All three returned artifacts rebuilt a parallel `OpenMath/OrderStars.lean`
  interface, so they were rejected as live patches.
- The builder artifact also changed the semantics enough that the contradiction
  became an artifact of the fabricated interface rather than a proof about the
  live seam.

## Discovery
- The connectedness crossing step is not the blocker anymore. In the live file,
  once a branch has one support point with amplitude below `1` and another with
  amplitude above `1`, `IsPreconnected.intermediate_value` yields a support point
  at unit level.
- The real open question is the minimal justified theorem-local hypothesis list
  for the concrete contradiction. The current scratch shape still needs:
  - exclusion of `0` from realized branch support,
  - exclusion of nonzero unit-level points on `orderWeb R`,
  - local cone sign control near realized tangents,
  - far-field sign control on large `orderWeb R` points.

## Suggested next approach
- Work from the cycle-278 scratch theorem shapes directly.
- Try to derive the local cone-control and far-field sign-control assumptions from
  the concrete asymptotics of the actual rational approximation `R`.
- Reassess whether the nonzero/unit-level support exclusions should remain as
  theorem-local assumptions or can be replaced by a more natural concrete
  nondegeneracy statement.
