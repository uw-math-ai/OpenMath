# Issue: Padé realized down-arrow seam lacks branch-tracking input

## Blocker
The first genuinely missing input for
`Nonempty (RealizedDownArrowInfinityBranch (padeR n d))` is
`BranchTracksRayNearOrigin`, not `EscapesEveryClosedBall`.

The current down-arrow existence seam only proves
`Nonempty (GlobalDownArrowBranch (padeR n d))`, and that proof is obtained from
`padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos`, whose support
is the trivial set `{0}`. A `{0}`-supported global branch does not supply any
local ray-tracking statement, so the realized-branch upgrade is blocked before
the far-field escape condition is even relevant.

## Context
Relevant live theorems in `OpenMath/PadeOrderStars.lean`:

- `padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos`
- `padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos`
- `PadeRDownArrowBranchTrackingInput`
- `PadeRInfinityBranchExistenceInput`

Relevant definitions in `OpenMath/OrderStars.lean`:

- `GlobalDownArrowBranch`
- `BranchTracksRayNearOrigin`
- `EscapesEveryClosedBall`
- `RealizedDownArrowInfinityBranch`

The current `GlobalDownArrowBranch` witness remembers only:

- connected support on `orderWeb (padeR n d)`,
- `0 ∈ closure support`,
- a tangent angle with `IsDownArrowDir`.

It does not provide a theorem that the support meets every cone
`rayConeNearOrigin θ aperture radius`.

## What was tried
- Re-read the realized-branch definitions in `OrderStars.lean`.
- Confirmed that the existing Padé support theorem is purely bookkeeping and
  returns support `{0}`.
- Checked whether either realized-branch field follows from the live Padé
  hypotheses.
- Refactored the seam to name the first missing field explicitly via
  `PadeRTrackedDownArrowBranch`,
  `PadeRTrackedDownArrowInfinityWitnessFamily`, and
  `PadeRDownArrowBranchTrackingInput`.

## Possible solutions
- Prove a new theorem-local Padé input of the form
  `0 < data.downArrowsAtInfinity → Nonempty (PadeRTrackedDownArrowBranch n d)`.
- More concretely, show that some counted Padé down-arrow branch has support
  meeting every sufficiently small cone around its tangent ray.
- Only after that local tracking theorem exists should the next seam target be a
  separate far-field theorem supplying `EscapesEveryClosedBall`.
