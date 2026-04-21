# Issue: Order-star finite endpoint classification needs a local regularity theorem

## Blocker
`OpenMath/OrderStars.lean` now exposes ordinary finite nonsingular endpoints as a
separate bucket in `OrderArrowTerminationData`, with the desired theorem boundary
recorded by `FiniteArrowEndpointsClassified`. The missing step is to prove that a
global order-arrow branch cannot terminate at such an ordinary finite point.

## Context
- Cycle 269 refactored the 355D interface so the abstract topology input is split into:
  - `FiniteArrowEndpointsClassified data`
  - `NoArrowsEscapeToInfinity data`
- The bookkeeping theorem
  `satisfiesArrowCountInequality_of_endpointClassification`
  now needs both hypotheses explicitly.
- What is still absent is the local geometric input turning the order web near a
  finite nonsingular point into a smooth arc or equivalent continuation object.

## What was tried
- Added separate counts
  `downArrowsAtOrdinaryFinitePoints` and `upArrowsAtOrdinaryFinitePoints`.
- Rewired `IsRationalApproxToExp` / `thm_355D` so the remaining gap is no longer
  one opaque topology blob.
- Confirmed that the new blocker is exactly the theorem needed to discharge
  `finiteEndpointsClassified`.

## Possible solutions
- Formalize a local nonsingularity predicate for points where the rational factor
  has neither zero nor pole and the order-web defining equation has nonvanishing
  derivative/transverse gradient.
- Prove a local continuation lemma: in a sufficiently small neighborhood of such a
  point, the order web is an embedded arc meeting both sides of the neighborhood,
  so no branch endpoint can occur there.
- Convert that local lemma into a global counting statement showing the ordinary
  finite endpoint counts in `OrderArrowTerminationData` vanish.
