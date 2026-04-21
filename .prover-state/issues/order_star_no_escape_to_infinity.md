# Issue: Prove `NoArrowsEscapeToInfinity` for global order-star branches

## Blocker
`OpenMath/OrderStars.lean` now separates endpoint bookkeeping from the final 355D
count inequality via `OrderArrowTerminationData` and `NoArrowsEscapeToInfinity`.
The remaining missing step is to prove that the global order-arrow branches counted
there do not contribute any infinity endpoints, so `thm_355D` can be discharged from
topology instead of by hypothesis.

## Context
- The file already has:
  - local ray-direction results (`IsUpArrowDir`, `IsDownArrowDir`)
  - explicit endpoint counts at zeros and poles
  - explicit infinity-endpoint counts in `OrderArrowTerminationData`
  - a reduction lemma
    `satisfiesArrowCountInequality_of_noArrowsEscape`
- What is still absent is the geometric bridge from the order web
  `R(z) * exp(-z) ∈ ℝ_{>0}` to the statement
  `NoArrowsEscapeToInfinity data`.
- Without that bridge, `thm_355D` still depends on an abstract topology field in
  `IsRationalApproxToExp`.

## What was tried
- Replaced the old coarse `arrowTrajectoryComplete : p ≤ ñ + d̃` assumption with a
  sharper interface that records zeros/poles/infinity as separate endpoint classes.
- Rewrote 355D/355E and the downstream Padé/A-stability layer to consume this new
  interface.
- Confirmed that this narrows the remaining gap to one precise statement:
  vanishing of the infinity-endpoint counts.

## Possible solutions
- Prove a local regularity lemma: away from zeros and poles of `R`, the order web is
  a smooth one-dimensional set, so a branch cannot stop at an ordinary finite point.
- Package a global branch as a connected component (or an arc-like parameterized
  subset) of the order web together with its endpoint alternatives: zero, pole, or
  infinity.
- Use compactness on closed balls to show any non-terminating branch with no finite
  singular endpoint must leave every compact set, then derive the needed contradiction
  or endpoint classification for the 355D setup.
