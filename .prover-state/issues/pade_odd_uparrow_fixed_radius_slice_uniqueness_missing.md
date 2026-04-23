# Issue: Odd up-arrow connected support still needs the positive-error fixed-radius slice uniqueness chain

## Blocker
The live odd positive-error up-arrow seam is no longer blocked at the arc
orientation layer: `padeR_odd_upArrowUniformRadiusPhaseStrip_of_pos_errorConst`,
`padeR_odd_upArrowArcEndpointSigns_of_pos_errorConst`, and
`padeR_odd_upArrowOrderWebMeetsRayConeNearOrigin_of_pos_errorConst` now compile
in `OpenMath/PadeOrderStars.lean`.

The next blocker is lower in the connected-support infrastructure. Raw
cone-meeting is not enough to derive
`padeR_odd_upArrowConnectedRayConeSupport_of_pos_errorConst`; the down-arrow
side needed the radius/phase connected-zero-set chain, and the positive-error
up-arrow mirror still lacks the fixed-radius uniqueness/projection step.

The exact new local surface is:
`oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_pos_errorConst`

Its proof in turn needs a positive-error mirror of the main-term variation
estimate:
`main_term_im_diff_bound_of_pos_errorConst`.

## Context
- The relevant existing negative-error chain is:
  - `main_term_im_diff_bound_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst`
  - `padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst`
  - `padeR_odd_downArrowSameComponentRadiusPhaseBound_of_neg_errorConst`
  - `padeR_odd_downArrowConnectedRayConeSupport_of_neg_errorConst`
- The odd-angle radius/phase definitions already exist and are usable:
  - `oddDownArrowRadiusPhaseCenter`
  - `oddDownArrowRadiusPhaseWedge`
  - `oddDownArrowRadiusPhasePoint`
  - `oddDownArrowRadiusPhaseValue`
  - `oddDownArrowRadiusPhaseIm`
  - `oddDownArrowRadiusPhaseZeroSet`
- For the positive-error odd up-arrow case, the true-slice endpoint signs must
  reverse:
  - left endpoint has `Im < 0`
  - right endpoint has `0 < Im`

## What was tried
- Landed the fixed-`η` odd positive-error up-arrow strip theorem from the usable
  Aristotle bundle.
- Derived the endpoint-sign corollary directly from that strip theorem.
- Proved the raw cone-meeting theorem directly by IVT with reversed endpoint
  orientation, without using `PadeROrderWebArcPhaseBridgeNearOrigin`.
- Inspected the down-arrow support path and confirmed it cannot be skipped:
  connected support there comes from the radius/phase connected-zero-set chain,
  not from raw cone witnesses alone.

## Possible solutions
- Mirror `main_term_im_diff_bound_of_neg_errorConst` first, but with the
  positive-error sign orientation.
- Use that to prove
  `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_pos_errorConst`.
- Then continue honestly through:
  - `oddDownArrowRadiusPhaseProjectionNoStop_of_pos_errorConst`
  - `padeR_odd_upArrowConnectedRadiusPhaseZeroSet_of_pos_errorConst`
  - `padeR_odd_upArrowSameComponentRadiusPhaseBound_of_pos_errorConst`
  - `padeR_odd_upArrowConnectedRayConeSupport_of_pos_errorConst`
