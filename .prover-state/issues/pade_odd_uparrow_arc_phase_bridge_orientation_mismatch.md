# Issue: Odd up-arrow arc bridge has the opposite endpoint-sign orientation

## Blocker
The next missing local theorem surface is
`padeR_odd_upArrowArcPhaseBridge_of_pos_errorConst`, but the odd up-arrow case
is not a direct wrapper-level mirror of the landed odd down-arrow chain.

For positive error constant near the odd angle
`θ0 = Real.pi / ((↑(n + d) + 1) : ℝ)`, the main-term imaginary part has the
opposite endpoint-sign orientation from the one built into the existing bridge
interface `PadeROrderWebArcPhaseBridgeNearOrigin`.

## Context
The current bridge interface in `OpenMath/PadeOrderStars.lean` expects:

- `0 < Im(...)` at `θ - η`
- `Im(...) < 0` at `θ + η`

The odd-angle main-term formulas already in the file show the opposite pattern
for the up-arrow positive-error case:

- `im_main_term_odd_down_left` gives a factor `(-c) * ... * sin α`
- `im_main_term_odd_down_right` gives `-((-c) * ... * sin α)`

If `c = padePhiErrorConst n d > 0`, then:

- the `θ0 - η` endpoint is negative
- the `θ0 + η` endpoint is positive

So the existing `PadeROrderWebArcPhaseBridgeNearOrigin` orientation matches the
odd down-arrow negative-error case, but not the odd up-arrow positive-error
case.

## What was tried
- Mirrored the down-arrow critical path far enough to land the up-arrow meet
  infrastructure and the even negative-error producer in live code.
- Checked the odd-angle main-term sign formulas against the bridge interface.
- Prepared a sorry-first Aristotle snapshot for the odd positive-error chain:
  `padeR_odd_upArrowUniformRadiusPhaseStrip_of_pos_errorConst`,
  `...ArcEndpointSigns...`, `...ArcPhaseBridge...`,
  `...ConnectedRayConeSupport...`, and
  `...OrderWebSameComponentContinuation...`.

## Possible solutions
- Introduce a theorem-local reversed-sign bridge for the odd up-arrow case and
  derive `PadeROrderWebMeetsRayConeNearOrigin` directly from it.
- Or bypass the old bridge interface entirely and prove
  `padeR_odd_upArrowArcPhaseBridge_of_pos_errorConst` directly as a raw
  `PadeROrderWebMeetsRayConeNearOrigin` theorem, then continue to the connected
  support / same-component layer from there.
- After that local orientation issue is resolved, the remaining up-arrow
  connected-component packaging should mirror the down-arrow chain again.
