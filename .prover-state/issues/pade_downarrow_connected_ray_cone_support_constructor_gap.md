# Issue: Padé down-arrow raw cone meeting still does not construct connected ray-cone support

## Blocker
The local Padé down-arrow cone work is now in live code for both concrete
parity cases:

- `padeR_even_downArrowArcPhaseBridge_of_pos_errorConst`
- `padeR_odd_downArrowArcPhaseBridge_of_neg_errorConst`
- `padeR_even_downArrowOrderWebMeetsRayConeNearOrigin_of_pos_errorConst`
- `padeR_odd_downArrowOrderWebMeetsRayConeNearOrigin_of_neg_errorConst`
- both corresponding
  `PadeRDownArrowOrderWebArcPhaseBridgeInput_of_*_errorConst` feeders

So the active blocker is no longer the local arc-phase bridge. The next missing
step is still construction of

```lean
Nonempty (PadeRConnectedRayConeOrderWebSupport n d θ)
```

for a concrete down-arrow direction `θ`.

Cycle 327 confirmed that the direct implication

```lean
PadeROrderWebMeetsRayConeNearOrigin n d θ →
Nonempty (PadeRConnectedRayConeOrderWebSupport n d θ)
```

is still underspecified. The live replacement seam is now

```lean
PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d θ
```

meaning: there exists `z0 ∈ orderWeb (padeR n d)` such that the fixed connected
component `connectedComponentIn (orderWeb (padeR n d)) z0` meets every
sufficiently small cone around `θ`.

## Context
Relevant live declarations in `OpenMath/PadeOrderStars.lean`:

- `PadeROrderWebArcPhaseBridgeNearOrigin`
- `PadeROrderWebMeetsRayConeNearOrigin`
- `PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge`
- `PadeROrderWebMeetsRayConeNearOriginInConnectedComponent`
- `nonempty_connectedRayConeSupport_of_meetsRayConeNearOriginInConnectedComponent`
- `PadeRDownArrowOrderWebArcPhaseBridgeInput`
- `PadeRDownArrowOrderWebArcPhaseBridgeInput.toOrderWebRayConeMeetInput`
- `PadeRDownArrowOrderWebRayConeMeetInput`
- `PadeRDownArrowOrderWebConnectedComponentMeetInput`
- `PadeRDownArrowOrderWebConnectedComponentMeetInput.toConnectedRayConeSupportInput`
- `PadeRConnectedRayConeOrderWebSupport`
- `PadeRConnectedRayConeOrderWebSupport.toRayTrackingOrderWebSupport`
- `PadeRDownArrowConnectedRayConeSupportInput`
- `PadeRDownArrowConnectedRayConeSupportInput.toRayTrackingSupportInput`
- `PadeRDownArrowRayTrackingSupportInput`
- `zero_mem_closure_of_meets_rayConeNearOrigin`

The easy closure field is already handled:

- if a connected support meets every small cone, then
  `zero_mem_closure_of_meets_rayConeNearOrigin` supplies
  `0 ∈ closure support`

The missing content is no longer the constructor from a fixed connected
component to connected support; that theorem is now live. The remaining gap is
producing the connected-component compatibility input itself for the concrete
Padé down-arrow families.

## What was tried
- Earlier cycles isolated the lower interfaces
  `PadeRDownArrowOrderWebRayConeMeetInput` and
  `PadeRDownArrowConnectedRayConeSupportInput` so the missing upgrade was named
  explicitly in the live file.
- Cycle 325 repaired the local down-arrow bridge orientation and landed the
  even-angle / positive-error-constant bridge path.
- Cycle 326 landed the odd-angle / negative-error-constant mirror path and the
  corresponding raw cone-meeting / bridge-input theorems.
- Cycle 327 audited the support seam and added the smaller honest compatibility
  predicate `PadeROrderWebMeetsRayConeNearOriginInConnectedComponent`.
- Cycle 327 proved

```lean
nonempty_connectedRayConeSupport_of_meetsRayConeNearOriginInConnectedComponent
```

  by taking the support to be
  `connectedComponentIn (orderWeb (padeR n d)) z0`.
- Cycle 327 also added the theorem-local wrapper
  `PadeRDownArrowOrderWebConnectedComponentMeetInput`, with a conversion to
  `PadeRDownArrowConnectedRayConeSupportInput`.
- A focused Aristotle batch (projects `ab62f411`, `1f043de0`, `49e95088`,
  `100cc39f`, `8d962ce1`) agreed on the same constructor proof and on the
  negative diagnosis that the current even/odd raw cone-meeting theorems do not
  yet imply the new connected-component seam.

## What was learned
- The arc-phase bridge seam is solved locally; the live obstruction has moved
  exactly one layer lower, between raw cone intersections and the new
  connected-component compatibility seam.
- The current `PadeROrderWebMeetsRayConeNearOrigin` statement is purely
  existential and pointwise in the cone parameters. It does not record any
  compatibility between witnesses at different radii/apertures, so connected
  support cannot be assembled by bookkeeping alone.
- The exact missing compatibility is now named explicitly in live code: all
  small-cone witnesses must be chosen inside one connected component of
  `orderWeb (padeR n d)`.
- The obstruction is a genuine quantifier mismatch:
  `PadeROrderWebMeetsRayConeNearOrigin` is `∀ aperture radius, ∃ z`, while the
  new seam requires `∃ z0, ∀ aperture radius, ...` for the connected component
  through `z0`.
- Taking support `{0}` or all of `orderWeb (padeR n d)` would not honestly solve
  this seam:
  - `{0}` does not meet any cone because `rayConeNearOrigin` requires `t > 0`
  - all of `orderWeb` may fail connectedness near the chosen ray

## Possible solutions
- The next honest target is concrete construction of

```lean
PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d θ
```

  for the already-landed down-arrow directions `θ = 0` and
  `θ = Real.pi / ((↑(n + d) + 1) : ℝ)`.
- Any future progress should work strictly through
  `PadeRDownArrowOrderWebConnectedComponentMeetInput` and then
  `PadeRDownArrowConnectedRayConeSupportInput`.
- Do not treat the raw implication
  `PadeROrderWebMeetsRayConeNearOrigin → Nonempty (PadeRConnectedRayConeOrderWebSupport ...)`
  as available unless a new proof actually supplies the missing
  connected-component compatibility.
- Do not hide this requirement inside higher branch packaging, infinity-germ
  interfaces, or count wrappers.
