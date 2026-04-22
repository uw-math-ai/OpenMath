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
step is a theorem that upgrades raw cone intersections of the Padé order web to

```lean
Nonempty (PadeRConnectedRayConeOrderWebSupport n d θ)
```

for a concrete down-arrow direction `θ`.

At present there is no live constructor showing that from

```lean
PadeROrderWebMeetsRayConeNearOrigin n d θ
```

one can extract a **connected** subset of `orderWeb (padeR n d)` that still
meets every sufficiently small cone around the same ray.

## Context
Relevant live declarations in `OpenMath/PadeOrderStars.lean`:

- `PadeROrderWebArcPhaseBridgeNearOrigin`
- `PadeROrderWebMeetsRayConeNearOrigin`
- `PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge`
- `PadeRDownArrowOrderWebArcPhaseBridgeInput`
- `PadeRDownArrowOrderWebArcPhaseBridgeInput.toOrderWebRayConeMeetInput`
- `PadeRDownArrowOrderWebRayConeMeetInput`
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

The missing content is the support constructor itself, not the closure argument.

## What was tried
- Earlier cycles isolated the lower interfaces
  `PadeRDownArrowOrderWebRayConeMeetInput` and
  `PadeRDownArrowConnectedRayConeSupportInput` so the missing upgrade is named
  explicitly in the live file.
- Cycle 325 repaired the local down-arrow bridge orientation and landed the
  even-angle / positive-error-constant bridge path.
- Cycle 326 landed the odd-angle / negative-error-constant mirror path and the
  corresponding raw cone-meeting / bridge-input theorems.
- The current file therefore already reaches raw order-web cone intersections
  near concrete down-arrow rays, but it still has no theorem packaging those
  intersections into a connected support set.

## What was learned
- The arc-phase bridge seam is solved locally; the live obstruction has moved
  one layer lower, exactly between raw cone intersections and
  `PadeRConnectedRayConeOrderWebSupport`.
- The current `PadeROrderWebMeetsRayConeNearOrigin` statement is purely
  existential and pointwise in the cone parameters. It does not record any
  compatibility between witnesses at different radii/apertures, so connected
  support cannot be assembled by bookkeeping alone.
- Taking support `{0}` or all of `orderWeb (padeR n d)` would not honestly solve
  this seam:
  - `{0}` does not meet any cone because `rayConeNearOrigin` requires `t > 0`
  - all of `orderWeb` may fail connectedness near the chosen ray

## Possible solutions
- Add an honest theorem-local constructor of the form

```lean
PadeROrderWebMeetsRayConeNearOrigin n d θ →
Nonempty (PadeRConnectedRayConeOrderWebSupport n d θ)
```

or an equivalent one-step-up input theorem filling
`PadeRDownArrowConnectedRayConeSupportInput`.
- The proof likely needs a new geometric/topological lemma extracting a
  connected component of `orderWeb (padeR n d)` that inherits the cone-meeting
  property from repeated local witnesses.
- Work at the support layer only. Do not jump ahead to realized branches,
  no-escape, or infinity-germ packaging until this constructor exists.
