# Issue: Padé down-arrow tracking is now reduced to an exact-angle arc-phase bridge

## Blocker
The live blocker is now one level lower again than
`PadeRDownArrowOrderWebRayConeMeetInput`.

The old raw target is still

```lean
PadeROrderWebMeetsRayConeNearOrigin n d θ
```

but cycle 323 now isolates a strictly smaller theorem-local bridge below it:

```lean
PadeROrderWebArcPhaseBridgeNearOrigin n d θ
```

This new bridge asks for a short exact-angle arc inside each sufficiently small
cone such that:

- every point on the arc stays in the cone,
- `padeR n d z * exp (-z)` has positive real part on the whole arc,
- the imaginary part is negative at one endpoint and positive at the other.

The new theorem

```lean
PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge
```

is now proved in the live file, so once the arc-phase bridge is constructed,
the raw cone-meeting theorem follows formally by IVT. Connected-support
packaging still sits one step above that.

## Context
Relevant live declarations in `OpenMath/PadeOrderStars.lean`:

- `PadeROrderWebArcPhaseBridgeNearOrigin`
- `PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge`
- `PadeRDownArrowOrderWebArcPhaseBridgeInput`
- `PadeRDownArrowOrderWebArcPhaseBridgeInput.toOrderWebRayConeMeetInput`
- `PadeROrderWebMeetsRayConeNearOrigin`
- `PadeRConnectedRayConeOrderWebSupport`
- `PadeRConnectedRayConeOrderWebSupport.toRayTrackingOrderWebSupport`
- `PadeRDownArrowOrderWebRayConeMeetInput`
- `PadeRDownArrowConnectedRayConeSupportInput`
- `PadeRDownArrowConnectedRayConeSupportInput.toRayTrackingSupportInput`
- `PadeRDownArrowRayTrackingSupportInput`

Supporting facts already in the live file:

- `padeR_exists_downArrowDir`
- `padeR_exp_neg_local_bound`
- `padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos`
- `padeR_local_minus_near_of_errorConst_cos_pos`
- `padeR_nonneg_sign_of_downArrowDir`
- `rayConeNearOrigin`
- `BranchTracksRayNearOrigin`

Cycle 322 also proved a purely geometric helper:

```lean
zero_mem_closure_of_meets_rayConeNearOrigin
```

so once a connected support meets every small cone, the `0 ∈ closure support`
field of `PadeRRayTrackingOrderWebSupport` is automatic.

## What was tried
- Added the new exact-angle arc-phase bridge
  `PadeROrderWebArcPhaseBridgeNearOrigin`.
- Proved the formal upgrade
  `PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge`.
- Added the lower input wrapper
  `PadeRDownArrowOrderWebArcPhaseBridgeInput` together with
  `PadeRDownArrowOrderWebArcPhaseBridgeInput.toOrderWebRayConeMeetInput`.
- Re-checked the asymptotic/sector control already available in
  `OpenMath/PadeAsymptotics.lean` and `OpenMath/OrderStars.lean`.
- Confirmed that the remaining missing work is no longer “some order-web point
  exists in the cone”, but “build an exact-angle arc where the Padé phase
  crosses the positive real axis while staying in the cone”.

## Why the current hypotheses are still insufficient
- `0 < data.downArrowsAtInfinity` is only a count statement. It does not
  produce any concrete exact-angle arc with phase crossing data.
- `∃ θ, IsDownArrowDir (padeR n d) θ` only gives exact-ray `< 1` behavior for
  points `t * exp(iθ)` with `t > 0` sufficiently small. Those ray points lie in
  `orderStarMinus`, not automatically in `orderWeb`.
- The live local sign-control lemmas
  `padeR_local_minus_near_of_errorConst_cos_pos` and
  `padeR_local_plus_near_of_errorConst_cos_neg` only control whether
  `‖padeR n d z * exp (-z)‖` is `< 1` or `> 1` on cones. They do not create any
  equality points `R z * exp(-z) = r > 0`, so they do not by themselves yield
  members of `orderWeb`.
- The new formal IVT bridge shows the exact missing analytic content more
  sharply: we still need a theorem deriving, from the Padé asymptotic control,
  a short exact-angle arc inside the cone on which the real part stays positive
  and the imaginary part changes sign between the endpoints.
- Even after raw cone hits, there is still no theorem connecting those
  witnesses into one connected support meeting every small cone.
- The current positive-count theorem still returns only `support = {0}`, and
  `0` alone cannot witness cone intersection because `rayConeNearOrigin` uses
  `t ∈ (0, radius)`.

## Possible solutions
- Prove explicit Padé-local arc-phase bridge theorems for the concrete even/odd
  down-arrow angles already supplied by the sign of `padePhiErrorConst`.
- Derive `PadeROrderWebArcPhaseBridgeNearOrigin n d θ` first; then the raw
  cone-meeting theorem follows automatically from the live IVT theorem.
- After that, return to the connected-support packaging problem
  `Nonempty (PadeRConnectedRayConeOrderWebSupport n d θ)`.
