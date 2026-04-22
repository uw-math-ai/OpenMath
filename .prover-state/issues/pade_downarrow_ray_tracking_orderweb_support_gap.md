# Issue: Padé down-arrow tracking is now reduced to an exact-angle arc-phase bridge orientation mismatch

## Blocker
Cycle 324 proved a concrete even-angle down-arrow endpoint-sign theorem in live
code:

```lean
padeR_even_downArrowArcEndpointSigns_of_pos_errorConst
```

This theorem shows that near a genuine down-arrow ray the exact-angle endpoint
signs are

- `0 < im` at `θ - η`,
- `im < 0` at `θ + η`.

But the current bridge interface

```lean
PadeROrderWebArcPhaseBridgeNearOrigin n d θ
```

demands the opposite ordering:

- `im(θ - η) < 0`,
- `0 < im(θ + η)`.

So the remaining blocker is now sharper than “prove endpoint signs”. The local
Padé asymptotics already produce endpoint signs, but with the reverse
orientation from the current bridge statement.

## Context
Relevant live declarations in `OpenMath/PadeOrderStars.lean`:

- `PadeROrderWebArcPhaseBridgeNearOrigin`
- `PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge`
- `padeR_even_downArrowArcEndpointSigns_of_pos_errorConst`
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
- `padeR_local_minus_near_of_errorConst_cos_pos`
- `rayConeNearOrigin`
- `padeR_even_downArrowArcEndpointSigns_of_pos_errorConst`

Cycle 322 also proved a purely geometric helper:

```lean
zero_mem_closure_of_meets_rayConeNearOrigin
```

so once a connected support meets every small cone, the `0 ∈ closure support`
field of `PadeRRayTrackingOrderWebSupport` is automatic.

## What was tried
- Cycle 323 added the theorem-local bridge seam
  `PadeROrderWebArcPhaseBridgeNearOrigin` and the IVT upgrade
  `PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge`.
- Cycle 324 first inserted sorry-first concrete even/odd bridge skeletons and
  verified the file compiled.
- Then cycle 324 proved the smaller concrete helper
  `padeR_even_downArrowArcEndpointSigns_of_pos_errorConst`.
- That helper uses the full local asymptotic bound
  `padeR_exp_neg_local_bound`, not only the norm-side cone corollaries.
- A fresh 5-file Aristotle batch was submitted for geometry, real-part
  positivity, endpoint signs, and the even/odd bridge targets.

## What was learned
- The missing content is not merely “prove endpoint signs somehow”.
- For the concrete even down-arrow case, the local Padé asymptotic already
  forces the opposite endpoint orientation from the current bridge definition.
- So the interface mismatch now sits exactly between:
  - the concrete Padé asymptotic helper,
  - and the current bridge statement consumed by the IVT theorem.

## Possible solutions
- Add an equivalent bridge theorem whose endpoint hypotheses allow the reversed
  sign order already produced by the down-arrow asymptotics.
- Or keep the existing geometric content but apply IVT to
  `s ↦ -Complex.im (...)`, so that the reversed endpoint signs become usable
  without changing the underlying order-web conclusion.
- Once the orientation mismatch is repaired, the remaining honest helper goals
  are still:
  - exact-angle arc geometry inside `rayConeNearOrigin`,
  - positive real part on the whole arc,
  - then the existing IVT upgrade to raw cone meeting.
