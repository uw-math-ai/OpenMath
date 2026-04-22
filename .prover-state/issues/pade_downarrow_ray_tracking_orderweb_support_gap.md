# Issue: Padé down-arrow tracking still lacks cone-level order-web support

## Blocker
The live blocker is now split one level lower than
`PadeRDownArrowRayTrackingSupportInput`.

The current target theorem is still

```lean
∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
  Nonempty (PadeRRayTrackingOrderWebSupport n d θ)
```

but cycle 322 isolates two strictly smaller ingredients below it:

```lean
PadeROrderWebMeetsRayConeNearOrigin n d θ
```

and

```lean
Nonempty (PadeRConnectedRayConeOrderWebSupport n d θ)
```

The first asks only for raw `orderWeb (padeR n d)` points in every sufficiently
small cone around the ray. The second packages those raw cone hits into a
connected order-web support. Only after that packaging step does the existing
`PadeRRayTrackingOrderWebSupport` interface follow.

## Context
Relevant live declarations in `OpenMath/PadeOrderStars.lean`:

- `PadeROrderWebMeetsRayConeNearOrigin`
- `PadeRConnectedRayConeOrderWebSupport`
- `PadeRConnectedRayConeOrderWebSupport.toRayTrackingOrderWebSupport`
- `PadeRDownArrowOrderWebRayConeMeetInput`
- `PadeRDownArrowConnectedRayConeSupportInput`
- `PadeRDownArrowConnectedRayConeSupportInput.toRayTrackingSupportInput`
- `PadeRDownArrowRayTrackingSupportInput`

Supporting facts already in the live file:

- `padeR_exists_downArrowDir`
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
- Re-triaged the six ready Aristotle bundles first.
- Rejected `TrackedFromCount`, `SupportFromCount`, `SupportFromDir`,
  `EvenAngleSupport`, and `OddAngleSupport` again because they redefine the live
  seam (`padeR`, support structures, or fake/default witnesses) instead of
  proving theorem-local lemmas against the current interface.
- Rejected `8418c228.../OrderStars.lean` as non-transplantable because it is a
  wholesale alternate `OrderStars` file, not a tiny live helper.
- Checked the current Padé-local sign-control lemmas against the support seam.
- Added the lower cone-meeting and connected-support seams in
  `OpenMath/PadeOrderStars.lean`.

## Why the current hypotheses are still insufficient
- `0 < data.downArrowsAtInfinity` is only a count statement. It does not
  produce any concrete point of `orderWeb (padeR n d)` near the chosen ray.
- `∃ θ, IsDownArrowDir (padeR n d) θ` only gives exact-ray `< 1` behavior for
  points `t * exp(iθ)` with `t > 0` sufficiently small. Those ray points lie in
  `orderStarMinus`, not automatically in `orderWeb`.
- The live local sign-control lemmas
  `padeR_local_minus_near_of_errorConst_cos_pos` and
  `padeR_local_plus_near_of_errorConst_cos_neg` only control whether
  `‖padeR n d z * exp (-z)‖` is `< 1` or `> 1` on cones. They do not create any
  equality points `R z * exp(-z) = r > 0`, so they do not by themselves yield
  members of `orderWeb`.
- Even if raw `orderWeb` cone hits were available, there is still no theorem
  connecting those scattered witnesses into a single connected support meeting
  every small cone.
- The current positive-count theorem still returns only `support = {0}`, and
  `0` alone cannot witness cone intersection because `rayConeNearOrigin` uses
  `t ∈ (0, radius)`.

## Possible solutions
- Prove the smallest missing analytic statement first:
  `PadeROrderWebMeetsRayConeNearOrigin n d θ` for a concrete Padé down-arrow
  angle.
- Then prove a connected-component packaging lemma turning those raw cone hits
  into `PadeRConnectedRayConeOrderWebSupport n d θ`.
- If that packaging needs extra local continuation input, state that input
  explicitly rather than jumping back to tracked branches or realized infinity
  branches.
