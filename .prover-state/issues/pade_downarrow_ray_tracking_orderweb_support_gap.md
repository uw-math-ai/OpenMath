# Issue: Padé down-arrow tracking still lacks cone-level order-web support

## Blocker
The live seam in `OpenMath/PadeOrderStars.lean` is now isolated one level lower
than `PadeRDownArrowBranchTrackingInput`, but the actual geometric theorem is
still missing.

What remains unproved is an existence statement of the form

```lean
∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
  Nonempty (PadeRRayTrackingOrderWebSupport n d θ)
```

or equivalently

```lean
Nonempty (PadeRTrackedDownArrowBranch n d)
```

in the positive-count case.

The exact missing content is not the tangent direction and not far-field escape:
it is a connected subset of `orderWeb (padeR n d)` whose support intersects
every sufficiently small cone `rayConeNearOrigin θ aperture radius`.

## Context
Relevant live additions in `OpenMath/PadeOrderStars.lean`:

- `PadeRRayTrackingOrderWebSupport`
- `PadeRTrackedDownArrowBranch.toRayTrackingOrderWebSupport`
- `nonempty_padeR_trackedDownArrowBranch_iff_exists_rayTrackingSupport`
- `PadeRDownArrowRayTrackingSupportInput`
- `PadeRDownArrowRayTrackingSupportInput.toTrackingInput`

Relevant older theorems/definitions:

- `padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos`
- `padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos`
- `padeR_local_minus_near_of_errorConst_cos_pos`
- `BranchTracksRayNearOrigin`
- `rayConeNearOrigin`

The current positive-count support theorem still returns only `support = {0}`.
That support cannot satisfy `BranchTracksRayNearOrigin`, because every
`rayConeNearOrigin θ aperture radius` is built from `t ∈ (0, radius)` and so
does not witness cone intersection using only the origin.

## What was tried
- Re-read the tracked-branch interface in `OpenMath/OrderStars.lean`.
- Re-checked the Padé local cone sign theorems and the current
  `{0}`-support branch constructor chain.
- Added a smaller support-level seam:
  `PadeRRayTrackingOrderWebSupport`.
- Proved packaging lemmas showing this support-level seam is exactly equivalent
  to `PadeRTrackedDownArrowBranch` once a matching `IsDownArrowDir` is supplied.
- Added `PadeRDownArrowRayTrackingSupportInput` so the remaining gap is now
  explicitly the cone-level order-web support theorem, not generic branch
  existence.

## Possible solutions
- Prove a Padé-local theorem that `orderWeb (padeR n d)` meets every
  sufficiently small cone around a concrete down-arrow direction, and extract a
  connected support from those witnesses.
- Prove a stronger local continuation theorem: nearby `orderWeb` points continue
  through the down-arrow germ, not just the `< 1` sign on the cone.
- Use the existing local minus/plus cone inequalities only as feeders; by
  themselves they do not create `orderWeb` points or connected branch support.
