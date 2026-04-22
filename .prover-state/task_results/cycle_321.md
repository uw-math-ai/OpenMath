# Cycle 321 Results

## Worked on
The active Padé/order-star near-origin tracking seam in
`OpenMath/PadeOrderStars.lean`, specifically the theorem-local input behind:

- `PadeRDownArrowBranchTrackingInput`
- `PadeRTrackedDownArrowBranch`
- `PadeRTrackedDownArrowInfinityWitnessFamily`

The concrete target was to decide whether

```lean
0 < data.downArrowsAtInfinity -> Nonempty (PadeRTrackedDownArrowBranch n d)
```

is derivable from the current live Padé inputs, and if not, to isolate the next
smaller honest seam below it.

## Approach
- Re-read the live definitions in `OpenMath/OrderStars.lean`:
  `GlobalDownArrowBranch`, `rayConeNearOrigin`,
  `BranchTracksRayNearOrigin`, `RealizedDownArrowInfinityBranch`.
- Re-read the live Padé seam in `OpenMath/PadeOrderStars.lean`:
  `PadeRTrackedDownArrowBranch`,
  `PadeRDownArrowBranchTrackingInput`,
  `padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos`,
  `padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos`,
  and the local cone sign feeders.
- Confirmed that the current positive-count support theorem still uses
  `support = {0}`, so it cannot imply `BranchTracksRayNearOrigin`.
- Added a smaller support-level seam:
  `PadeRRayTrackingOrderWebSupport`, together with packaging lemmas:
  `PadeRRayTrackingOrderWebSupport.toTrackedDownArrowBranch`,
  `PadeRTrackedDownArrowBranch.toRayTrackingOrderWebSupport`,
  `nonempty_padeR_trackedDownArrowBranch_iff_exists_rayTrackingSupport`.
- Added the next honest theorem-local input structure below the branch-level
  seam:
  `PadeRDownArrowRayTrackingSupportInput`, plus
  `PadeRDownArrowRayTrackingSupportInput.toTrackingInput`.
- Stated five Aristotle scratch jobs after the live theorem-local boundary was
  explicit:
  - `TrackedFromCount.lean`
  - `SupportFromCount.lean`
  - `SupportFromDir.lean`
  - `EvenAngleSupport.lean`
  - `OddAngleSupport.lean`
- Waited 30 minutes, refreshed once, inspected the returned outputs, and
  rejected all five because they replaced the live interface rather than
  proving the live theorem.

## Result
SUCCESS: the remaining blocker is now isolated one level lower than
`PadeRDownArrowBranchTrackingInput`.

The new live seam is:

```lean
0 < data.downArrowsAtInfinity ->
  ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
    Nonempty (PadeRRayTrackingOrderWebSupport n d θ)
```

This packages immediately into a tracked branch, but it is strictly more local
and more honest than asking for `Nonempty (PadeRTrackedDownArrowBranch n d)`
without naming the missing support theorem.

Compiled successfully:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`

## Dead ends
- The existing theorem
  `padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos`
  is still pure bookkeeping via `{0}` support and does not create any cone-level
  `orderWeb` witness near a tangent ray.
- The local Padé cone inequalities (`padeR_local_minus_near_of_errorConst_cos_pos`
  and companions) control the sign of `‖padeR * exp(-z)‖` on cones, but by
  themselves they do not produce points of `orderWeb (padeR n d)` or a connected
  support inside the order web.
- Aristotle batch results after the required wait:
  - `36a04f78-1b9a-4628-a553-47e8eaeb8b4b` (`TrackedFromCount.lean`):
    `COMPLETE_WITH_ERRORS`, rejected. Invented a replacement
    `OpenMath/PadeOrderStars.lean` where `PadeRTrackedDownArrowBranch` was a
    default-inhabited record.
  - `56f677a7-41d4-4694-8110-af254f23a1cc` (`SupportFromCount.lean`):
    `COMPLETE_WITH_ERRORS`, rejected. Added a fake `witness` field to
    `OrderArrowTerminationData`.
  - `fa812f00-37d9-4f27-b05b-3e97c62a5326` (`SupportFromDir.lean`):
    `COMPLETE_WITH_ERRORS`, rejected. Rebuilt `padeR`, `IsDownArrowDir`, and
    `PadeRRayTrackingOrderWebSupport` as unrelated toy structures.
  - `860ccd68-d85f-4706-a3e4-0f9dc61100e5` (`EvenAngleSupport.lean`):
    `COMPLETE_WITH_ERRORS`, rejected. Replaced the live support notion by a
    record with synthetic branch indices/residual fields.
  - `fcc42dc1-9658-487f-8aa5-b54d536282b7` (`OddAngleSupport.lean`):
    `COMPLETE_WITH_ERRORS`, rejected. Introduced a different boundary/sine-based
    surrogate interface instead of the live `orderWeb` support theorem.

## Discovery
- The first missing realized-branch field remains near-origin tracking, not
  far-field escape.
- After this cycle, the exact remaining theorem is no longer “some tracked branch
  exists,” but “there is a connected subset of `orderWeb (padeR n d)` meeting
  every sufficiently small cone around a concrete down-arrow ray.”
- The new equivalence
  `nonempty_padeR_trackedDownArrowBranch_iff_exists_rayTrackingSupport`
  confirms that the live seam is now localized to support geometry rather than
  branch packaging.

## Suggested next approach
- Target a Padé-local theorem proving actual `orderWeb` intersection in every
  sufficiently small cone around a concrete down-arrow direction.
- Extract a connected support from those cone witnesses to instantiate
  `PadeRRayTrackingOrderWebSupport`.
- Do not return to `EscapesEveryClosedBall` until this support theorem exists.
- Reuse the new support-level seam rather than the older `{0}`-support global
  branch theorem.
