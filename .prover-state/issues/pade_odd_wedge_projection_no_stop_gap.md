# Issue: odd wedge projection no-stop lemma still missing

## Blocker
The file now isolates the remaining odd down-arrow gap to
`oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst` in
`OpenMath/PadeOrderStars.lean`.

The missing implication is:

- for the compact zero set
  `oddDownArrowRadiusPhaseZeroSet n d δ`
- with `(0, 0)` in the zero set,
- with closed projection
  `Prod.fst '' connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0)`,
- and with positive real part already proved on the whole wedge,

show that the connected component of `(0,0)` projects onto all of
`Set.Icc (0 : ℝ) δ`.

## Context
- The original blocker theorem
  `padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst`
  is now proved modulo this helper.
- New live helper infrastructure directly above the helper proves:
  - closedness and compactness of the true odd wedge
    `p.2 ∈ Set.Icc (-p.1) p.1`
  - continuity of the live radius-phase value/im function on the wedge
  - compactness of the wedge zero set
  - `(0,0)` membership in the zero set
  - compactness/closedness of the first-coordinate image of the connected
    component of `(0,0)`
  - positive real part on the entire wedge from the existing small-norm lemma
- Cycle 341 added two more theorem-local helpers:
  - `mem_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet_of_connected_subset`
  - `exists_clopen_separating_origin_from_radiusSlice_in_oddDownArrowRadiusPhaseZeroSet`
- The live `sorry` is now reduced to the final contradiction after assuming
  `r ∉ Prod.fst '' connectedComponentIn ...`:
  - a clopen `C` of the compact subtype zero set separates the origin from the
    whole `r`-slice,
  - `L := (fun p : X => p.1.1) '' C` and `R := (fun p : X => p.1.1) '' Cᶜ`
    are both closed,
  - `0 ∈ L`,
  - any zero-set point with first coordinate `r` is forced into `Cᶜ`.

## What was tried
- Rejected the ready Aristotle bundle `187b14fd...` under the strict transplant
  filter:
  - it rebuilds `OpenMath/PadeOrderStars.lean`,
  - replaces the live Padé/order-web objects with toy model definitions,
  - proves the obsolete connected-support surface instead of the live helper.
- Added the two live theorem-local helpers listed above and rewrote
  `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst` so the remaining
  `sorry` is now just the final `False` after the clopen split is set up.
- Verified the file still compiles with exactly one `sorry` via
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`.
- Submitted five new cycle-341 Aristotle jobs on the sharpened live file:
  - `e346a8bc-c36e-4033-9d91-23691b40b7ad`
  - `ff4fe71b-6a26-4ba0-ab70-e7e1ba03d2f5`
  - `d78e6e94-96cb-4fe2-8b4b-a132ca83392c`
  - `20210ea6-a72b-41df-8393-4b69efc7b22e`
  - `bd2c41f1-7710-437f-a82b-633458adf72e`
- Canceled the five stale cycle-340 Aristotle jobs because they were still
  `QUEUED` and were blocking new submissions:
  - `aa1ad4ec-29e7-4155-8e33-b5d7dd491bb5`
  - `3d0928dd-ef72-4b85-b12c-3f0dfc5c505b`
  - `d660eceb-582f-444d-9251-9d11d3c72a60`
  - `ce763ce4-2d6f-46fa-a1fb-06fc08298633`
  - `162237a7-c638-43e5-b582-71bcc5a3b8da`
- Immediate status after submission: all five cycle-341 jobs were `QUEUED`.

## Possible solutions
- Prove a theorem-local slice-zero lemma on the true wedge, then use
  `exists_clopen_of_no_connected_subset_meeting_both` to contradict early
  stopping of the projection.
- More concretely, the missing implication is now:
  1. obtain a zero-set witness on the omitted `r`-slice in the true wedge,
  2. place that slice radius into `R`,
  3. show the closed sets `L` and `R` cannot cover/separate `Set.Icc (0 : ℝ) δ`.
- If the exact slice-zero statement is still the hard part, it should become
  its own private helper theorem above the no-stop lemma rather than staying
  implicit inside the final contradiction.
