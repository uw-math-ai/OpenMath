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

## What was tried
- Rejected the ready Aristotle outputs first:
  - `951809cb...` depends on replacement lemmas and a rebuilt
    `OpenMath/PadeOrderStars.lean`
  - `1ab44380...` is just a theorem statement with `sorry`
  - `f76f0680...` solves a toy theorem by replacing the live geometry/proof
- Added the theorem-local radius-phase wedge defs and proved the compactness and
  projection-closedness lemmas in the live file.
- Rewrote the old blocker theorem to use
  `connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0,0)`,
  so the only remaining `sorry` is the projection/no-stop helper.
- Submitted five focused Aristotle jobs on the sharpened file state:
  - `aa1ad4ec-29e7-4155-8e33-b5d7dd491bb5`
  - `3d0928dd-ef72-4b85-b12c-3f0dfc5c505b`
  - `d660eceb-582f-444d-9251-9d11d3c72a60`
  - `ce763ce4-2d6f-46fa-a1fb-06fc08298633`
  - `162237a7-c638-43e5-b582-71bcc5a3b8da`
- On the single allowed refresh in this cycle, all five were still `QUEUED`.

## Possible solutions
- Prove a theorem-local slice-zero lemma on the true wedge, then use
  `exists_clopen_of_no_connected_subset_meeting_both` to contradict early
  stopping of the projection.
- Alternatively prove directly that the projection set is closed, contains `0`,
  and is locally extendable to the right inside the zero set, then conclude it
  is all of `Set.Icc (0 : ℝ) δ`.
- If the slice-zero statement itself is the hard part, split it out as its own
  private helper instead of keeping it implicit inside the no-stop argument.
