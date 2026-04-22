# Cycle 341 Results

## Worked on
- Ready Aristotle bundle:
  - `187b14fd-01fc-42c2-950f-b7e1cc0a85bb`
- `OpenMath/PadeOrderStars.lean`
- Live blocker:
  `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst`
- New cycle-341 Aristotle batch:
  - `e346a8bc-c36e-4033-9d91-23691b40b7ad`
  - `ff4fe71b-6a26-4ba0-ab70-e7e1ba03d2f5`
  - `d78e6e94-96cb-4fe2-8b4b-a132ca83392c`
  - `20210ea6-a72b-41df-8393-4b69efc7b22e`
  - `bd2c41f1-7710-437f-a82b-633458adf72e`

## Approach
- Read `.prover-state/strategy.md` and the two blocker issues first.
- Audited the ready Aristotle bundle `187b14fd...` under the strict transplant
  filter.
- Rejected that bundle as a code transplant:
  - it creates a replacement `OpenMath/PadeOrderStars.lean`,
  - it replaces the live Padé/order-web objects with toy/model definitions,
  - it proves the obsolete connected-support surface rather than the current
    no-stop helper.
- Added two new live theorem-local helpers in `OpenMath/PadeOrderStars.lean`:
  - `mem_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet_of_connected_subset`
  - `exists_clopen_separating_origin_from_radiusSlice_in_oddDownArrowRadiusPhaseZeroSet`
- Rewrote `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst` so the
  remaining `sorry` is no longer the whole theorem body; it now sits only at
  the final contradiction after:
  - the omitted-radius assumption is introduced,
  - the clopen separator is produced,
  - the closed projection sets `L` and `R` are defined,
  - the origin membership `0 ∈ L` is proved.
- Verified the file with:
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
- Submitted five new Aristotle jobs against the sharpened live file.
- Canceled the five stale cycle-340 Aristotle jobs because they were still
  `QUEUED` and were blocking fresh submissions.

## Result
- SUCCESS (bundle triage): `187b14fd...` was rejected for interface drift and
  toy replacements; nothing was transplanted into the live file.
- SUCCESS (code progress): the file gained 2 proved theorem-local helpers and
  the remaining `sorry` was reduced to a smaller final contradiction goal.
- PARTIAL: `OpenMath/PadeOrderStars.lean` still contains exactly one `sorry`,
  inside `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst`.
- Aristotle status immediately after the new submissions:
  - `e346a8bc...`: `QUEUED`
  - `ff4fe71b...`: `QUEUED`
  - `d78e6e94...`: `QUEUED`
  - `20210ea6...`: `QUEUED`
  - `bd2c41f1...`: `QUEUED`
- Canceled old cycle-340 queued jobs:
  - `aa1ad4ec...`
  - `3d0928dd...`
  - `d660eceb...`
  - `ce763ce4...`
  - `162237a7...`

## Dead ends
- The ready Aristotle bundle again failed the live transplant filter; it was a
  rebuilt/toy file, not a theorem-local patch.
- I did not land the exact slice-zero lemma on the true wedge this cycle.
- The final contradiction still needs the analytic crossing step that turns the
  clopen split into an impossible closed separation of the radius interval.

## Discovery
- The blocker is now sharper in code than at the start of the cycle. The live
  proof already packages:
  - omitted radius `r`,
  - clopen separator `C` in the compact subtype zero set,
  - closed projection sets `L` and `R`,
  - `0 ∈ L`,
  - the fact that any zero on the omitted `r`-slice must lie in `Cᶜ`.
- The new helper
  `mem_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet_of_connected_subset`
  cleanly packages the component-projection fact needed for all future clopen
  contradictions.
- The new helper
  `exists_clopen_separating_origin_from_radiusSlice_in_oddDownArrowRadiusPhaseZeroSet`
  isolates the compact-topology side of the omitted-radius argument.

## Suggested next approach
- Prove the exact slice-zero lemma on the true wedge:
  for each `r ∈ Set.Icc (0 : ℝ) δ`, find `s ∈ Set.Icc (-r) r` with
  `(r, s) ∈ oddDownArrowRadiusPhaseZeroSet n d δ`.
- Then return to the current final contradiction and show the closed sets `L`
  and `R` cannot separate `Set.Icc (0 : ℝ) δ`.
- Re-check the five cycle-341 Aristotle jobs once they leave `QUEUED`, but only
  transplant theorem-local fragments that match the live file shape.
