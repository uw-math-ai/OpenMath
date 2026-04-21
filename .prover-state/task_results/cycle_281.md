# Cycle 281 Results

## Worked on
- `OpenMath/OrderStars.lean`
- theorem-local branch contradiction:
  `realizedDownArrowInfinityBranch_contradiction`
- attempted generic tangent-classification bridge after the cone-control layer

## Approach
- Confirmed the live baseline still compiled with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean`.
- Read the two planner issue files for the tangent bridge and the realized
  infinity-branch contradiction shape.
- Added sorry-first skeletons in `OrderStars.lean` for:
  - generic down-arrow bridge,
  - generic up-arrow bridge,
  - the down-arrow contradiction theorem.
- Created a focused Aristotle batch in `.prover-state/aristotle/cycle_281/`:
  - `01_downArrowDir_exp_eq_pm_one.lean`
  - `02_upArrowDir_exp_eq_pm_one.lean`
  - `03_local_minus_near_downArrowDir_of_errorConst.lean`
  - `04_local_plus_near_upArrowDir_of_errorConst.lean`
  - `05_realizedDownArrowInfinityBranch_contradiction.lean`
- Submitted all five jobs, slept for 30 minutes, then refreshed each project
  exactly once.
- Rejected the completed Aristotle artifacts that changed the live interface.
- Manually filled `realizedDownArrowInfinityBranch_contradiction` in the live
  file using the cycle-278 helper layer unchanged.
- Removed the two live bridge skeletons after verifying the inverse
  classification target is false under the current norm-only arrow definitions.

## Result
- SUCCESS: `OpenMath/OrderStars.lean` now contains a proved theorem-local
  down-arrow contradiction:
  `realizedDownArrowInfinityBranch_contradiction`.
- SUCCESS: the target file compiles cleanly again with no live `sorry`s.
- FAILED: the planned inverse-classification bridge from
  `IsDownArrowDir` / `IsUpArrowDir` to `exp (I * (p + 1) * θ) = ±1` is not
  derivable from the current live definitions, so the generic down/up tangent
  bridges were not added to the live file this cycle.

## Dead ends
- Aristotle project `2d8579c7-9397-4273-8838-1668de85037f`
  (`02_upArrowDir_exp_eq_pm_one`) finished `COMPLETE_WITH_ERRORS`, but the
  artifact redefined `IsUpArrowDir` to include real/order-web content not
  present in the live file.
- Aristotle project `e24fe038-1806-4efe-9f29-851ae4662150`
  (`05_realizedDownArrowInfinityBranch_contradiction`) finished
  `COMPLETE_WITH_ERRORS`, but the returned proof used fabricated fields like
  `branch.dir`, `branch.isDownDir`, `branch.branchTracksRayNearOrigin`, and
  `cexp`, so it was not directly incorporable.
- Aristotle projects
  `5b0c3468-81a1-4ccb-b8b3-62b1aa5f5209`,
  `61b6fd34-caeb-48e1-a86c-15dec2d4c83e`,
  and `6d853567-449b-470c-b000-f2004e7e736d`
  were still `IN_PROGRESS` at the single post-wait refresh, so they were
  treated as unavailable for this cycle.
- The intended inverse step is analytically false with the current arrow
  predicates: for the model `1 - C z^(p+1)`, norm sign is governed by
  `cos ((p + 1) * θ)`, so many non-`±1` phases already give up/down rays.

## Discovery
- The live `IsUpArrowDir` / `IsDownArrowDir` predicates are too weak for the
  planned tangent-family dispatch. They capture only whether
  `‖R(t e^{iθ}) * exp(-(t e^{iθ}))‖` is above or below `1` near `0`.
- Because of that, the sought implication to `exp (I * (p + 1) * θ) = ±1`
  fails. A concrete obstruction is forward Euler at `θ = π / 3`, where the
  norm is already greater than `1` for small `t`, but `exp (2π I / 3) ≠ ±1`.
- The theorem-local contradiction shape itself is sound and closes cleanly from
  the existing helper layer once the local cone sign control is supplied as a
  hypothesis.

## Suggested next approach
- Do not retry the generic bridge with the current norm-only arrow predicates.
- Instead, decide which of the following is mathematically intended:
  - strengthen the tangent-direction hypothesis to include order-web/phase
    tangency data, or
  - keep local cone sign control as an explicit theorem-local hypothesis for the
    no-infinity contradiction seam.
- Start from the focused blocker issue
  `.prover-state/issues/order_star_inverse_classification_from_norm_only_arrow_dirs_fails.md`
  rather than from the rejected cycle-278/279/280 bundles.
