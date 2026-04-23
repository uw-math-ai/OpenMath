# Cycle 362 Results

## Worked on
- Aristotle triage for project `314a6a62-23a9-4572-a6b4-be80da8c324c`
- `OpenMath/CollocationAlgStability.lean`
  - theorem-local `(358c)` helper split
  - `nodePoly_polyMoment_orthogonal_of_algStable`
  - `nodePoly_interval_orthogonal_of_algStable`
  - `thm_358A_only_if`
- Focused blocker write-up:
  - `.prover-state/issues/cycle_362_358A_transformed_matrix_358c_helpers.md`

## Approach
- Read the ready Aristotle bundle summary and diffed its `CollocationAlgStability`,
  `Legendre`, and `StiffEquations` copies against the live repository.
- Rejected the bundle copies of `OpenMath/Legendre.lean` and
  `OpenMath/StiffEquations.lean` because they are stub replacements of live
  project files.
- Rejected the bundle proof route for
  `nodePoly_polyMoment_orthogonal_of_algStable` because it depends on a fake
  strengthened `IsAlgStable` field `satisfiesB_enhanced`, which does not exist
  in the live code.
- Salvaged only the theorem shape and restructured the live file around the real
  missing seam:
  - added `nodePoly_interval_zero_aux_of_algStable`
  - added `nodePoly_interval_nonpos_aux_of_algStable`
- Closed the old interval/moment orthogonality pair on top of the live zero
  helper and the existing `OpenMath.Legendre` bridge:
  - `nodePoly_interval_orthogonal_of_algStable`
  - `nodePoly_polyMoment_orthogonal_of_algStable`
- Submitted a fresh focused 5-job Aristotle batch on the updated live file:
  - `f298bb43-ff28-4047-aba4-00f6d9bc1692` — `nodePoly_interval_zero_aux_of_algStable`
  - `018396aa-862f-40af-ab80-f1d50e1263b2` — `nodePoly_interval_nonpos_aux_of_algStable`
  - `04dc25b1-f231-437c-b2e4-7bb394171735` — `orthogonal_degree_eq_boundaryPoly`
  - `52cf2a73-fe6f-4019-8dfd-f462d2e37b0f` — `boundary_theta_nonneg_of_algStable`
  - `b0b385af-9f0e-4cf2-818c-edb6a8ed5f5a` — `thm_358A_only_if`
- Slept 30 minutes and did one refresh only.
- Extracted the three ready results and transplanted the only clean live proof:
  `thm_358A_only_if` from project `b0b385af-9f0e-4cf2-818c-edb6a8ed5f5a`,
  adapting it to the live file and verifying it compiles.

## Result
SUCCESS — the ready Aristotle bundle was triaged and rejected on the fake-field
route, `CollocationAlgStability.lean` now has the live `(358c)` zero/sign helper
scaffold, the orthogonality pair is closed as wrappers over that scaffold, and
`thm_358A_only_if` is fully proved in the live file. The file compiles with the
remaining frontier reduced to five sorrys:
- `nodePoly_interval_zero_aux_of_algStable`
- `nodePoly_interval_nonpos_aux_of_algStable`
- `orthogonal_degree_eq_boundaryPoly`
- `boundary_theta_nonneg_of_algStable`
- `thm_358A_if`

Fresh Aristotle batch status after the mandated single refresh:
- `f298bb43-ff28-4047-aba4-00f6d9bc1692`: `IN_PROGRESS`
- `018396aa-862f-40af-ab80-f1d50e1263b2`: `COMPLETE_WITH_ERRORS`
- `04dc25b1-f231-437c-b2e4-7bb394171735`: `IN_PROGRESS`
- `52cf2a73-fe6f-4019-8dfd-f462d2e37b0f`: `COMPLETE_WITH_ERRORS`
- `b0b385af-9f0e-4cf2-818c-edb6a8ed5f5a`: `COMPLETE`

## Dead ends
- The ready bundle `314a6a62-...` is not transplantable as code because its
  `Legendre` and `StiffEquations` files are stub replacements.
- The bundle proof for the first bridge theorem is unusable in the live repo
  because it smuggles in `hAlg.satisfiesB_enhanced`.
- The new Aristotle sign/theta artifacts (`018396aa-...`, `52cf2a73-...`) also
  fell back to stub-module assumptions and introduced extra sorry'd helper
  infrastructure, so they were not transplanted.
- Local search during the wait window did not reveal a ready-made interpolation
  API that directly supplies the transformed-matrix `(358c)` identity.

## Discovery
- The real live seam is now explicit in code:
  `nodePoly_interval_zero_aux_of_algStable` plus the degree-`s - 1` sign helper.
- The wrapper theorem `thm_358A_only_if` does not need new mathematics once the
  zero/sign and boundary-polynomial lemmas are in place; Aristotle’s completed
  proof was directly reusable after minor live-file fixes.
- The extracted theorem metadata at
  `../butcher_exp_1/OpenMath/extraction/formalization_data/entities/thm_358A.json`
  matches the planner’s `(358c)` reading: zero against degree `≤ s - 2`
  polynomials and a sign statement in degree `s - 1`.

## Suggested next approach
- First harvest the two still-running Aristotle jobs if they later complete:
  - `f298bb43-ff28-4047-aba4-00f6d9bc1692`
  - `04dc25b1-f231-437c-b2e4-7bb394171735`
- If they do not close the gap, attack the live transformed-matrix helper from
  `hAlg.posdef_M` directly, as recorded in
  `.prover-state/issues/cycle_362_358A_transformed_matrix_358c_helpers.md`.
- After the zero/sign helpers land, the next downstream targets are:
  - `orthogonal_degree_eq_boundaryPoly`
  - `boundary_theta_nonneg_of_algStable`
  - `thm_358A_if`
