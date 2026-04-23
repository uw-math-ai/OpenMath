# Cycle 363 Results

## Worked on
- `OpenMath/CollocationAlgStability.lean`
- Aristotle triage for bundles:
  - `018396aa-862f-40af-ab80-f1d50e1263b2`
  - `52cf2a73-fe6f-4019-8dfd-f462d2e37b0f`
  - `fabcddf1-d2e4-46d2-b0b9-90ed47ed1cc8`
- Optional single status refresh for:
  - `f298bb43-ff28-4047-aba4-00f6d9bc1692`
  - `04dc25b1-f231-437c-b2e4-7bb394171735`

## Approach
- Diffed only each bundle's `CollocationAlgStability.lean` against the live
  file, as required.
- Rejected all bundled copies of `OpenMath/Legendre.lean`,
  `OpenMath/StiffEquations.lean`, and `lakefile.toml` as non-transplantable
  stub replacements.
- From `018396aa`, salvaged only the local helper shape
  `stabilityMatrix_quadForm_eq_neg_integral` plus the proof route for the sign
  theorem.
- From `52cf2a73`, salvaged only the route sketch for
  `boundary_theta_nonneg_of_algStable`.
- Treated `fabcddf1` purely as a sign-convention warning and did not transplant
  its theorem-statement change.
- Added the live second-stage helper scaffold
  `stabilityMatrix_quadForm_eq_neg_integral`.
- Replaced the former bare `sorry` in
  `nodePoly_interval_nonpos_aux_of_algStable` with a live proof reducing the
  sign statement to:
  - `stabilityMatrix_quadForm_eq_neg_integral`
  - `nodePoly_interval_zero_aux_of_algStable`
  - `hAlg.posdef_M`
- Submitted a fresh focused Aristotle batch on the remaining live surfaces.

## Result
- SUCCESS: completed the mandated Aristotle triage and made live progress in
  `CollocationAlgStability.lean`.
- SUCCESS: closed one of the original frontier theorems,
  `nodePoly_interval_nonpos_aux_of_algStable`.
- SUCCESS: `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/CollocationAlgStability.lean`
  passed.
- SUCCESS: `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.CollocationAlgStability`
  passed.
- PENDING: the primary transformed-matrix zero bridge
  `nodePoly_interval_zero_aux_of_algStable` is still open.

## Dead ends
- The `018396aa` helper route is not sufficient as the primary `(358c)` bridge,
  because it depends on the lower-degree zero theorem via `hzero`.
- The `52cf2a73` boundary proof adds wrappers whose sign assumptions do not
  match the live mapped-shifted-Legendre convention without further checking.
- `fabcddf1` changes the boundary theorem statement to `a ≠ 0`; that is a
  warning about sign convention, not a safe live patch.

## Discovery
- The exact missing transformed-matrix identity is more precise than “prove the
  zero theorem”: after dividing the antiderivative `Q` by `nodePoly t`, the
  remaining blocker is the theorem-local exactness statement
  `∑ b_i q(c_i) r(c_i) = ∫ q*r` for the specific remainder polynomial `r`.
- The optional Aristotle refreshes still showed:
  - `f298bb43-ff28-4047-aba4-00f6d9bc1692`: `IN_PROGRESS` at 16%
  - `04dc25b1-f231-437c-b2e4-7bb394171735`: `IN_PROGRESS` at 19%
- Fresh Aristotle submissions created:
  - `316c37f4-8e12-4d55-88a8-3682f79fbb75` for `stabilityMatrix_quadForm_eq_neg_integral`
  - `9fd0c5c8-911a-4daa-9393-a762eeff297d` for `nodePoly_interval_zero_aux_of_algStable`
  - `9ff6bd72-65af-4a9c-9fb3-36c9bd0f14a8` for `boundary_theta_nonneg_of_algStable`
  - `f4149896-55c9-4146-a3ff-8caabd337a59` for `orthogonal_degree_eq_boundaryPoly`
  - `6ef314f0-9928-498f-90c6-23644b5496e7` for `thm_358A_if`
- All five fresh Aristotle jobs were `QUEUED` immediately after submission.

## Suggested next approach
- Prove the special exactness lemma for the antiderivative remainder `r`
  identified in the new blocker issue:
  `.prover-state/issues/cycle_363_358A_transformed_matrix_primary_identity.md`
- Once that is live, close `nodePoly_interval_zero_aux_of_algStable`, then
  discharge `stabilityMatrix_quadForm_eq_neg_integral` and keep
  `nodePoly_interval_nonpos_aux_of_algStable` as the thin wrapper already in
  place.
- After the zero/sign pair is fully live, revisit
  `boundary_theta_nonneg_of_algStable` with a sign-correct shifted-Legendre test
  polynomial if the raw mapped polynomial has alternating leading sign.
