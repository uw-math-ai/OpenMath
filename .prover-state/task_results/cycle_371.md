# Cycle 371 Results

## Worked on
- Reverse direction of Theorem 358A in `OpenMath/CollocationAlgStability.lean`
- Ported the boundary-node/Lagrange/quadrature infrastructure below the forward-direction proof
- Closed `thm_358A_if` and therefore the full iff theorem `thm_358A`

## Approach
- Checked the five cycle-370 Aristotle jobs first:
  - `ccf88ddf-93b1-450b-8d70-74b2aaa14864`: `IN_PROGRESS`
  - `a6da066b-10b2-4ce5-bf05-ac61da149bc6`: `IN_PROGRESS`
  - `5f2ebb0e-4c72-42d9-b32c-281d1b68b517`: `IN_PROGRESS`
  - `292dfe56-3f87-4c53-b3ff-081074a9414f`: `IN_PROGRESS`
  - `18acc2c0-52dc-4b7b-aef0-ccc1116f2de5`: `IN_PROGRESS`
- Added the reverse-direction scaffold with the Lagrange-basis route and verified the sorry-first structure compiled.
- Submitted the required Aristotle batch:
  - `2e4a95a2-cb01-4c34-9bb8-c875c8a8b75a` for `weight_eq_integral_lagrange`
  - `5b40f708-0db1-4545-9c89-9073df4a8e62` for `shiftedLegendre_orthogonal_integral`
  - `ee48d33d-8e0a-4019-bd0c-58dd937764ed` for `nodePoly_eq_const_mul_boundary`
  - `fd068e62-e283-4fe9-b1ac-81bc4c17a44f` for `quadrature_exact_of_boundary`
  - `24ad416d-23e9-40df-b37a-1cf1f117b3f6` for `quadrature_error_pQ_nonneg_of_boundary`
- Slept for 30 minutes as required, then refreshed once.
- Extracted the completed result `fd068e62-e283-4fe9-b1ac-81bc4c17a44f` and ported its proof of `quadrature_exact_of_boundary`.
- Manually completed the remaining reverse-direction proof.
- Introduced a small antiderivative bridge:
  - `antiderivPoly`
  - `antiderivPoly_eval`
  - `antiderivPoly_derivative`
  - `antiderivPoly_natDegree_le`
  - `antiderivPoly_leadingCoeff_of_natDegree_eq`
- Used that bridge to prove `algStabMatrix_quadForm_nonneg_of_boundary` by:
  - interpolating the coefficient vector into a polynomial `p`
  - setting `Q := antiderivPoly p`
  - rewriting the quadratic form with `algStabMatrix_quadForm_expand`
  - applying `quadrature_error_pQ_nonneg_of_boundary` to `p * Q`

## Result
- SUCCESS
- Proved `thm_358A_if`.
- Proved the full theorem `thm_358A`.
- `OpenMath/CollocationAlgStability.lean` has no remaining `sorry`.
- `lake env lean OpenMath/CollocationAlgStability.lean` succeeds with existing linter warnings only.
- `lake build` succeeds.
- Completed lemmas:
  - `weight_eq_integral_lagrange`
  - `A_eq_integral_lagrange`
  - `B_quadrature_exact`
  - `shiftedLegendre_orthogonal_integral`
  - `boundary_poly_orthogonal`
  - `nodePoly_eq_const_mul_boundary`
  - `nodePoly_orthogonal_low_degree`
  - `quadrature_exact_of_boundary`
  - `weights_nonneg_of_boundary`
  - `shiftedLegendre_mul_Xpow_integral_pos`
  - `quadrature_error_pQ_nonneg_of_boundary`
  - `algStabMatrix_quadForm_nonneg_of_boundary`

## Dead ends
- Tried a direct-antiderivative `Q` for the final PSD proof. This made the leading-coefficient sign of `p * Q` clean, but the interpolation/antiderivative equalities generated a large amount of brittle coefficient algebra in Lean.
- Tried porting the old artifact’s final PSD proof more literally. That proof shape still works mathematically, but adapting it to the corrected quadrature-error statement needed an extra reusable antiderivative/leading-coefficient bridge.

## Discovery
- The corrected reverse-direction quadrature-error lemma is workable if stated with the additional hypothesis `0 ≤ r.leadingCoeff`.
- The node polynomial normalization proof is cleaner via polynomial determination on the `s` distinct nodes than via quotient/divisibility bookkeeping.
- The final PSD step becomes manageable once the antiderivative is packaged into a reusable polynomial helper instead of being expanded inline.

## Suggested next approach
- Reuse the `antiderivPoly` helper if later chapters need the same quadrature-error/PSD pattern for other collocation arguments.
- If the remaining cycle-370 or cycle-371 Aristotle jobs later complete, compare them against the manual proof and harvest any shorter helper lemmas without changing the mathematics.
