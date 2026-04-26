# Cycle 425 Results

## Worked on
AB6 convergence file split and the Adams-Bashforth 6-step vector convergence chain.

## Approach
First triaged the two ready Aristotle outputs:
- `9202af0e-688a-4e44-97f7-4cc0cd4ef0a8`: targets already-closed `LMMAB5Convergence.lean` vector pointwise residual work.
- `d8c9fa72-5cc3-4718-86e9-89830e077df8`: targets already-closed AB5 vector one-step Lipschitz work and includes a stubbed/rebuilt environment.

Both were discarded per the cycle strategy; no proof fragments were transplanted.

Then split `OpenMath/LMMAB6Convergence.lean` into:
- `OpenMath/LMMAB6ScalarConvergence.lean`
- `OpenMath/LMMAB6VectorConvergence.lean`

The vector file was written sorry-first, verified, and submitted to Aristotle as a five-job batch:
- `9476c9e2-6000-4aa9-973d-b9ea1e103ac8`: `iteratedDeriv_seven_bounded_on_Icc_vec`
- `fd65d55a-5660-47a7-b175-9d0bd828cf40`: `y_seventh_order_taylor_remainder_vec`
- `f6c02e02-f01d-45c8-9792-56929fbeb9c1`: `derivY_sixth_order_taylor_remainder_vec`
- `4865b916-48ab-4c6e-b3fa-f0aa8f026081`: `ab6Vec_pointwise_residual_bound`
- `7ee03a6c-b0f8-40b7-81d7-eb79a07d929b`: `ab6Vec_global_error_bound`

While waiting for Aristotle, I closed the vector chain manually. The AB6 vector proof reuses the AB5 vector sixth-order Taylor remainder by making `LMM.y_sixth_order_taylor_remainder_vec` public, then adds the AB6-specific seventh-order vector Taylor layer and six-window recurrence.

## Result
SUCCESS.

Implemented `OpenMath/LMMAB6VectorConvergence.lean` with:
- `LMM.ab6IterVec`
- `LMM.ab6VecResidual`
- `LMM.ab6Vec_localTruncationError_eq`
- `LMM.ab6Vec_one_step_lipschitz`
- `LMM.ab6Vec_one_step_error_bound`
- private vector Taylor and algebra helpers
- `LMM.ab6Vec_local_residual_bound`
- `LMM.ab6Vec_global_error_bound`

The exact AB6 residual coefficient used is `1264800760 / 7257600`, with the safe `175 * M * h^7` over-estimate.

Verification:
- `lake env lean OpenMath/LMMAB5Convergence.lean`
- `lake env lean OpenMath/LMMAB6ScalarConvergence.lean`
- `lake env lean OpenMath/LMMAB6VectorConvergence.lean`
- `lake build OpenMath.LMMAB6VectorConvergence`

All completed successfully. Existing lint warnings in imported/scalar files remain unchanged.

## Aristotle batch results
After the required 30-minute wait, one refresh pass showed all five jobs still
in progress, so no Aristotle output was incorporated this cycle:
- `9476c9e2-6000-4aa9-973d-b9ea1e103ac8`: IN_PROGRESS, 5%
- `fd65d55a-5660-47a7-b175-9d0bd828cf40`: IN_PROGRESS, 3%
- `f6c02e02-f01d-45c8-9792-56929fbeb9c1`: IN_PROGRESS, 2%
- `4865b916-48ab-4c6e-b3fa-f0aa8f026081`: IN_PROGRESS, 4%
- `7ee03a6c-b0f8-40b7-81d7-eb79a07d929b`: IN_PROGRESS, 3%

## Dead ends
- Did not transplant prior AB5 Aristotle bundles because their target declarations are already closed on main.
- Avoided in-place AB6 vector growth in the scalar file; the split kept both AB6 files below the soft cap.
- Avoided `nlinarith` on the large residual slack rational; used `norm_num` for the literal coefficient inequality and `mul_le_mul_of_nonneg_right` for the nonnegative factor.

## Discovery
- The AB5 vector sixth-order Taylor remainder is reusable AB6 infrastructure if exported. This avoids duplicating the lower-order interval-integral Taylor ladder in the new AB6 vector file.
- The AB6 vector file lands at about 1470 lines, and the scalar file remains about 1410 lines after the split.

## Suggested next approach
Start the generic Adams-Bashforth `s`-step convergence abstraction for §1.2. AB2-AB6 now provide closed scalar and vector examples with repeated recurrence, residual, and Gronwall structure.
