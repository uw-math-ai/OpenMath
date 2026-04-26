# Cycle 437 Results

## Worked on
AM5 quantitative scalar convergence chain:

- Promoted the three AB6 seventh-order scalar Taylor helpers from `private` to public.
- Added `OpenMath/LMMAM5Convergence.lean`.
- Updated `plan.md` with the AM5 scalar entry and constants.

## Approach
Ported `OpenMath/LMMAM4Convergence.lean` one stencil step up to AM5:

- Coefficients changed to `(475, 1427, -798, 482, -173, 27) / 1440`.
- The implicit recurrence and max-window proofs were extended from four to five history samples.
- The divided one-step proof uses the required `5L` growth slack under `(475/1440) * h * L ≤ 1/2`.
- The residual proof uses the public AB6 helpers:
  `iteratedDeriv_seven_bounded_on_Icc`,
  `y_seventh_order_taylor_remainder`,
  `derivY_sixth_order_taylor_remainder`.
- The pointwise residual coefficient was computed with Python `Fraction` as
  `23325037/725760 ≈ 32.14` and slackened to `33`.
- The headline theorem uses `lmm_error_bound_from_local_truncation` at `p = 6`
  with effective Lipschitz constant `5L` and horizon side condition `(N + 4) * h ≤ T`.

Aristotle batch submitted as focused one-sorry scaffolds under
`.prover-state/aristotle_scaffolds/cycle_437/`:

- `f0990dc8-c2be-46dc-af0d-2e4efc9f2d6e`: `am5_localTruncationError_eq`
- `5d47be46-48e2-408d-b19e-98e466a8be84`: `am5_one_step_lipschitz`
- `42a1ee9e-6362-4963-9d7a-40022e0ac2f2`: `am5_one_step_error_bound`
- `04cc8648-4e31-48f8-939f-6d2d879d97bb`: `am5_pointwise_residual_bound`
- `2003d297-5b76-4393-b663-59c780770a3d`: `am5_global_error_bound`

## Result
SUCCESS — the live AM5 file compiles sorry-free locally.

Verification commands run:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.LMMAB6ScalarConvergence`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAM5Convergence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAB6ScalarConvergence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.LMMAM5Convergence`

Aristotle status after the required 30-minute wait:

- `f0990dc8-c2be-46dc-af0d-2e4efc9f2d6e`: `COMPLETE_WITH_ERRORS`
- `5d47be46-48e2-408d-b19e-98e466a8be84`: `IN_PROGRESS` at 21%
- `42a1ee9e-6362-4963-9d7a-40022e0ac2f2`: `IN_PROGRESS` at 17%
- `04cc8648-4e31-48f8-939f-6d2d879d97bb`: `IN_PROGRESS` at 24%
- `2003d297-5b76-4393-b663-59c780770a3d`: `IN_PROGRESS` at 21%

No Aristotle output was incorporated because the live AM5 chain was already
closed manually before any usable completed result returned.

## Dead ends
None in the live proof. A Lean LSP outline request for the new AM5 file timed out,
but command-line Lean checks were clean and did not depend on LSP state.

## Discovery
The AM4 proof template scales directly to AM5 once the additional slot is threaded
through the Lipschitz, divided, rolling-window, local-residual, and Gronwall
sections. The exact residual coefficient is `23325037/725760`, so integer slack
`33` is the smallest simple bound above the exact rational.

The `5L` divided-growth slack is sufficient with the strategy's small-step
condition. The corresponding algebraic step closes by `nlinarith` using
`h * L ≤ 144/95`.

## Suggested next approach
AM6 scalar would require eighth-order Taylor helpers, which are not currently
available from the AB6 chain. Either build/expose the needed Taylor remainder
infrastructure first, or begin the deferred Adams-Moulton vector scaffold from
AM2 as planned.
