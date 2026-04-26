# Cycle 435 Results

## Worked on
AM3 quantitative scalar convergence chain for Iserles Chapter 1 section 1.2.

## Approach
First made the required AB4 scalar Taylor helpers public:
`iteratedDeriv_five_bounded_on_Icc`,
`y_fifth_order_taylor_remainder`, and
`derivY_fourth_order_taylor_remainder`.

Then added `OpenMath/LMMAM3Convergence.lean` by porting the AM2 supplied
implicit-trajectory template to the AM3 stencil.  The file includes:
`IsAM3Trajectory`, the AM3 local truncation rewrite, one-step implicit
Lipschitz bounds, a rolling 3-window max recurrence, a fifth-order Taylor
residual bound, the uniform local residual bound, and the headline global
error theorem.

Submitted the required Aristotle batch after the sorry-first scaffold:

- `96fb129c-0c98-466f-a2d6-e74a04e54541`: COMPLETE for
  `am3_localTruncationError_eq`, but used stub OpenMath replacement files.
  Rejected as a transplant; the live proof was closed manually with the same
  `unfold; simp; ring` idea.
- `e489fbd4-636d-4576-a55d-ebc8d0a07e0a`: IN_PROGRESS at the single
  post-sleep refresh; rejected for this cycle.
- `6e62a0a8-b8e8-4d5b-9a6f-8b171818878c`: COMPLETE_WITH_ERRORS for
  `am3_one_step_error_bound`; proof was against a self-contained/stub file,
  but confirmed the divided growth slack `3L` and residual coefficient `2`.
- `6d0c8843-1328-4d67-b77c-bf03aeedfe47`: IN_PROGRESS at the single
  post-sleep refresh; rejected for this cycle.
- `b9e70467-2f17-4e19-ba64-d14f9eadba63`: COMPLETE_WITH_ERRORS for
  `am3_local_residual_bound`; used stub imports and a local helper, so not
  transplanted.

## Result
SUCCESS.  `OpenMath/LMMAM3Convergence.lean` is tracked and has no sorries.
The final headline is:

`LMM.am3_global_error_bound`:
`|yseq N - y (t0 + N*h)| <= exp((3*L)*T)*eps0 + K*h^4`
for supplied AM3 trajectories under `(9/24)hL <= 1/2` and
`(N+2)h <= T`.

The planner's target exponent `25L/24` is the explicit-history coefficient
only.  The implicit `9/24` new-point term must be divided out, so the exact
small-step growth starts at `(25/24 + 9/24)L = 17L/12`; the closed proof uses
the AM2-style conservative `3L` slack.

## Dead ends
Aristotle results were not directly usable because completed bundles either
included stub OpenMath modules or local replacement definitions.  They were
used only as sanity checks for proof shape.

## Discovery
Direct `lake env lean OpenMath/LMMAM3Convergence.lean` initially saw the old
compiled AB4 interface after dropping `private`; running
`lake build OpenMath.LMMAB4Convergence` refreshed the `.olean` so AM3 could
import the newly public fifth-order helper names.

The AM3 residual Taylor coefficient is exactly `131/32`, slackened to `5`.

## Suggested next approach
Continue the Adams-Moulton quantitative chain with AM4, but expect the global
growth constant to include the divided implicit coefficient, not just the
explicit-history weight sum.
