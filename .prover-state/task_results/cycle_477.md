# Cycle 477 Results

## Worked on
Adams--Moulton 10-step scalar quantitative convergence chain:
`OpenMath/LMMAM10Convergence.lean`, plus `LMM.adamsMoulton10` and the four
standard registrations in `OpenMath/AdamsMethods.lean`.

## Approach
Computed the AM10 weights by exact `Fraction` Lagrange-basis integration on
nodes `0,...,10` over `[9,10]`.  Sanity checks passed: numerators sum to
`479001600`, moments through degree 10 match the Adams integral moments, and
`ceil (2 * sum |beta|) = 37`.  The exact twelfth-order residual coefficient is
`251196920117213671 / 49792216320000`, slackened to `5045`.

Used the public scalar twelfth-order Taylor helpers from
`OpenMath/LMMAB11Convergence.lean`.  The residual proof follows the extracted
abstract-helper pattern: algebra identity, numeric bound identity, 12-term
triangle, and combine lemma.  The one-step recurrence uses a finite-window
`am10ErrWindow`, then the headline theorem routes through
`lmm_error_bound_from_local_truncation` at `p = 10`, weakening the `h^12`
local residual to `h^11` under the selected `h <= 1` cap to match the planned
`K * h^10` statement.

## Result
SUCCESS.  Added:

- `LMM.adamsMoulton10`
- `LMM.adamsMoulton10_consistent`
- `LMM.adamsMoulton10_implicit`
- `LMM.adamsMoulton10_order_eleven`
- `LMM.adamsMoulton10_zeroStable`
- `LMM.IsAM10Trajectory`
- `LMM.am10_localTruncationError_eq`
- `LMM.am10_one_step_lipschitz`
- `LMM.am10_one_step_error_pair_bound`
- `LMM.am10_pointwise_residual_bound`
- `LMM.am10_local_residual_bound`
- `LMM.am10_global_error_bound`

Aristotle: submitted project `76e2fe2d-b1be-49d5-991a-6f6c9ed43622` for
`am10_localTruncationError_eq`.  The other four requested parallel submissions
were rejected by the service with 429 "too many requests in progress."  After
the required 30-minute wait, the accepted job was still `QUEUED`, so no
Aristotle proof was available to transplant.

## Dead ends
No mathematical blocker.  Aristotle could not be used beyond the single queued
job because of the service concurrency limit, and the queued job had no result
after the mandated wait.

## Discovery
The AM10 scalar chain fits within the 200K heartbeat budget when the Taylor
remainders are named and cleared before applying abstract scalar residual
helpers.  A compact finite-window definition avoids the very large nested-max
term used by earlier AM scalar files while still feeding the same Gronwall
bridge.

## Suggested next approach
Open the AM10 vector chain next, reusing the scalar coefficients and mirroring
the AB11-vector lesson: keep residual algebra abstract over the Taylor
witnesses, and be prepared to parameterize the module-valued algebra helper if
statement elaboration approaches the heartbeat budget.
