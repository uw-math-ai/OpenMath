# Cycle 487 Results

## Worked on
AB13 vector quantitative convergence:
`OpenMath/LMMAB13VectorConvergence.lean`, with plan bookkeeping in `plan.md`.

## Approach
First triaged the ready Aristotle outputs. The live `LMMAB13Convergence.lean`
and `LMMAM12VectorConvergence.lean` had no executable `sorry`s. The ready
AB13 scalar Aristotle outputs were stale/off-target against the live repo: they
created stub `OpenMath` dependencies or regressed closed scalar work, so no
code was transplanted. The unrelated algebraic-geometry bundles were ignored.

Built the AB13 vector file sorry-first, checked that the scaffold compiled, and
submitted five Aristotle jobs:
- `f8bed1c4-55a2-45d3-82db-4df059fe945e`: generic setup, still `IN_PROGRESS`
  at the single 30-minute check.
- `7056b0b3-1595-4a69-a607-d1507b73e350`: packed residual algebra,
  `COMPLETE`; incorporated `ab13Vec_residual_alg_identity` and
  `ab13Vec_residual_bound_alg_identity`.
- `32e81aaf-e2bd-41ff-96ac-0f0a07823953`: triangle/combine helpers,
  `COMPLETE`; incorporated `ab13Vec_triangle_aux`,
  `ab13Vec_residual_fourteen_term_triangle`, and
  `ab13Vec_residual_combine_aux`.
- `0a4f1474-ef22-4585-ad6d-3295422c1c71`: pointwise/local residuals, still
  `IN_PROGRESS` at the single 30-minute check.
- `510800b8-c96b-4bb1-9b13-321ba6396859`: residual bridge/global theorem,
  still `IN_PROGRESS` at the single 30-minute check.

Closed the remaining goals manually by mirroring the AB12 vector and AB13 scalar
generic patterns, using the public fourteenth-order vector Taylor helpers from
`OpenMath/LMMAM12VectorConvergence.lean`.

## Result
SUCCESS. Added the finite-dimensional vector AB13 chain:
`ab13IterVec`, `ab13VecResidual`, one-step vector Lipschitz/error bounds,
packed residual algebra, `ab13Vec_pointwise_residual_bound`,
`ab13Vec_local_residual_bound`, generic bridge lemmas, and the headline
`ab13Vec_global_error_bound`.

The pointwise residual bound is
`‖τ_n‖ ≤ 529729 * M * h ^ 14`, matching the scalar AB13 slack.

## Dead ends
The pre-existing ready Aristotle scalar AB13 results were not useful because
they targeted already-closed work and depended on stubbed or stale project
structure. No unrelated Aristotle algebraic-geometry output was incorporated.

## Discovery
The AM12 vector packed-polynomial pattern transfers cleanly to AB13 once the
y-remainder window is shifted to `13h`/`12h` and the derivative remainders run
from `12h` down to `h`. The generic AB vector convergence bridge then handles
the global theorem without new framework work.

## Suggested next approach
The Adams scalar/vector quantitative chains are now closed through AB13 and
AM12. Future multistep work should either move to the next planned method
family or address the deferred BDF4-BDF6 global theorem through a generic
quadratic/discrete Lyapunov framework, not another weighted `l¹` recurrence.
