# Cycle 352 Results

## Worked on
- Read `.prover-state/task_results/cycle_351.md`.
- Read `.prover-state/issues/pade_odd_true_slice_second_order_remainder_bound_missing.md`.
- Confirmed the only live `sorry`s were the three in `OpenMath/PadeOrderStars.lean`.
- Triaged the ready Aristotle bundles requested by the planner.
- Added theorem-local second-order local bound infrastructure in
  `OpenMath/PadeOrderStars.lean`.
- Closed
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`.
- Submitted a fresh five-job Aristotle batch on the reduced fixed-radius
  uniqueness/wrapper seam.
- Wrote a new focused blocker issue:
  `.prover-state/issues/pade_fixed_radius_uniqueness_monotonicity_seam.md`.

## Approach
- Rejected the ready Aristotle bundles unless they patched the live
  `PadeOrderStars` theorem chain without reopening older seams.
- Replaced the dead first-order `hgapTarget` route by building a quantitative
  second-order bound directly in `OpenMath/PadeOrderStars.lean`.
- Added local helper bounds for:
  - the second-order Padé defect remainder,
  - the second-order truncated-exponential remainder,
  - the linear Padé-denominator and inverse-denominator errors,
  - the quadratic `exp (-z) / padeQ n d z` error,
  - the final second-order local approximation
    `padeR n d z * exp (-z) = 1 - C z^(m+1) + C₂ z^(m+2) + O(‖z‖^(m+3))`.
- Rebuilt the endpoint-sign theorem from the explicit `z^(m+2)` term plus the
  tighter `O(r^(m+3))` remainder.

## Result
- SUCCESS: `OpenMath/PadeOrderStars.lean` now compiles with only two remaining
  `sorry`s.
- SUCCESS:
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst` is
  closed.
- SUCCESS:
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  succeeds.
- SUCCESS:
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`
  succeeds.
- PARTIAL: the remaining live `sorry`s are now only:
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`

## Dead ends
- Ready Aristotle bundles `0e8898de`, `914fbab1`, `cc01c469`, `db58b777`,
  `feb2aaaf`, and `b8f45bec` were rejected because they either targeted stale
  surfaces, introduced new helper `sorry`s, or reopened older seams.
- The fresh Aristotle wrapper-only result `3980824d...` was not transplantable:
  it changed the uniqueness theorem surface and still left the actual
  fixed-radius uniqueness proof as `sorry`.
- The current obstacle is not value control any more; it is variation in the
  slice parameter `s`. The new second-order value bound alone does not yet give
  `StrictMonoOn` or an equivalent one-zero result.

## Discovery
- The second-order remainder seam can be made fully quantitative inside
  `PadeOrderStars.lean` without reopening `Pade.lean`, `PadeAsymptotics.lean`,
  or `OrderStars.lean`.
- Once that bound is available, the endpoint theorem closes cleanly using the
  explicit `C₂` term and a simple `sin(x) > x/2` comparison for small `x`.
- The smallest remaining theorem-local seam is now a monotonicity/derivative
  argument for the fixed-radius slice
  `s ↦ oddDownArrowRadiusPhaseIm n d (ρ, s)`.

## Aristotle
- Ready-bundle triage:
  - `0e8898de-afd8-446f-b21d-d72dee25c92a` — rejected; wrapper patch depended
    on a changed uniqueness theorem surface.
  - `914fbab1-59ce-42be-a7f0-8adf8ecbdcde` — rejected; introduced new helper
    `sorry`s for the second-order bound.
  - `cc01c469-a8ee-4b34-8f3f-dbb278794b1c` — rejected; targeted an older
    factorization seam.
  - `db58b777-52bb-411e-80b4-c80a38fb45ab` — rejected; relied on extra helper
    seams not present live.
  - `feb2aaaf-344a-4781-b9c8-fc98d2244f61` — rejected; added helper `sorry`s
    and increased heartbeat budget.
  - `b8f45bec-d404-4ef4-98a8-9ea5a87b6ff9` — rejected; mixed bundle reopened
    stale support layers and was not a direct live patch.
- Fresh cycle-352 batch after narrowing the seam:
  - `4c958aca-b5b3-4622-bd13-4873094c6198` — `IN_PROGRESS` at single refresh
    (22%)
  - `cedda63b-fd05-432d-892b-74c2c1df9339` — `IN_PROGRESS` at single refresh
    (35%)
  - `3980824d-da8c-4575-b492-7edde5876f29` — `COMPLETE_WITH_ERRORS`; rejected
    because it changed the uniqueness theorem surface and left that proof as
    `sorry`
  - `9e276bba-6325-4ceb-86dc-ce0cbda7351a` — `IN_PROGRESS` at single refresh
    (31%)
  - `f0f3bf0c-6367-4fa4-98cf-ea7bd031b881` — `IN_PROGRESS` at single refresh
    (35%)

## Suggested next approach
- Work directly on a theorem-local monotonicity seam for the fixed-radius slice:
  prove a `StrictMonoOn` or equivalent derivative-sign helper on
  `Set.Icc (-ρ) ρ` for small `ρ`.
- After that theorem closes, make the wrapper theorem a short contradiction
  wrapper around same-radius uniqueness.
- If the uniqueness theorem is only local in `ρ`, thread its `δmono` into the
  later projection-radius choice instead of trying to force a global-radius
  uniqueness statement prematurely.
