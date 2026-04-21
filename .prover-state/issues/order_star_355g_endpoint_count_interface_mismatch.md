# Issue: 355G interface reuses 355E endpoint counts as vanishing correction terms

## Blocker
The current 355G-side interface is not semantically compatible with the
explicit 355E endpoint API.

- `thm_355E` / `thm_355E'` conclude
  `downArrowsAtZeros = numeratorDegree` and
  `upArrowsAtPoles = denominatorDegree`.
- `IsAStablePadeApprox.arrows_zero` and `.arrows_poles` instead require
  those same fields to be `0`.

So an honest bridge from `thm_355E'_of_padeR` into the current
`ehle_barrier` / `ehle_barrier_nat` interface would force
`numeratorDegree = 0` and `denominatorDegree = 0`. That is a real semantic
mismatch, not just a missing wrapper theorem.

## Context
- Live seam audited this cycle:
  - `OpenMath/OrderStars.lean`
    - `thm_355E'`
    - `thm_355E'_of_concreteRationalApprox`
    - `IsAStablePadeApprox`
    - `ehle_barrier`
    - `ehle_barrier_nat`
  - `OpenMath/PadeOrderStars.lean`
    - `thm_355E'_of_padeR`
- New theorem added this cycle:
  - `degrees_eq_zero_of_exact_endpoint_counts_and_aStablePadeApprox`
  - `degrees_eq_zero_of_thm_355E_and_aStablePadeApprox`
- These theorems formalize the mismatch directly: combining the exact 355E
  endpoint counts with the current 355G vanishing fields collapses to the
  trivial degree-zero case.

## What was tried
- Audited the exact 355E endpoint theorem chain and the 355G/Ehle-barrier
  packaging before editing.
- Checked whether the current fields
  `IsAStablePadeApprox.arrows_zero` and `.arrows_poles` could honestly be
  identified with the explicit endpoint counts from 355E.
- Confirmed they cannot: the counts are equal to `n` and `d` after 355E, while
  the 355G interface needs them to vanish.
- Added the mismatch theorem in `OpenMath/OrderStars.lean` and recompiled the
  file to record the boundary in live code rather than leaving it implicit.

## Possible solutions
- Replace the 355G-side vanishing fields by the actual A-stability correction
  terms, distinct from `downArrowsAtZeros` and `upArrowsAtPoles`.
- Keep the explicit 355E endpoint equalities, but build a new downstream bridge
  theorem that consumes those equalities together with separate A-stability
  topology inputs, bypassing the current `IsAStablePadeApprox` fields.
- Until the correct correction terms are formalized, keep the Ehle-barrier side
  theorem-local and do not pretend that `thm_355E'_of_padeR` feeds directly
  into `ehle_barrier_nat`.
