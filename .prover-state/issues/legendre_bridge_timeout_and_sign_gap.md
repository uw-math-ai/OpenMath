# Issue: Legendre bridge proof times out and has a sign-convention gap

## Blocker
Closing `gaussLegendre_B_double` currently needs a bridge from the recursive
`shiftedLegendreP` to Mathlib's `Polynomial.shiftedLegendre`, plus an
orthogonality theorem for the resulting coefficients. The available Aristotle
bridge result is mathematically useful, but it does not drop into this repo
cleanly under the current heartbeat cap and local environment.

## Context
- Current remaining sorrys:
  - `OpenMath/Legendre.lean:207` (`gaussLegendre_B_double`)
  - `OpenMath/Legendre.lean:235` (`gaussLegendreNodes_of_B_double`)
- Aristotle job `1d9822aa-9d1d-4d23-abf6-501995a5f6a8` proved a corrected bridge
  with a sign:
  `shiftedLegendreP n x = (-1)^n * eval x (map _ (Polynomial.shiftedLegendre n))`
- That sign is expected: Mathlib's `Polynomial.shiftedLegendre` uses the
  `P_n(1 - 2x)` convention, while the local recurrence defines `P_n(2x - 1)`.
- When I attempted to inline the bridge proof, the key coefficient-comparison
  recurrence for `Polynomial.shiftedLegendre` timed out in this repo at the
  default `200000` heartbeat limit.
- The orthogonality proof path imported from Aristotle also needed additional
  repair: some simp-heavy combinatorial steps were brittle here, and one proof
  branch failed before reaching the main theorem.

## What was tried
- Checked all 7 planner-listed Aristotle jobs first.
- Extracted completed jobs:
  - `25f0bc02-fd9c-4e56-a5fe-dcb75e9a92c0`
  - `88562ee9-0604-4af8-af76-4cd109783926`
  - `1d9822aa-9d1d-4d23-abf6-501995a5f6a8`
- Tried to inline the bridge proof and explicit-coefficient orthogonality
  lemmas directly in `OpenMath/Legendre.lean`.
- Ran `lake env lean OpenMath/Legendre.lean` and `lean_diagnostic_messages`.
- Reverted the non-compiling experiment after confirming:
  - a timeout in the bridge recurrence proof
  - a mismatch around `natDegree_map`
  - a broken coefficient-rewrite step in the polynomial expansion proof

## Possible solutions
- Use the Aristotle bridge theorem as a starting point, but re-prove the
  polynomial recurrence with smaller, less simp-heavy coefficient lemmas that
  stay under the `200000` heartbeat limit.
- Avoid the full bridge initially and prove only the exact coefficient formula
  needed for `gaussLegendre_B_double`.
- Switch the orthogonality proof to a Rodrigues-based algebraic functional
  (`∑ coeff/(k+1)`) if that produces shorter local proof terms than the
  alternating-binomial route.
