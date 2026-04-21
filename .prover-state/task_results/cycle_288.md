# Cycle 288 Results

## Worked on
The 355E/355G seam in `OpenMath/OrderStars.lean` and
`OpenMath/PadeOrderStars.lean`, specifically whether the explicit endpoint API
behind `thm_355E'_of_padeR` can honestly feed the current Ehle-barrier
interface.

## Approach
Read the cycle strategy and audited the live seam around:
- `SatisfiesArrowCountInequality`
- `thm_355E'`
- `thm_355E'_of_concreteRationalApprox`
- `IsAStablePadeApprox`
- `ehle_barrier`
- `ehle_barrier_nat`
- `thm_355E'_of_padeR`

Then compared the meanings of:
- explicit 355E endpoint equalities
  `downArrowsAtZeros = numeratorDegree`,
  `upArrowsAtPoles = denominatorDegree`
- current 355G-side vanishing fields
  `IsAStablePadeApprox.arrows_zero`,
  `IsAStablePadeApprox.arrows_poles`

Instead of adding a fake bridge, I recorded the semantic mismatch directly in
live code with:
- `degrees_eq_zero_of_exact_endpoint_counts_and_aStablePadeApprox`
- `degrees_eq_zero_of_thm_355E_and_aStablePadeApprox`

I also updated the `IsAStablePadeApprox` docstring to state that the present
355G interface is not yet an honest downstream interface for the explicit 355E
endpoint API.

Aristotle status this cycle:
- No Aristotle submissions. The planner explicitly said there were no pending
  results to harvest and not to submit a new batch without a statement-correct
  local proof gap. This cycle uncovered an interface contradiction instead.

## Result
SUCCESS: clarified the boundary and proved that the current 355G packaging is
not derivable from the explicit 355E endpoint counts except in the trivial
degree-zero case.

`OpenMath/OrderStars.lean` now compiles with the mismatch theorem in place.

## Dead ends
Treating `IsAStablePadeApprox.arrows_zero` and `.arrows_poles` as if they were
the same quantities as the explicit 355E endpoint counts would make the
downstream bridge vacuous except when both Padé degrees are zero.

## Discovery
The live blocker is semantic, not syntactic:
- 355E gives exact endpoint counts equal to `n` and `d`.
- 355G currently erases those same coordinates by setting them to `0`.
- Therefore `ehle_barrier_nat` cannot honestly depend on the explicit endpoint
  API until the 355G-side correction terms are replaced or restated.

Created focused blocker issue:
- `.prover-state/issues/order_star_355g_endpoint_count_interface_mismatch.md`

## Suggested next approach
Replace the 355G-side vanishing fields with the actual A-stability correction
terms, or derive a new Ehle-barrier theorem directly from 355E exact endpoint
counts plus separate A-stability/topology inputs. Do not add a wrapper from
`thm_355E'_of_padeR` to `ehle_barrier_nat` until that interface mismatch is
resolved.
