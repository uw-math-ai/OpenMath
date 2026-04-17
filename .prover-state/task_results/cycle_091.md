# Cycle 091 Results

## Worked on
BDF5 zero-stability in `OpenMath/MultistepMethods.lean`, specifically the two remaining quartic branches in `bdf5_zeroStable`:
- `roots_in_disk`
- `unit_roots_simple`

## Approach
Checked the prepared cycle 091 Aristotle submissions and existing Aristotle result directories first.

For `unit_roots_simple`, incorporated the successful algebraic structure from the completed Aristotle outputs, but kept the local proof `grind`-free:
- conjugate the quartic on `‖ξ‖ = 1` to get the reversed quartic
- combine quartic and reversed quartic to derive a cubic
- conjugate again to get the reversed cubic
- combine to derive a quadratic and its reverse
- subtract to obtain `ξ^2 = 1`
- substitute back into the quartic branch to force `ξ = 143 / 113`, contradiction

For `roots_in_disk`, tested the strongest available Aristotle attempt from the `COMPLETE_WITH_ERRORS` result. The compact branch that normalizes the quartic into real/imaginary coordinates with
`norm_num [Complex.ext_iff, pow_succ]`
and closes the real/nonreal cases by `nlinarith` compiled successfully in the live file without further changes.

## Result
SUCCESS

`lake env lean OpenMath/MultistepMethods.lean` passes with the BDF5 branches closed. There are no remaining executable `sorry`s in `OpenMath/MultistepMethods.lean`; only comments/docstrings elsewhere still mention the word “sorry”.

## Dead ends
- The direct Aristotle file for `bdf5_quartic_no_unit_roots` used `grind` heavily, so I did not copy it directly.
- The prepared and recent Aristotle jobs for the standalone/full BDF5 roots-in-disk targets were still `IN_PROGRESS` when checked at the end of the cycle, so they were not incorporated.

## Discovery
- Prepared cycle 091 Aristotle jobs had already been submitted before this run.
- A `COMPLETE_WITH_ERRORS` Aristotle result can still contain a locally usable proof fragment; the `roots_in_disk` branch compiled even though the full returned file did not.
- The quartic unit-circle exclusion can be proved cleanly by repeated reversed-polynomial elimination, without needing the planner’s alternative `(ξ-1)(ξ+1)(125ξ²-100ξ+125)` factor route.

## Suggested next approach
- If desired, harvest the still-running Aristotle projects `895c0aa7-77a8-4cee-a07f-d76c30a57fbc` and `bd946160-c1d2-4a94-ae6c-93212abc0c38` later, but BDF5 is already complete locally.
- Next planner target can move on to the trivial BDF4/BDF5 convergence corollaries or start BDF6 zero-stability.
