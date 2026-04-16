# Cycle 081 Results

## Worked on
`OpenMath/DahlquistEquivalence.lean`, targeting the remaining sorry
`uniformly_bounded_tupleSucc_iterates`.

## Approach
- Added the planner-requested sorry-first decomposition:
  `tupleSucc_eq_smul_on_unit_eigenspace` and
  `tupleSucc_pow_bounded_on_disk_eigenspace`.
- Proved a supporting helper:
  `tupleSucc_minpoly_rootMultiplicity_eq_one_of_unit_eigenvalue`.
  This upgrades the existing unit-circle simplicity result from the recurrence
  polynomial to the ambient `minpoly` of `tupleSucc`, using
  `minpoly ∣ E.charPoly`.
- Verified the modified file builds with `lake build OpenMath.DahlquistEquivalence`.
- Submitted five Aristotle jobs focused on the two helper lemmas and the final
  combination step.

## Result
FAILED — the main sorry is still open, but the file now has the required
decomposition and one new proved helper lemma.

Aristotle submissions:
- `65e4e237-32f1-413c-9acd-3663227575dc` — `tupleSucc_eq_smul_on_unit_eigenspace`
- `668684f8-c89c-4315-9aa9-35340c3dd7ab` — `tupleSucc_pow_bounded_on_disk_eigenspace`
- `9b831aee-06f6-47c0-bbae-5907ab2e2976` — `uniformly_bounded_tupleSucc_iterates`
- `b9b81468-ea6f-4521-8665-509fc26a5139` — minpoly/restriction route for the unit eigenspace lemma
- `4d573da6-7e4b-4754-be47-59e9a27616f5` — final decomposition/combination step

Status at check time: all five were still `QUEUED`.

## Dead ends
- The `finrank_maxGenEigenspace_eq` shortcut is not directly usable here because
  we still do not have an in-file proof that the recurrence polynomial
  `E.charPoly` agrees with the actual `LinearMap.charpoly` of `tupleSucc`.
- The helper statement for the disk eigenspace initially used the subtype norm of
  `(T^n) v` as a vector in `maxGenEigenspace`; this was the wrong type and had to
  be relaxed to the ambient norm on the coerced vector.

## Discovery
- The new helper
  `tupleSucc_minpoly_rootMultiplicity_eq_one_of_unit_eigenvalue` compiles and is
  enough to reduce the unit-circle problem to a restriction/minpoly argument on
  `Module.End.maxGenEigenspace`.
- The local Mathlib snapshot does not expose the planned
  `Polynomial.rootMultiplicity_le_of_dvd` name; the proof worked cleanly using
  `pow_rootMultiplicity_dvd` and `le_rootMultiplicity_iff`.

## Suggested next approach
- Prove that the restriction of `tupleSucc` to
  `Module.End.maxGenEigenspace T μ` has minimal polynomial dividing both
  `minpoly ℂ T` and a power of `X - C μ`; then use the new helper to conclude the
  restricted minimal polynomial divides `X - C μ`, giving
  `tupleSucc_eq_smul_on_unit_eigenspace`.
- If that closes, either:
  1. finish the disk-eigenspace estimate via nilpotent binomial expansion, or
  2. factor out the remaining combination step as a separate focused theorem about
     power-boundedness from generalized eigenspace decomposition.
