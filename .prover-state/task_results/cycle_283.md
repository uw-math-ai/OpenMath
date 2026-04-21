# Cycle 283 Results

## Worked on
- Mandatory Aristotle triage for:
  - `.prover-state/aristotle_results/6d853567-449b-470c-b000-f2004e7e736d`
  - `.prover-state/aristotle_results/5b0c3468-81a1-4ccb-b8b3-62b1aa5f5209`
  - `.prover-state/aristotle_results/3ec9c1fe-7549-430e-8c64-49ffb0ae1f9a`
- `OpenMath/OrderStars.lean`
- The concrete unit-level hypothesis feeding
  `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions`

## Approach
- Read `.prover-state/strategy.md` and the three required blocker issue files
  before editing.
- Inspected the three ready Aristotle result directories against the live
  `OpenMath/OrderStars.lean` interface.
- Rejected all three ready Aristotle bundles before proof work:
  - `6d853567-449b-470c-b000-f2004e7e736d` was a standalone generic
    `IsUpArrowDir` dispatcher artifact, not a clean patch against the live seam.
  - `5b0c3468-81a1-4ccb-b8b3-62b1aa5f5209` targeted the already-refuted inverse
    bridge `IsDownArrowDir -> exp (I * (p + 1) * θ) = ±1`.
  - `3ec9c1fe-7549-430e-8c64-49ffb0ae1f9a` was a separate cone-lemma artifact and
    not an incorporable patch to the live contradiction/package layer.
- Worked directly adjacent to the live seam by adding small helper lemmas that
  isolate what the current unit-level contradiction hypothesis really says on
  `orderWeb R`.
- Verified with:
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean`

## Result
- SUCCESS: all three mandated Aristotle result directories were triaged and
  rejected for the reasons above.
- SUCCESS: added the following live helper lemmas to `OpenMath/OrderStars.lean`:
  - `eq_one_of_mem_orderWeb_of_norm_eq_one`
  - `eq_exp_of_mem_orderWeb_of_norm_eq_one`
  - `no_nonzero_unit_points_on_orderWeb_iff_no_nonzero_eq_exp`
- SUCCESS: the live file now makes the unit-level exclusion concrete:
  on `orderWeb R`, the hypothesis
  `‖R z * exp (-z)‖ = 1 -> False` is equivalent to excluding nonzero points with
  `R z = exp z`.
- SUCCESS: `lake env lean OpenMath/OrderStars.lean` compiled cleanly after the edit.
- BLOCKED: I did not derive the concrete unit-level exclusion itself from the
  current rational-approximation data. The first unresolved input is now sharply
  isolated as a global nonzero coincidence exclusion for `R` against `exp` on
  `orderWeb R`.
- No fresh Aristotle submission was opened this cycle. After the required ready
  result triage, the only live progress available was the statement-level
  reduction above; the remaining gap is a global theorem-shape blocker rather
  than a proof-local sorry that Aristotle could consume directly without first
  inventing new interface content.

## Dead ends
- The inverse-classification route remains unusable: the current live
  norm-only `IsUpArrowDir` / `IsDownArrowDir` predicates do not imply
  `exp (I * (p + 1) * θ) = ±1`.
- The ready Aristotle outputs could not be repaired by local edits because their
  mismatch was at the statement/interface level, not at the proof-term level.
- I did not find a derivation of the nonzero coincidence exclusion from the
  current local asymptotic and cone-control lemmas alone.

## Discovery
- The unit-level hypothesis in the realized-branch contradiction is stronger and
  more concrete than it first appears: on `orderWeb R`, it is exactly a statement
  that `R` and `exp` have no common nonzero point.
- This converts the remaining gap from a norm-language obstruction into a global
  coincidence-exclusion problem for the concrete rational approximation.

## Suggested next approach
- Prove a concrete theorem excluding nonzero `R z = exp z` points on `orderWeb R`
  for the rational approximation under study.
- Then feed that result through
  `no_nonzero_unit_points_on_orderWeb_iff_no_nonzero_eq_exp`.
- After that, revisit whether the separate `0`-support exclusion is truly the next
  missing input, or whether the same concrete nondegeneracy argument also handles it.
