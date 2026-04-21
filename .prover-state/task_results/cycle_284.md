# Cycle 284 Results

## Worked on
- `OpenMath/OrderStars.lean` at the exact coincidence / realized-branch contradiction seam.
- The sharper hypothesis path below
  `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions`.

## Approach
- Read the cycle-284 strategy and the four binding blocker issues first.
- Re-read the live seam around:
  - `eq_exp_of_mem_orderWeb_of_norm_eq_one`
  - `no_nonzero_unit_points_on_orderWeb_iff_no_nonzero_eq_exp`
  - `realizedDownArrowInfinityBranch_contradiction`
  - `realizedUpArrowInfinityBranch_contradiction`
  - `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions`
- Added seam-local wrappers that consume the sharper exact-coincidence statement
  `∀ z ≠ 0, z ∈ orderWeb R → R z = exp z → False`
  directly and route it through the cycle-283 equivalence.
- Recompiled with:
  `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderStars.lean`
- Submitted a five-file Aristotle scratch batch against the live interface:
  - `40100c59-47ab-46a0-a41d-476a1d0626d4`
  - `2d4e2259-f858-44c6-a65e-d9dff606301e`
  - `0cdf5b9a-65a6-4c77-85e4-097595e4d057`
  - `478be5a7-9b1b-4814-b3d5-784dc45ac547`
  - `a937370e-0b94-43f2-bcc9-1ebeef9eace8`
- Refreshed all five jobs once after submission.
- Ran a numerical sanity check on `backwardEulerR` to see whether the sharpened
  exact-coincidence exclusion could possibly hold for an arbitrary `R`.

## Result
- SUCCESS: added live theorem(s) removing the unit-level hypothesis from the
  concrete contradiction/package seam:
  - `realizedDownArrowInfinityBranch_contradiction_of_no_nonzero_eq_exp`
  - `realizedUpArrowInfinityBranch_contradiction_of_no_nonzero_eq_exp`
  - `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions_of_no_nonzero_eq_exp`
- `OpenMath/OrderStars.lean` compiles cleanly after the change.
- Aristotle status after the single allowed refresh:
  - all five cycle-284 projects remained `QUEUED`
  - no result was ready to incorporate this cycle

## Dead ends
- I did not find any live theorem in `OrderStars.lean` or adjacent files that
  controls the nonzero zero set of `fun z => exp z - R z`.
- The sharpened theorem
  `∀ z ≠ 0, z ∈ orderWeb R → R z = exp z → False`
  cannot be derived from the present arbitrary-`R` interface alone.
- Numerical evidence shows why: `backwardEulerR z = exp z` has a nonzero complex
  solution near `z ≈ -4.06479569417 - 58.03240937970 i`, so any theorem with no
  extra concrete hypotheses on `R` is false.

## Discovery
- The old unit-level contradiction input has now been fully removed from the
  live contradiction/package seam; the only remaining gap is the exact
  coincidence exclusion itself.
- The missing theorem is genuinely global and `R`-specific. The local asymptotic
  lemmas near `0`, the cone-control lemmas, and the realized-branch topology do
  not imply it.

## Suggested next approach
- Keep the new exact-coincidence wrapper theorems unchanged.
- Make the intended concrete rational approximation `R` explicit at this seam
  and prove a genuinely `R`-specific theorem excluding nonzero zeros of
  `exp - R` on `orderWeb R`.
- Do not try to prove the exclusion from only the existing generic local
  hypotheses, and do not reopen the already-refuted inverse
  `IsUpArrowDir` / `IsDownArrowDir` classification route.
