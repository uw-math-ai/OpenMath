# Cycle 270 Results

## Worked on
`OpenMath/OrderStars.lean` at the 355D finite-endpoint boundary:
- added `OrdinaryFinitePointLocalRegularity`
- added the bridge lemmas
  `noDownArrowTerminatesAtOrdinaryFinitePoint`,
  `noUpArrowTerminatesAtOrdinaryFinitePoint`,
  `finiteArrowEndpointsClassified_of_localRegularity`,
  `thm_355D_of_localRegularity`
- rewired `IsRationalApproxToExp` so it carries `localRegularity` instead of the
  opaque field `finiteEndpointsClassified`
- rewired `thm_355D` to derive finite endpoint classification explicitly from the
  local-regularity theorem path

I also prepared and archived a fresh five-file Aristotle batch under
`.prover-state/aristotle/cycle_270/`.

## Approach
Followed the required sorry-first workflow literally:
1. inserted the new local-regularity scaffold in `OpenMath/OrderStars.lean` with
   four fresh `sorry`s;
2. verified `lake env lean OpenMath/OrderStars.lean` passed with those `sorry`s;
3. created five self-contained Aristotle scratch files for:
   - down-arrow local regularity
   - up-arrow local regularity
   - `finiteArrowEndpointsClassified_of_localRegularity`
   - `thm_355D_of_localRegularity`
   - `finiteArrowEndpointsClassified_of_rationalApprox`
4. submitted all five jobs, slept 30 minutes, and checked status exactly once;
5. harvested the returned proofs and removed the live `sorry`s in
   `OpenMath/OrderStars.lean`.

Fresh Aristotle submissions:
- `66167b58-797d-44f0-983e-2c0fbd05cf65`
- `d3adc045-24ad-4e7b-b359-ead17e3e3b66`
- `b9168a5f-4f38-438b-b4b7-0c397208696d`
- `75695185-2285-4608-bf9b-690862c79283`
- `573a9fe3-809a-42c5-bfab-17b2f3773970`

## Result
SUCCESS

The 355D boundary is now one step sharper in live Lean code:
- `IsRationalApproxToExp` no longer carries `FiniteArrowEndpointsClassified data`
  as an unexplained field;
- there is now a named theorem path from local regularity to finite endpoint
  classification;
- `thm_355D` explicitly derives the finite-endpoint part and leaves
  `NoArrowsEscapeToInfinity data` as the only remaining opaque global trajectory
  hypothesis.

All five Aristotle jobs completed. Their returned proofs were usable but trivial:
each one reduced to direct projection/packaging from the new local-regularity
structure. I copied that information into the live proofs and also updated the
cycle-270 scratch files to be sorry-free.

Verification passed:
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderStars.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build`
- all five files in `.prover-state/aristotle/cycle_270/` compile with
  `lake env lean`

## Dead ends
The new `OrdinaryFinitePointLocalRegularity` interface is still only a minimal
scaffold around the bookkeeping layer. Because the file still has no branch or
point-level formalization of ordinary finite nonsingular order-web points, the
Aristotle proofs could only discharge the interface by projection rather than by
real geometry.

I did not open a new blocker issue because the existing issue
`.prover-state/issues/order_star_finite_endpoint_local_regularity.md` still
describes the remaining mathematical gap accurately.

## Discovery
The narrowest clean refactor is to make local regularity the explicit hypothesis of
`IsRationalApproxToExp` and prove `FiniteArrowEndpointsClassified data` from it by a
named theorem. That makes the 355D boundary clearer even before the genuine local
geometry is formalized.

The actual unsolved mathematics is now cleaner to state:
- replace the abstract `OrdinaryFinitePointLocalRegularity` wrapper with a truly
  geometric local continuation theorem for ordinary finite nonsingular points;
- separately prove `NoArrowsEscapeToInfinity data`.

## Suggested next approach
Keep working in `OpenMath/OrderStars.lean`, but the next cycle should sharpen the
new scaffold rather than add more count-only bookkeeping:
- introduce the smallest pointwise/order-web notion needed to state local
  continuation at an ordinary finite nonsingular point;
- prove that theorem implies the current `OrdinaryFinitePointLocalRegularity`
  wrapper or directly replaces it;
- once that layer is genuine, move to the remaining global hypothesis
  `NoArrowsEscapeToInfinity data`.
