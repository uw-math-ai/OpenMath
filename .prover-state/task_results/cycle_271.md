# Cycle 271 Results

## Worked on
`OpenMath/OrderStars.lean` at the 355D / 355E no-infinity seam.

Before editing, I checked the ready cycle-270 Aristotle outputs:

- `66167b58-797d-44f0-983e-2c0fbd05cf65`
- `d3adc045-24ad-4e7b-b359-ead17e3e3b66`
- `b9168a5f-4f38-438b-b4b7-0c397208696d`
- `75695185-2285-4608-bf9b-690862c79283`
- `573a9fe3-809a-42c5-bfab-17b2f3773970`

Those files are already incorporated in live code or only contain trivial
projection/packaging proofs around cycle-270 finite-endpoint work. None contained a
stronger no-infinity theorem to merge.

## Approach
1. Read the required seam in `OpenMath/OrderStars.lean`, the two no-escape issues,
   `cycle_270.md`, and the current `plan.md` target section.
2. Added the minimal branch-level scaffold adjacent to `NoArrowsEscapeToInfinity`:
   - `GlobalOrderArrowBranch`
   - `GlobalDownArrowBranch`
   - `GlobalUpArrowBranch`
   - `OrderArrowFiniteEndpointKind`
   - `OrderArrowFiniteEndpoint`
   - `EscapesEveryClosedBall`
   - `HasFiniteEndpoint`
   - `DownArrowInfinityWitnesses`
   - `UpArrowInfinityWitnesses`
3. Stated the fresh theorem family with explicit `sorry`s:
   - `downArrowBranch_hasFiniteEndpoint_or_escapesToInfinity`
   - `upArrowBranch_hasFiniteEndpoint_or_escapesToInfinity`
   - `noDownArrowBranchEscapesToInfinity_of_rationalApprox`
   - `noUpArrowBranchEscapesToInfinity_of_rationalApprox`
   - plus the count-level corollaries
     `noDownArrowEscapesToInfinity_of_rationalApprox`,
     `noUpArrowEscapesToInfinity_of_rationalApprox`,
     `noArrowsEscapeToInfinity_of_rationalApprox`
4. Verified the scaffold compiles, then built `OpenMath.OrderStars` so the scratch
   Aristotle files could import it.
5. Submitted a fresh five-file Aristotle batch under
   `.prover-state/aristotle/cycle_271/`, slept 30 minutes, and refreshed status
   exactly once.

Fresh Aristotle submissions:

- `843a4b82-5d68-4c20-97d8-452545a2ac42`
- `04537f3f-864a-4da9-a49d-f9c8ee16dbad`
- `d6a3f01c-97ab-4ddf-87d6-cd52042eee81`
- `4a04dd7f-9552-415d-ba74-0de1da9aeaf3`
- `01f3a18b-cab1-497b-b7ee-ddb7a6456ca0`

## Result
SUCCESS on the cycle minimum: `OpenMath/OrderStars.lean` now contains a compileable
no-escape scaffold with fresh explicit `sorry`s and the count-level target theorem
`noArrowsEscapeToInfinity_of_rationalApprox`.

Aristotle outcome after the single post-wait refresh:

- `843a4b82...`: `COMPLETE_WITH_ERRORS`
- `04537f3f...`: `COMPLETE_WITH_ERRORS`
- `d6a3f01c...`: `COMPLETE_WITH_ERRORS`
- `4a04dd7f...`: `COMPLETE_WITH_ERRORS`
- `01f3a18b...`: still `IN_PROGRESS` at the single allowed check, so I did not poll it again

I extracted the four completed results. None were usable in the live file:

- the endpoint-dichotomy jobs replaced the live branch structures with stronger
  axiomatized fields like `branch.dichotomy` / `branch.converges_in_alexandroff`;
- the branch no-escape jobs replaced the live scaffold with stronger boundedness
  fields like `branch.isBounded`.

So no Aristotle proof was incorporated into `OpenMath/OrderStars.lean` this cycle.

## Dead ends
- The fresh branch no-escape theorems currently quantify over a concrete function
  `R : ℂ → ℂ` and concrete branches of `orderWeb R`, but
  `IsRationalApproxToExp data` still only constrains the abstract count data.
- Because of that mismatch, Aristotle consistently "fixed" the problem by inventing
  new stronger fields rather than proving the live statements.
- I did not simplify the 355D boundary or change downstream APIs, because
  `NoArrowsEscapeToInfinity data` was not discharged this cycle.

## Discovery
The next blocker is narrower than the existing generic topology issue:

- we do not merely need a proof of no-escape;
- we first need a small realization interface relating a concrete stability function
  `R` and its global order-web branches to `OrderArrowTerminationData`.

Without that bridge, the branch-level theorems are not sufficiently tied to the
count data for either Aristotle or manual proof work to start cleanly.

## Suggested next approach
- Add the smallest possible `R ↔ data` realization interface, adjacent to the new
  scaffold, saying which concrete global branches are the arrows counted by
  `OrderArrowTerminationData`.
- Then restate or refine the branch no-escape theorem so its hypotheses actually
  constrain the concrete branch geometry of `orderWeb R`.
- Reuse the current witness predicates and count-level corollaries once that bridge
  exists; do not reopen the finite-endpoint packaging.
