# Issue: No-escape scaffold lacks an `R`-to-count realization bridge

## Blocker
The cycle-271 no-escape scaffold in `OpenMath/OrderStars.lean` now has concrete
branch objects

- `GlobalDownArrowBranch R`
- `GlobalUpArrowBranch R`
- `EscapesEveryClosedBall`
- `HasFiniteEndpoint`

and count-level witness predicates

- `DownArrowInfinityWitnesses R data`
- `UpArrowInfinityWitnesses R data`.

But the core branch theorems

- `noDownArrowBranchEscapesToInfinity_of_rationalApprox`
- `noUpArrowBranchEscapesToInfinity_of_rationalApprox`

are still underspecified: `IsRationalApproxToExp data` only constrains the abstract
count data, while the branch theorems quantify over a concrete stability function
`R` and concrete branches of `orderWeb R`. There is currently no hypothesis linking
those two layers.

## Context
- Live scaffold added in cycle 271 is adjacent to the existing
  `NoArrowsEscapeToInfinity` seam in `OpenMath/OrderStars.lean`.
- The count-level theorems
  `noDownArrowEscapesToInfinity_of_rationalApprox`,
  `noUpArrowEscapesToInfinity_of_rationalApprox`, and
  `noArrowsEscapeToInfinity_of_rationalApprox`
  are now structurally correct once the branch-level no-escape statements exist.
- The remaining mismatch is specifically between:
  - branch geometry of a concrete `R : ℂ → ℂ`, and
  - the abstract bookkeeping object `OrderArrowTerminationData`.

## What was tried
- Added the smallest branch-level scaffolding needed to talk about:
  - a connected global branch,
  - leaving every closed ball,
  - finite endpoint labels.
- Added witness predicates from infinity counts back to concrete branches.
- Submitted five Aristotle jobs on the new scaffold:
  - `843a4b82-5d68-4c20-97d8-452545a2ac42`
  - `04537f3f-864a-4da9-a49d-f9c8ee16dbad`
  - `d6a3f01c-97ab-4ddf-87d6-cd52042eee81`
  - `4a04dd7f-9552-415d-ba74-0de1da9aeaf3`
  - `01f3a18b-cab1-497b-b7ee-ddb7a6456ca0`
- The four completed Aristotle outputs were unusable in the live file because they
  all repaired the statement by inventing stronger replacement fields such as:
  - `branch.dichotomy`
  - `branch.isBounded`
  - `branch.converges_in_alexandroff`

This is evidence that the present live theorem statements are not merely hard; they
still need one more small interface layer connecting `R` to the counted data.

## Possible solutions
- Introduce a minimal realization interface `R ↔ data` saying which concrete global
  branches of `orderWeb R` are the arrows counted by `OrderArrowTerminationData`.
- Alternatively, parameterize the branch no-escape theorem by a rational-approximation
  hypothesis on `R` itself, and keep the count-level corollaries on `data`.
- Once that bridge exists, the current witness predicates should be enough to derive
  `NoArrowsEscapeToInfinity data` without reopening the finite-endpoint packaging.
