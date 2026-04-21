# Issue: concrete Padé Ehle barrier still needs `EhleBarrierInput`

## Blocker
The first honest concrete Padé-side Ehle theorem has now been reduced to the
minimal live seam

- `PadeREhleBarrierNatInput n d data`
- `ehle_barrier_nat_of_padeR_of_natInput`

in `OpenMath/PadeOrderStars.lean`.

That refinement shows the exact remaining blocker: a real `padeR` application
of the Ehle barrier still needs a concrete proof of `EhleBarrierInput data`.
The heavier Padé-side fields

- `RealizesInfinityBranchGerms (padeR n d) data`
- `ConcreteRationalApproxToExp (padeR n d) data`

are not part of the theorem-local dependency for `ehle_barrier_nat_of_padeR`
itself; they are only used by the sibling 355D/355E' wrappers.

## Context
- Live theorem audit in `OpenMath/PadeOrderStars.lean`:
  - `thm_355D_of_padeR`
  - `thm_355E'_of_padeR`
  - `concreteRationalApproxToExp_of_padeR`
  - `PadeREhleBarrierInput`
  - `PadeREhleBarrierNatInput`
  - `ehle_barrier_nat_of_padeR_of_natInput`
  - `ehle_barrier_nat_of_padeR`
- `PadeREhleBarrierInput.thm_355D` and `.thm_355E'` genuinely consume the full
  Padé bundle.
- `PadeREhleBarrierInput.ehle_barrier_nat` reduces immediately to the smaller
  `PadeREhleBarrierNatInput`, so the live wedge theorem depends only on:
  - `data.numeratorDegree = n`
  - `data.denominatorDegree = d`
  - `EhleBarrierInput data`
- `EhleBarrierInput data` itself still packages the missing concrete 355G-side
  correction-term witnesses:
  - the zero-side correction theorem
  - the pole-side correction theorem

## What was tried
- Re-read `OpenMath/OrderStars.lean`, `OpenMath/PadeOrderStars.lean`, and the
  current plan before editing.
- Audited the three ready Aristotle directories first and rejected them as
  instructed because none supplied a live delta for this seam.
- Followed the live dependency chain and checked which fields of
  `PadeREhleBarrierInput` are actually used by `ehle_barrier_nat_of_padeR`.
- Landed the smallest honest local refinement:
  - added `PadeREhleBarrierNatInput`
  - added `PadeREhleBarrierInput.toNatInput`
  - added `PadeREhleBarrierNatInput.ehle_barrier_nat`
  - added `ehle_barrier_nat_of_padeR_of_natInput`
  - rewired `ehle_barrier_nat_of_padeR` through the smaller seam

## Possible solutions
- Prove the zero-side 355G correction-term theorem for concrete Padé/order-star
  data and package it into `EhleBarrierInput data`.
- Prove the pole-side analogue.
- Once those two theorems exist, build a concrete Padé constructor for
  `PadeREhleBarrierNatInput n d data` directly from:
  - the degree equalities
  - the Padé/A-stability assumptions
  - the new zero-side and pole-side correction-term theorems
