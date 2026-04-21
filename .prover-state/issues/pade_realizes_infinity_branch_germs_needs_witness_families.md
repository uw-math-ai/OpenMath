# Issue: Padé infinity-branch germs still need concrete witness families

## Blocker
The next Padé-side seam target

```lean
RealizesInfinityBranchGerms (padeR n d) data
```

is now decomposed explicitly in `OpenMath/PadeOrderStars.lean`, but the live
mathematics still does not produce the two required witness families:

```lean
PadeRRealizedDownArrowInfinityWitnessFamily n d data
PadeRRealizedUpArrowInfinityWitnessFamily n d data
```

The currently available Padé/count hypotheses such as
`data.numeratorDegree = n`, `data.denominatorDegree = d`, and
`IsPadeApproxToExp data` do not mention concrete global branches of
`orderWeb (padeR n d)` at all, so they are not enough to construct
`RealizedDownArrowInfinityBranch (padeR n d)` or
`RealizedUpArrowInfinityBranch (padeR n d)` witnesses.

## Context
- Live narrowing added in `OpenMath/PadeOrderStars.lean`:
  - `PadeRRealizedDownArrowInfinityWitnessFamily`
  - `PadeRRealizedUpArrowInfinityWitnessFamily`
  - `realizesInfinityBranchGerms_of_padeR`
  - `realizesInfinityBranchGermsEquiv_of_padeR`
- The new equivalence shows the exact remaining gap:

```lean
RealizesInfinityBranchGerms (padeR n d) data ≃
  (PadeRRealizedDownArrowInfinityWitnessFamily n d data ×
    PadeRRealizedUpArrowInfinityWitnessFamily n d data)
```

- `IsPadeApproxToExp data` only constrains the bookkeeping object `data`
  (`order_eq`, `order_le`, `localRegularity`); it does not connect `data` to
  any actual `GlobalDownArrowBranch` / `GlobalUpArrowBranch` of `padeR n d`.
- `ConcreteRationalApproxToExp (padeR n d) data` is downstream of
  `RealizesInfinityBranchGerms (padeR n d) data`, so it cannot be used to
  manufacture the missing witnesses.

## What was tried
- Added a sorry-first Padé-local decomposition in `OpenMath/PadeOrderStars.lean`
  and verified the scaffold with `lake env lean OpenMath/PadeOrderStars.lean`.
- Submitted the required five-file Aristotle batch:
  - `2638aed1-59b0-4174-b79c-66b4b8bf9587`
  - `21eb66f3-ea37-405c-b79c-ad80399619f1`
  - `c4280795-c516-4989-a5d2-fdaf850d8b5f`
  - `992f7e35-e2d5-4314-95ea-ec27fea1b818`
  - `1b6e0246-a0dd-42d6-abb9-872f758d55e0`
- After the mandated 30-minute wait and single refresh:
  - the down/up/main witness jobs either failed to reproduce the workspace or
    fabricated replacement `OpenMath` modules / surrogate interfaces,
  - only the trivial packaging/equivalence jobs were usable, and those are now
    incorporated into the live file.

## Possible solutions
- Prove a new concrete Padé-side realization theorem that actually constructs a
  `GlobalDownArrowBranch` / `GlobalUpArrowBranch` of `orderWeb (padeR n d)`
  escaping every closed ball and tracking the local germ near the origin.
- If that is too global at once, first prove theorem-local hypotheses that for
  each counted infinity endpoint in `data` there exists a corresponding realized
  branch witness of the right direction, then package them via
  `realizesInfinityBranchGerms_of_padeR`.
- Keep the repair local to `OpenMath/PadeOrderStars.lean`; do not widen
  `IsPadeApproxToExp` or redesign `OrderStars` interfaces just to hide the gap.
