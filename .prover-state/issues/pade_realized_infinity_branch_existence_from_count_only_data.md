# Issue: Padé realized infinity-branch existence is still underspecified from count-only data

## Blocker
After the live support-level and direction-level Padé helpers, the first honest
missing theorem is now realized-branch existence, not a count-to-direction
bridge.

The concrete missing targets are:

```lean
theorem padeR_nonempty_realizedDownArrowInfinityBranch_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    Nonempty (RealizedDownArrowInfinityBranch (padeR n d))

theorem padeR_nonempty_realizedUpArrowInfinityBranch_of_upArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.upArrowsAtInfinity) :
    Nonempty (RealizedUpArrowInfinityBranch (padeR n d))
```

These statements do not follow from the current hypotheses. The only live input
is count-only:

```lean
0 < data.downArrowsAtInfinity
0 < data.upArrowsAtInfinity
```

but a realized infinity branch is `R`-dependent data:

- a concrete `GlobalDownArrowBranch (padeR n d)` or `GlobalUpArrowBranch (padeR n d)`,
- a `BranchTracksRayNearOrigin` proof for its tangent angle,
- an `EscapesEveryClosedBall` proof for its support.

## Context
- `OpenMath/PadeOrderStars.lean` already contains:
  - `padeR_exists_downArrowDir`
  - `padeR_exists_upArrowDir`
  - `padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos`
  - `padeR_exists_globalUpArrowBranch_of_upArrowsAtInfinity_pos`
- Those theorems close the older support/direction gap, but they do not produce
  a realized escaping branch.
- Cycle 319 added the explicit theorem-local seam:

```lean
structure PadeRInfinityBranchExistenceInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  downBranch_of_downArrowsAtInfinity_pos :
    0 < data.downArrowsAtInfinity →
      Nonempty (RealizedDownArrowInfinityBranch (padeR n d))
  upBranch_of_upArrowsAtInfinity_pos :
    0 < data.upArrowsAtInfinity →
      Nonempty (RealizedUpArrowInfinityBranch (padeR n d))
```

This packages the exact missing theorem-local input and reconstructs
`RealizesInfinityBranchGerms (padeR n d) data` once those branch witnesses are
available.

## What was tried
- Re-read the live seam around:
  - `PadeRRealizedDownArrowInfinityWitnessFamily`
  - `PadeRRealizedUpArrowInfinityWitnessFamily`
  - `realizesInfinityBranchGerms_of_padeR`
  - `realizesInfinityBranchGermsEquiv_of_padeR`
- Confirmed that the planner's suspected direction gap is already closed by the
  live `padeR_exists_downArrowDir` and `padeR_exists_upArrowDir`.
- Searched `OpenMath/OrderStars.lean` for any generic upgrade from
  `GlobalDownArrowBranch` / `GlobalUpArrowBranch` to realized escaping branches;
  none exists.
- Triaged Aristotle bundle `8400a088-090d-4146-aa1b-1fb094da08b3`:
  - `OpenMath/Pade.lean` in the bundle replaces the live Padé interface with a
    small piecewise toy definition of `padeR`.
  - `OpenMath/OrderStars.lean` in the bundle replaces the live near-origin
    `IsUpArrowDir` notion with a large-radius asymptotic definition.
  - The exact-ray proof therefore does not replay directly against the live
    interfaces and was rejected.

## Possible solutions
- Prove one field of `PadeRInfinityBranchExistenceInput` honestly from
  additional branch-level hypotheses that mention `padeR n d`, not just `data`.
- If the real input is geometric, target a theorem-local producer of:
  - a concrete global Padé branch,
  - local germ tracking for its tangent angle,
  - and escape to infinity for its support,
  then package that as a realized branch.
- Do not revisit the already-solved count-to-direction bridge, and do not widen
  `OrderArrowTerminationData` or replace `OrderStars` interfaces to smuggle in
  the missing branch data.
