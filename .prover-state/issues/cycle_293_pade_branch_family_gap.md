# Issue: Padé branch-family seam now reduces to positive-count branch existence

## Blocker
The new helper lemmas in `OpenMath/PadeOrderStars.lean`

- `nonempty_padeR_realizedDownArrowInfinityWitnessFamily_iff`
- `nonempty_padeR_realizedUpArrowInfinityWitnessFamily_iff`

sharpen the remaining Padé-side gap. The branch-family goals no longer need to be
discussed as full `Fin`-indexed families: they reduce exactly to producing one
realized escaping branch when the corresponding infinity count is positive.

The concrete missing theorems are therefore:

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

Nothing in the current live hypotheses constructs such a branch. `IsPadeApproxToExp data`
still contains only order bookkeeping and local regularity, while a realized branch
needs:

- a concrete `GlobalDownArrowBranch (padeR n d)` or `GlobalUpArrowBranch (padeR n d)`,
- `BranchTracksRayNearOrigin` for its tangent angle,
- `EscapesEveryClosedBall` for the chosen support.

## Context
- `PadeRRealizedDownArrowInfinityWitnessFamily` and
  `PadeRRealizedUpArrowInfinityWitnessFamily` live in `OpenMath/PadeOrderStars.lean`.
- `RealizedDownArrowInfinityBranch` / `RealizedUpArrowInfinityBranch` live in
  `OpenMath/OrderStars.lean`.
- The new equivalences show that the family goal is equivalent to `count = 0` or
  `Nonempty` of the corresponding realized-branch type.
- Repo-wide search found no existing theorem proving:
  - `Nonempty (RealizedDownArrowInfinityBranch (padeR n d))`,
  - `Nonempty (RealizedUpArrowInfinityBranch (padeR n d))`,
  - or any concrete Padé theorem constructing the required global branch objects.

## What was tried
- Re-read the live blocker issue plus `OpenMath/PadeOrderStars.lean` and the
  realized-branch structures in `OpenMath/OrderStars.lean`.
- Triaged the ready cycle-292 Aristotle outputs first:
  - `2638aed1...` rejected: fabricated a missing-workspace obstruction instead of
    using the live repo.
  - `21eb66f3...` rejected: treated `IsPadeApproxToExp` as a function supplying
    branch witnesses, which does not match the live interface.
  - `c4280795...` rejected: same missing-workspace obstruction pattern as `2638...`.
  - `992f7e35...` and `1b6e0246...` were already incorporated in the live packaging
    layer before this cycle.
- Created and verified cycle-293 scratch files isolating the down-arrow, up-arrow,
  packaging, shared helper, and blocker-probe statements.
- Proved the helper reduction in scratch and moved it into `OpenMath/PadeOrderStars.lean`.

## Possible solutions
- Prove a concrete Padé theorem that a positive infinity count forces existence of a
  realized global branch of the correct direction for `orderWeb (padeR n d)`.
- If the real theorem is more geometric, first construct:
  - a `GlobalDownArrowBranch (padeR n d)` or `GlobalUpArrowBranch (padeR n d)`,
  - then prove `BranchTracksRayNearOrigin`,
  - then prove `EscapesEveryClosedBall`,
  and only afterwards package it as a realized branch.
- Keep the repair local to `OpenMath/PadeOrderStars.lean`; do not widen
  `IsPadeApproxToExp` and do not add surrogate fields to the branch structures.
