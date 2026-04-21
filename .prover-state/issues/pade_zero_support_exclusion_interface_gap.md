# Issue: Padé zero-support exclusion is not forced by the realized-branch interface

## Blocker
The current realized-branch interface is closed under adjoining `{0}` to the
tracked support. Because `padeR n d 0 = 1`, the origin lies on
`orderWeb (padeR n d)`, so this support enlargement preserves every field of a
realized escaping Padé branch.

Therefore the fields

- `zero_not_mem_down_support`
- `zero_not_mem_up_support`

in `PadeRConcreteNoEscapeInput` are not derivable from the present
`RealizedDownArrowInfinityBranch` / `RealizedUpArrowInfinityBranch` interface
alone.

## Context
- Live file:
  - `OpenMath/PadeOrderStars.lean`
- Relevant branch interface from `OpenMath/OrderStars.lean`:
  - `GlobalOrderArrowBranch`
  - `BranchTracksRayNearOrigin`
  - `RealizedDownArrowInfinityBranch`
  - `RealizedUpArrowInfinityBranch`
- Cycle-300 audit lemmas added in `OpenMath/PadeOrderStars.lean`:
  - `padeR_exists_realizedDownArrowInfinityBranch_with_zero_mem_support`
  - `padeR_exists_realizedUpArrowInfinityBranch_with_zero_mem_support`

## What was tried
- Re-read the live branch interface and the Padé no-escape seam.
- Audited the exact countermodel suggested by the planner: replace a realized
  branch support `S` by `S ∪ {0}`.
- Formalized the audit on the Padé side instead of only arguing informally.

## `support ∪ {0}` countermodel argument
Let `branch` be a realized escaping down- or up-arrow branch for `padeR n d`.
Define the new support

`S' := branch.branch.toGlobalOrderArrowBranch.support ∪ {0}`.

Then every realized-branch field still holds:

- Connectedness:
  - the old support is connected
  - `0 ∈ closure support` is already a field of `GlobalOrderArrowBranch`
  - hence `support ∪ {0}` is still connected
- Order-web support:
  - the old support already lies in `orderWeb (padeR n d)`
  - `padeP_eval_zero` and `padeQ_eval_zero` give `padeR n d 0 = 1`
  - therefore `0 ∈ orderWeb (padeR n d)`
- Branch tracking near the origin:
  - `BranchTracksRayNearOrigin` only asks for nonempty intersections with cone
    neighborhoods
  - enlarging support cannot destroy those witnesses
- Escape to infinity:
  - `EscapesEveryClosedBall` only asks for sufficiently large support points
  - enlarging support cannot destroy those witnesses

So from any realized branch one can build another realized branch whose support
contains `0`.

## Why this blocks the current target
The cycle-300 target fields are universal support exclusions:

- `∀ branch : RealizedDownArrowInfinityBranch (padeR n d), 0 ∉ support`
- `∀ branch : RealizedUpArrowInfinityBranch (padeR n d), 0 ∉ support`

But the current interface itself admits realized branches with `0 ∈ support`
once any realized branch exists, by the construction above. So those exclusion
fields cannot come from the present branch interface alone.

## Blocker classification
The blocker is interface-level for the current realized-branch notion.

It is still potentially recoverable from extra Padé-specific hypotheses not yet
in the seam, but only as additional input beyond the present realized-branch
records. The cycle-300 local seam split reflects this by isolating
`PadeRZeroSupportExclusionInput` as a separate Padé-local bundle.

## Possible solutions
- Keep the current `OrderStars` interface unchanged and treat zero-support
  exclusion as explicit extra Padé-local input.
- Prove a genuinely Padé-specific theorem ruling out `0` from realized branch
  supports using analytic information not currently stored in the realized
  branch records.
- Do not attempt to derive zero-support exclusion from
  `RealizesInfinityBranchGerms` alone; the cycle-300 audit shows that route is
  false.
