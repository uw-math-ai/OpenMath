# Issue: `PadeRConcreteNoEscapeInput` still lacks a live producer

## Blocker
Cycle 299 introduced the new Padé-local bundle
`PadeRConcreteNoEscapeInput n d data` in `OpenMath/PadeOrderStars.lean`.
This is now the first honest missing theorem surface below
`ConcreteRationalApproxToExp`.

The blocker is no longer packaging. The blocker is that no current live theorem
produces this structure from the interfaces already available for Padé data.

## Context
- Live file:
  - `OpenMath/PadeOrderStars.lean`
- New structure:
  - `PadeRConcreteNoEscapeInput n d data`
- New bridge methods:
  - `PadeRConcreteNoEscapeInput.realizesInfinityBranchGerms`
  - `PadeRConcreteNoEscapeInput.concrete`
  - `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms`
- Current downstream consumers:
  - `PadeREhleBarrierInput.noEscape`
  - `PadeREhleBarrierInput.thm_355D`
  - `PadeREhleBarrierInput.thm_355E'`

The new structure makes the remaining fields explicit:
- realized down-arrow infinity witness family
- realized up-arrow infinity witness family
- continuity of `z ↦ ‖padeR n d z * exp (-z)‖`
- zero excluded from realized down-branch support
- zero excluded from realized up-branch support
- nonzero exact coincidence exclusion on `orderWeb (padeR n d)`
- local down-arrow cone sign control
- local up-arrow cone sign control
- far-field plus sign on `orderWeb (padeR n d)`
- far-field minus sign on `orderWeb (padeR n d)`

## What was tried
- Re-read the live `OrderStars` contradiction seam and the Padé wrapper chain.
- Rejected the five cycle-298 Aristotle outputs again because they still depend
  on fake fields or rebuilt `OpenMath` modules.
- Refactored the Padé-side seam so the no-escape content is carried by the new
  structure instead of being spread across `PadeREhleBarrierInput`.
- Added the theorem-local constructor
  `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms`, which proves the
  packaging layer is no longer the issue.

## Why the live interfaces are insufficient
- `IsPadeApproxToExp data` supplies approximation bookkeeping, not the analytic
  contradiction fields listed above.
- `RealizesInfinityBranchGerms (padeR n d) data` supplies only the two realized
  witness families.
- Even together, those interfaces do not mention:
  - support exclusion of `0`
  - local cone sign inequalities
  - far-field sign inequalities

So the first missing theorem is not a new wrapper. It is a genuine analytic
feeder theorem proving at least one field of `PadeRConcreteNoEscapeInput`.

## Possible solutions
- Prove one field of `PadeRConcreteNoEscapeInput` at a time rather than aiming
  for the entire bundle immediately.
- Candidate next targets:
  - `∀ branch : RealizedDownArrowInfinityBranch (padeR n d),
      (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support`
  - `∀ branch : RealizedUpArrowInfinityBranch (padeR n d),
      (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support`
  - one local cone-sign theorem for a realized down/up direction
  - one far-field sign theorem on large `orderWeb (padeR n d)` points
- Once any one of those fields is proved honestly, keep using
  `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms` to assemble the
  higher-level seam without changing `OpenMath/OrderStars.lean`.
