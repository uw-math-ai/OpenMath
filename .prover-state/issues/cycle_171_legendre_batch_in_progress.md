# Issue: Cycle 171 Legendre batch still waiting on bridge-level Aristotle output

## Blocker
`OpenMath/Legendre.lean` still has the same two generic `sorry`s:
- `ButcherTableau.gaussLegendre_B_double`
- `ButcherTableau.gaussLegendreNodes_of_B_double`

Cycle 171 did not expose a new local Lean error. The blocking issue is still
the missing bridge/package around shifted Legendre polynomials, and the fresh
Aristotle batch was still `IN_PROGRESS` at the single result check.

## Context
- The planner CI failure `24641918796` was stale:
  - failed commit: `ff5b2b124b325b4eef636d308baf1885a2d147df`
  - current `main`: `8aea4bc23c4d19b4ddfc5274726e1aa387a03c29`
  - local `lake build` succeeds on current `main`
- Current file status:
  - `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/Legendre.lean`
    compiles with only the two existing `sorry` warnings
- Ready Aristotle results checked first:
  - `705b435b-fe19-4f1b-9bf1-9d3fd31c7158`
  - `71a95770-f792-434e-b7bc-dfd9ca377a9e`
- Those bundles were not directly usable because they replaced the current
  recursive `shiftedLegendreP` setup with standalone alternate `OpenMath/Legendre.lean`
  files rather than producing a patch compatible with the repo’s current theorem statements.

Fresh batch submitted this cycle:
- `819194af-66fe-4d07-90ce-35de882ff419` — sign-correct bridge
- `53cb0348-b54f-4867-bc0b-577b3c3ee630` — node/root reformulation
- `679726ac-461a-49a9-be03-3a6f13dbb5fe` — division by shifted Legendre polynomial
- `ea375b78-11b6-4ed8-9526-ee3e7beff5df` — orthogonality on `[0,1]`
- `ea7b7617-ff30-49b0-bfca-40ed3c9d91c4` — forward/backward reduction theorems

Single status check in this cycle:
- all five remained `IN_PROGRESS`

## What was tried
- Verified the current CI/workflow situation instead of assuming the planner’s run
  still matched `main`.
- Read the two ready Aristotle output bundles first.
- Diffed their generated `OpenMath/Legendre.lean` files against the current repo file.
- Revalidated the five scratch files in `.prover-state/aristotle/cycle_165/` with
  `lake env lean`, confirming they compile with `sorry`.
- Submitted all five as a new batch and performed one status refresh.

## Possible solutions
- Next worker should start by refreshing the five project IDs above and harvesting
  any completed output directories.
- If the bridge theorem lands, integrate it first and only then revisit
  `gaussLegendre_B_double`.
- If only the converse job remains weak, split work:
  - close `gaussLegendre_B_double` in-project
  - leave `gaussLegendreNodes_of_B_double` behind a stronger hypotheses issue
