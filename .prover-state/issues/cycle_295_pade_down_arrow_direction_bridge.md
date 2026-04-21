# Issue: Padé down-arrow direction bridge is still missing after support construction

## Blocker
The support-level blocker in `OpenMath/PadeOrderStars.lean` is now closed:

```lean
theorem padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos
```

is proved in live code by taking `support = {0}`, since `padeR n d 0 = 1` puts
`0` on `orderWeb (padeR n d)`.

The next exact missing theorem boundary is now the direction bridge:

```lean
theorem padeR_exists_downArrowDir_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ
```

Without such a `θ`, the new live packaging lemma

```lean
theorem padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos_of_exists_downArrowDir
```

cannot be applied, so the chain to `GlobalDownArrowBranch`, tracking, escape,
and `RealizedDownArrowInfinityBranch` remains blocked.

## Context
- `OpenMath/PadeOrderStars.lean` now contains:
  - `padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos`
  - `padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos_of_exists_downArrowDir`
- The abstract hypotheses still do not mention `padeR n d`:
  - `OrderArrowTerminationData` records only counts and arithmetic bookkeeping.
  - `IsRationalApproxToExp data` and `IsPadeApproxToExp data` in
    `OpenMath/OrderStars.lean` are still `data`-only structures.
- So neither

```lean
0 < data.downArrowsAtInfinity
```

nor the current Padé bookkeeping interface can by itself manufacture an
`R`-dependent theorem about `IsDownArrowDir (padeR n d) θ`.

## What was tried
- Proved the live support theorem directly by using the singleton support `{0}`.
- Proved the live branch-packaging theorem showing that once a real down-arrow
  direction exists, the global branch support can be assembled immediately.
- Re-read the generic direction theorems in `OpenMath/OrderStars.lean`:
  - `arrow_down_of_pos_errorConst`
  - `arrow_down_of_neg_errorConst_odd`
- Checked `OpenMath/Pade.lean` for the missing Padé-side input and found only
  Padé approximation-order identities, not a theorem turning those identities into
  a concrete `IsDownArrowDir (padeR n d) θ`.
- Refreshed the new cycle-295 Aristotle batch once after the required wait:
  - project `5d037a95...` returned a fake replacement `OpenMath/PadeOrderStars.lean`
    that adds fields like `downDirs`/`isDownArrowDir` directly to
    `OrderArrowTerminationData`; rejected.
  - project `f7242662...` returned another replacement `OpenMath/PadeOrderStars.lean`
    rebuilding `padeR`, `IsDownArrowDir`, `GlobalDownArrowBranch`, and
    `RealizedDownArrowInfinityBranch`; rejected.

## Possible solutions
- Prove a real Padé-local asymptotic theorem for

```lean
φ(z) = padeR n d z * exp (-z)
```

near `0`, with an explicit leading error term and sign, then feed that theorem
into the existing generic `arrow_down_of_*` results in `OpenMath/OrderStars.lean`.
- If the planner wants to stay theorem-local, make the next target explicitly
  assume a Padé-side direction witness

```lean
∃ θ, IsDownArrowDir (padeR n d) θ
```

and only then continue to tracking and escape.
- Do not widen `OrderArrowTerminationData` to store directions. The completed
  cycle-295 Aristotle result `5d037a95...` shows that this is exactly the bad
  replacement-interface failure mode.
