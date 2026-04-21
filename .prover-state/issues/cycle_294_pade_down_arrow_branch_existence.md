# Issue: Padé down-arrow infinity branch existence still lacks a concrete order-web support

## Blocker
The remaining down-arrow target

```lean
theorem padeR_nonempty_realizedDownArrowInfinityBranch_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    Nonempty (RealizedDownArrowInfinityBranch (padeR n d))
```

still has no honest bridge from its hypotheses to the geometric object it asks for.

The first unsupported field of
`RealizedDownArrowInfinityBranch (padeR n d)` is currently the concrete support set
inside `orderWeb (padeR n d)`. Without that support there is no way to even form the
base `GlobalOrderArrowBranch`, so the downstream fields also remain unavailable:

- `support : Set ℂ`
- `support_connected : IsConnected support`
- `support_subset_orderWeb : support ⊆ orderWeb (padeR n d)`
- `origin_mem_closure : (0 : ℂ) ∈ closure support`

After that, the following fields are still separately unsupported in the live repo:

- `tangentAngle : ℝ`
- `tangentDown : IsDownArrowDir (padeR n d) tangentAngle`
- `BranchTracksRayNearOrigin ...`
- `EscapesEveryClosedBall ...`

## Context
- `GlobalOrderArrowBranch`, `GlobalDownArrowBranch`, and
  `RealizedDownArrowInfinityBranch` live in `OpenMath/OrderStars.lean`.
- `OpenMath/PadeOrderStars.lean` now reduces the finite-family target to
  zero-count-or-branch-nonemptiness:

```lean
nonempty_padeR_realizedDownArrowInfinityWitnessFamily_iff
```

- `OrderArrowTerminationData` carries only abstract endpoint counts and one
  arithmetic inequality. Its field

```lean
0 < data.downArrowsAtInfinity
```

does not mention `padeR n d`, `orderWeb (padeR n d)`, a support set, a tangent
direction, or any global branch topology.
- Repo-wide search found no theorem constructing any of:
  - `GlobalDownArrowBranch (padeR n d)`
  - `RealizedDownArrowInfinityBranch (padeR n d)`
  - `IsDownArrowDir (padeR n d) θ`

## What was tried
- Re-read the cycle-293 blocker issue and the branch interfaces in
  `OpenMath/OrderStars.lean`.
- Searched the live repo for any existing concrete Padé branch construction or
  Padé-specific down-arrow direction theorem; none were found.
- Created the cycle-294 scratch batch:
  - `01_padeR_exists_globalDownArrowBranch.lean`
  - `02_padeR_down_branch_tracksRayNearOrigin.lean`
  - `03_padeR_down_branch_escapesEveryClosedBall.lean`
  - `04_padeR_nonempty_realizedDownArrowInfinityBranch.lean`
  - `05_padeR_down_branch_exact_blocker.lean`
- Isolated the deeper support-level target in scratch:

```lean
theorem padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    ∃ support : Set ℂ,
      IsConnected support ∧
        support ⊆ orderWeb (padeR n d) ∧
        (0 : ℂ) ∈ closure support
```

- Ran a quick numerical sanity check on small Padé pairs. The obvious positive-real
  candidate is not uniformly usable: for examples such as `(0,1)` and `(1,1)`,
  `padeR n d x * exp (-x)` blows up at a positive-real pole and changes sign
  afterwards, so the escaping support cannot just be asserted as all of `ℝ_{>0}`.

## Possible solutions
- Prove a genuinely Padé-local geometric theorem producing a connected subset of
  `orderWeb (padeR n d)` whose closure meets the origin.
- If the positive-real axis is still part of the intended construction, prove a
  theorem that identifies the correct connected component of
  `{x : ℝ | padeR n d x * exp (-x) > 0}` and shows it either escapes to `+∞` or
  explain why another ray/component must be used.
- Alternatively, first prove a Padé-specific tangent-direction theorem
  `IsDownArrowDir (padeR n d) θ`, then construct a global support that continues
  that local germ and only afterwards add the escape-to-infinity field.
