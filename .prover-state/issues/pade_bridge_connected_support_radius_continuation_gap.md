# Issue: `connectedSupport_of_bridgeWitnesses` still lacks a radius-continuation theorem

## Blocker
The single live sorry in `OpenMath/PadeOrderStars.lean` is now the local helper

```lean
connectedSupport_of_bridgeWitnesses
```

at [OpenMath/PadeOrderStars.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/PadeOrderStars.lean:1761).

Its hypotheses are already narrower than the previous cycle:

- `hz0web : z0 ∈ orderWeb (padeR n d)`
- `hz0cone : z0 ∈ rayConeNearOrigin θ 1 1`
- `hzweb : z ∈ orderWeb (padeR n d)`
- `hzcone : z ∈ rayConeNearOrigin θ aperture radius`

and its conclusion asks only for

```lean
∃ support : Set ℂ,
  IsConnected support ∧
  support ⊆ orderWeb (padeR n d) ∧
  z0 ∈ support ∧
  z ∈ support
```

So the blocker is no longer witness existence. The blocker is specifically the
missing continuation statement that would turn two already-chosen bridge
witnesses in the same near-origin sector into one connected subset of the order
web.

## Context
Cycle 331 kept the wrapper structure intact and changed only the local theorem
shape:

- `bridgeWitnesses_have_connectedSupport` now chooses `z` using
  `padeR_exists_referenceOrderWebWitness_of_arcPhaseBridge`
- the only remaining `sorry` is the support-only helper above

This compiles with exactly one `sorry`, and both requested checks succeed:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`

The bridge data available in the outer theorem still has the same shape:

- for each small cone, choose one exact-angle arc at one small radius
- along that arc,
  `0 < Complex.re (padeR n d w * Complex.exp (-w))`
- the imaginary part has opposite signs at the two endpoints
- IVT then gives one order-web witness on that single arc

## What was tried
- Triaged the five ready Aristotle bundles required by the planner:
  - `7efec658-a889-4088-8a4f-7feed697d422`
  - `e9192f8a-45fe-465a-873b-11f5cf0003b8`
  - `97a6af7e-45aa-47bf-bef1-265fb55c875f`
  - `9734460d-7f32-4daf-9029-d2380415ac4e`
  - `d7eb3d3f-316f-4205-b460-9bef43b7ad6a`
- Rejected all five for live use:
  - they either introduced new `sorry`s,
  - or switched to non-live-safe multi-file stub rebuilds,
  - or changed the proof target to a different zero-based local-connectedness
    route instead of closing the actual live helper.
- Performed the one allowed decomposition beneath
  `bridgeWitnesses_have_connectedSupport` so that the live `sorry` now asks
  only for support construction from an already chosen `z`.
- Submitted a fresh 5-job Aristotle batch against the narrowed helper:
  - `8ff4654f-e37e-407d-863d-63ad39813fea`
  - `3219b43a-56f8-4859-aaf6-8108033787f1`
  - `7cbf54cc-e2e8-4c1f-b871-d9e741158632`
  - `c8fe0799-0de6-400e-a552-38392edbc8c0`
  - `5668761d-825b-499d-81fd-e350bee2386a`
- Single refresh status after submission:
  all five were still `QUEUED`, so there was nothing to transplant.

## Why the connected subset construction failed
- The current hypotheses provide two order-web points `z0` and `z`, but no
  relation between how those points were chosen across radius.
- The available bridge theorem is only pointwise in radius:
  it proves `∀ aperture radius, ∃ witness`, not a coherent family of witnesses.
- Because of that, the obvious Mathlib route

```lean
IsPreconnected.subset_connectedComponentIn
```

still cannot start: there is no explicit preconnected subset of
`orderWeb (padeR n d)` known to contain both `z0` and `z`.
- The exact missing statement is one of the following:
  - a continuous choice of zero of
    `Complex.im (padeR n d (t * exp ((θ + s) * I)) * exp (-(t * exp ((θ + s) * I))))`
    as the radius parameter `t` varies through a small interval, or
  - a topological theorem that the union of the sign-changing exact-angle arcs
    already contains a connected subset of the zero set joining the witness at
    the larger radius to the witness at the smaller radius.
- Without one of those two ingredients, the attempted support definitions all
  collapse to disconnected data:
  - one singleton witness on one radius,
  - another singleton witness on another radius,
  - and no proved continuation object between them.

## Possible solutions
- Prove a still-local radius-continuation lemma immediately underneath
  `connectedSupport_of_bridgeWitnesses`.
  The lemma should conclude an explicit `support : Set ℂ` inside
  `orderWeb (padeR n d)` containing `z0` and `z`.
- A viable proof will likely need one new analytic ingredient beyond the
  current bridge:
  either uniqueness / continuity of the zero on each exact-angle arc, or a
  planar connected-zero-set theorem for the positive-real sector.
- Do not go back upward to more wrappers over `connectedComponentIn`.
  The wrapper layer is already reduced as far as it can go; the missing
  mathematics is exactly the local support construction.
