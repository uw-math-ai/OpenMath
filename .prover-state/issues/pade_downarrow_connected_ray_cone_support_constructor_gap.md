# Issue: Padé down-arrow connected-component bridge from arc-phase data remains unproved

## Blocker
The old support-constructor blocker is solved in live code:

- `nonempty_connectedRayConeSupport_of_meetsRayConeNearOriginInConnectedComponent`
- `PadeRDownArrowOrderWebConnectedComponentMeetInput`
- `PadeRDownArrowOrderWebConnectedComponentMeetInput.toConnectedRayConeSupportInput`

The live blocker is now one level lower and is encoded directly in
`OpenMath/PadeOrderStars.lean` as

```lean
PadeROrderWebMeetsRayConeNearOriginInConnectedComponent_of_arcPhaseBridge
```

This theorem must upgrade an existing local arc-phase bridge

```lean
PadeROrderWebArcPhaseBridgeNearOrigin n d θ
```

to the fixed-component compatibility statement

```lean
PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d θ.
```

Equivalently: choose one basepoint `z0 ∈ orderWeb (padeR n d)` and show that
for every sufficiently small cone around the same ray, the cone contains an
order-web witness lying in `connectedComponentIn (orderWeb (padeR n d)) z0`.

## Context
Relevant live declarations in `OpenMath/PadeOrderStars.lean`:

- `PadeROrderWebArcPhaseBridgeNearOrigin`
- `PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge`
- `PadeROrderWebMeetsRayConeNearOriginInConnectedComponent`
- `PadeROrderWebMeetsRayConeNearOriginInConnectedComponent_of_arcPhaseBridge`
- `nonempty_connectedRayConeSupport_of_meetsRayConeNearOriginInConnectedComponent`
- `padeR_even_downArrowArcPhaseBridge_of_pos_errorConst`
- `padeR_odd_downArrowArcPhaseBridge_of_neg_errorConst`
- `padeR_even_downArrowOrderWebSameComponentContinuation_of_pos_errorConst`
- `padeR_odd_downArrowOrderWebSameComponentContinuation_of_neg_errorConst`
- `padeR_even_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_pos_errorConst`
- `padeR_odd_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_neg_errorConst`
- `padeRDownArrowOrderWebConnectedComponentMeetInput_of_pos_errorConst`
- `padeRDownArrowOrderWebConnectedComponentMeetInput_of_neg_errorConst`

The concrete even and odd connected-component theorems are now only wrappers.
Both reduce immediately to the single generic arc-phase bridge theorem above.

## What was tried
- Cycles 325-327 already solved the local arc-phase bridge, raw cone meeting,
  and support-constructor layers.
- Cycle 328 first audited the five ready Aristotle result directories from the
  previous cycle; they contained only already-landed constructor variants or the
  known diagnosis that raw cone meeting is too weak.
- Cycle 328 added sorry-first same-component continuation scaffolding for the
  concrete even and odd rays and verified the file compiled.
- A new 5-job Aristotle batch was submitted for the same-component gap:
  - `42d317c0-1da1-44b9-924a-20c224187886`
  - `e9192f8a-45fe-465a-873b-11f5cf0003b8`
  - `e711d5f7-ae22-4994-8953-1c999de12768`
  - `0a294221-55c0-4239-8493-8ff15ab3c7a2`
  - `d7eb3d3f-316f-4205-b460-9bef43b7ad6a`
- After the mandated 30-minute wait, one job completed:
  `e711d5f7-ae22-4994-8953-1c999de12768`.
  Its useful contribution was not a proof, but the refactor identifying one
  generic bridging theorem from arc-phase data to connected-component meeting.
- That refactor was incorporated into live code, reducing the blocked surface
  from two concrete `sorry`s to one generic `sorry`.
- The other four Aristotle jobs were still `IN_PROGRESS` after the single
  post-wait check, so they were not polled repeatedly.
- Cycle 329 first triaged the now-ready Aristotle result
  `e711d5f7-ae22-4994-8953-1c999de12768` and confirmed that it only contained
  the already-landed refactor
  `2 concrete sorrys -> 1 generic sorry`; no proof was transplanted.
- Cycle 329 then moved the blocker one level lower in live code:
  - proved the reference-witness extraction helper
    `padeR_exists_referenceOrderWebWitness_of_arcPhaseBridge`
  - introduced the narrower private helper
    `padeR_referenceWitness_sameComponentContinuation_of_arcPhaseBridge`
  - rewrote
    `PadeROrderWebMeetsRayConeNearOriginInConnectedComponent_of_arcPhaseBridge`
    as a short wrapper around that helper
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  succeeds after this refactor; the only remaining warning is the intentional
  `sorry` in the new helper.
- A fresh 5-job Aristotle batch was submitted for the helper/generic-theorem
  layer:
  - `97a6af7e-45aa-47bf-bef1-265fb55c875f`
  - `abdf875d-df5c-42c1-a284-49bc1359174c`
  - `3571269b-efde-4a8e-8a47-185e36d3b0a7`
  - `7efec658-a889-4088-8a4f-7feed697d422`
  - `9734460d-7f32-4daf-9029-d2380415ac4e`
- After the mandated single 30-minute wait and single refresh, all five new
  jobs were still `IN_PROGRESS`:
  - `97a6af7e...` at 26%
  - `abdf875d...` at 23%
  - `3571269b...` at 37%
  - `7efec658...` at 34%
  - `9734460d...` at 34%

## What was learned
- The remaining obstruction is not parity-specific anymore.
  The real gap is angle-uniform:

```lean
PadeROrderWebArcPhaseBridgeNearOrigin n d θ
→ PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d θ.
```

- The current bridge theorem only gives `∀ cone, ∃ witness` via IVT on a short
  exact-angle arc. It does not relate witnesses obtained at different radii.
- Therefore the issue is still a genuine quantifier mismatch:
  - raw bridge / cone meeting: `∀ aperture radius, ∃ z`
  - desired connected-component seam: `∃ z0, ∀ aperture radius, ∃ z ∈ CC(z0)`
- The exact missing mathematics is now isolated cleanly:
  prove that the order-web zeros produced by the IVT live on one continuing
  local branch inside the positive-real near-origin sector.
- The blocker is now more precise than the old generic theorem statement:
  the missing content is specifically the new private helper

```lean
padeR_referenceWitness_sameComponentContinuation_of_arcPhaseBridge
```

  which fixes a bridge-produced basepoint in `rayConeNearOrigin θ 1 1` and asks
  only for same-component continuation from that basepoint to witnesses in
  smaller cones.
- Generic `connectedComponentIn` lemmas from Mathlib do not close the gap on
  their own. They would need a genuinely preconnected subset of
  `orderWeb (padeR n d)` containing both witnesses, and the current bridge data
  still does not provide that subset.

## Possible solutions
- Work directly on

```lean
padeR_referenceWitness_sameComponentContinuation_of_arcPhaseBridge
```

  and keep the public theorem as the wrapper now present in live code.
- Start from the fixed unit-cone basepoint already isolated by the helper shape,
  not from the concrete even/odd wrappers.
- A plausible route is to define a small sector where
  `Complex.re (padeR n d z * exp (-z)) > 0`, show this sector is open and
  path-connected, and then prove the order-web inside that sector is connected
  (or at least lies in one connected component) near the target ray.
- Another route is a local continuation theorem:
  show that the IVT witness on each small exact-angle arc can be chosen
  continuously in the radius parameter, giving a path in `orderWeb`.
- Do not go back to the old support-constructor seam; that part is already
  resolved and no longer the blocker.
