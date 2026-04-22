# Cycle 323 Results

## Worked on
`OpenMath/PadeOrderStars.lean`

The down-arrow Padé seam below:

- `PadeROrderWebMeetsRayConeNearOrigin`
- `PadeRConnectedRayConeOrderWebSupport`
- `PadeRDownArrowOrderWebRayConeMeetInput`

## Approach
- Re-read the live seam around raw cone-meeting, connected-support packaging,
  and the concrete down-arrow direction theorem.
- Checked `OpenMath/OrderStars.lean` and `OpenMath/PadeAsymptotics.lean` to see
  what was already available beyond the cone `< 1` / `> 1` sign lemmas.
- Noticed the missing step was now phase-based: to get an `orderWeb` point, the
  Padé order-star amplitude must hit the positive real axis somewhere inside a
  small cone, and the live file had no explicit IVT bridge for that.
- Added a smaller exact-angle arc-phase bridge below raw cone-meeting:
  `PadeROrderWebArcPhaseBridgeNearOrigin`.
- Proved the formal upgrade:
  `PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge`.
- Added the lower theorem-local input wrapper
  `PadeRDownArrowOrderWebArcPhaseBridgeInput` and the converter
  `PadeRDownArrowOrderWebArcPhaseBridgeInput.toOrderWebRayConeMeetInput`.
- Created five new Aristotle scratch files against this new seam and submitted
  all five in batch.

## Result
SUCCESS

The raw cone-meeting seam is now reduced one level further.

New smallest live blocker:

```lean
PadeROrderWebArcPhaseBridgeNearOrigin n d θ
```

New landed theorem:

```lean
PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge
```

So the remaining analytic task is no longer “find an order-web point in each
small cone” directly. It is now:

1. build a short exact-angle arc inside each cone,
2. keep `Complex.re (padeR n d z * exp (-z))` positive on that arc,
3. force `Complex.im (padeR n d z * exp (-z))` to change sign across the two
   endpoints,
4. let IVT produce the `orderWeb` point formally.

Verification succeeded:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`

## Dead ends
- The current Padé cone sign-control lemmas still only prove `< 1` / `> 1`
  behavior. They do not by themselves force any point to land on the positive
  real axis.
- `padeR_exists_downArrowDir` still only gives norm information on the exact ray.
  That is insufficient for `orderWeb` without additional phase information.
- The connected-support packaging step remains untouched this cycle because raw
  cone-meeting itself was still too coarse a blocker; the honest obstruction sat
  below it.

## Discovery
- The exact missing content under the raw cone-meeting theorem is a phase-crossing
  statement, not another norm sign theorem.
- Continuity along a short exact-angle arc is easy once `padeQ_nonzero_near_zero`
  is brought into scope; the hard part is constructing the arc with positive real
  part and opposite imaginary signs.
- The new bridge theorem makes the planner-facing obstruction precise enough to
  target directly with future asymptotic work.

## Suggested next approach
- Prove explicit arc-phase bridge theorems for the concrete Padé down-arrow
  angles:
  - even-angle case when `0 < padePhiErrorConst n d`,
  - odd-angle case when `padePhiErrorConst n d < 0`.
- Reuse the full complex asymptotic bound `padeR_exp_neg_local_bound`, not just
  the derived cone norm inequalities.
- After `PadeROrderWebArcPhaseBridgeNearOrigin` is available, immediately lift it
  through `PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge`, then return to
  the connected-support packaging problem.

## Aristotle job results
- `5fd100f0-65d7-48e0-8314-caf10f09cb2b` (`ArcConeGeometry.lean`): submitted,
  single refresh status `QUEUED`.
- `47599d5f-05f3-48e2-818b-bb41dfd94daa` (`ArcPhaseEven.lean`): submitted,
  single refresh status `QUEUED`.
- `8c87cf7f-6c17-46f4-8331-185624c98584` (`ArcPhaseOdd.lean`): submitted,
  single refresh status `QUEUED`.
- `da56b462-d8b6-4238-be33-eb6e90dc1b6d` (`ArcPhaseExists.lean`): submitted,
  single refresh status `QUEUED`.
- `1514e634-1a27-422a-8cb6-21a8f88b4424` (`ArcPhaseInput.lean`): submitted,
  single refresh status `QUEUED`.

No Aristotle output was ready for incorporation during this cycle.
