# Cycle 279 Results

## Worked on
- `OpenMath/OrderStars.lean`
- `.prover-state/aristotle/cycle_279/01_local_plus_near_even_angle_of_neg_errorConst.lean`
- `.prover-state/aristotle/cycle_279/02_local_minus_near_odd_angle_of_neg_errorConst.lean`
- `.prover-state/aristotle/cycle_279/03_local_plus_near_odd_angle_of_pos_errorConst.lean`
- `.prover-state/aristotle/cycle_279/04_realizedDownArrowInfinityBranch_contradiction_even.lean`
- `.prover-state/aristotle/cycle_279/05_realizedUpArrowInfinityBranch_contradiction_even.lean`
- `.prover-state/issues/order_star_remaining_concrete_hypotheses_after_even_cone_control.md`

## Approach
- Followed the cycle-279 strategy in order.
- Re-triaged the three ready cycle-278 Aristotle bundles first:
  - `3187363b-ba74-497e-a8c9-966db1aa874f`
  - `6e6eb7ac-2bc5-4667-9411-f1ca5f8e2f8b`
  - `85dab4bf-8050-4378-9cac-b875e9ef491c`
- Rejected all three quickly because each shipped a parallel `OpenMath/OrderStars.lean`, violating the planner's immediate reject criterion.
- Worked only in the live `OpenMath/OrderStars.lean` seam after that.
- Targeted the theorem-local concrete hypotheses instead of the final contradiction.
- Added a new live cone-control lemma by thickening the existing exact-ray 355B asymptotics to a genuine `rayConeNearOrigin` neighborhood.
- Wrote a fresh cycle-279 Aristotle batch with five focused scratch files.
- Waited once for 30 minutes, then refreshed each project once.

## Result
SUCCESS

The live file remains sorry-free and now proves one new concrete local hypothesis:

- `local_minus_near_even_angle_of_pos_errorConst`

This is a real theorem-local analytic input for the cycle-278 contradiction shape:
it derives strict `< 1` control on a whole cone near an even 355B down-arrow ray,
not just on the exact ray.

`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean`
completed successfully after the edit.

## Dead ends
- The three cycle-278 Aristotle bundles were rejected again for the same reason as
  in cycle 278: each rebuilt a parallel `OpenMath/OrderStars.lean` or changed the
  live seam instead of proving facts about it.
- After the cycle-279 30-minute Aristotle wait, the two completed contradiction jobs
  were also rejected:
  - `ab436bfb-e548-4e3b-978b-9b6b65c3cdf1`
  - `0a239bce-1458-4111-9659-63249a161ec9`
  because both results again shipped a parallel `OpenMath/OrderStars.lean` and
  fabricated witness-style branch fields that do not exist in the live file.
- The three cycle-279 local-cone jobs were still `IN_PROGRESS` at the single
  post-wait refresh and were not polled again this cycle:
  - `2ca3d296-5953-4725-a0bf-1f565c9af2ff`
  - `3ec9c1fe-7549-430e-8c64-49ffb0ae1f9a`
  - `7362206e-685f-431c-89ea-27cc3327acbd`

## Discovery
- Of the four missing concrete contradiction inputs from cycle 278, one piece now
  has live progress:
  - local cone sign control: partially proved, specifically the even-angle / `C > 0`
    down-arrow case via `local_minus_near_even_angle_of_pos_errorConst`
- The following still lack live justification:
  - exclusion of `0` from realized branch support
  - exclusion of nonzero unit-level points on `orderWeb R`
  - far-field sign control on large `orderWeb R` points
  - the remaining local cone-control parity/sign cases
  - a bridge from generic `IsDownArrowDir` / `IsUpArrowDir` tangents to the 355B
    even/odd angle families

## Suggested next approach
- Prove the three companion cone-control lemmas:
  - even-angle / `C < 0` gives local `> 1`
  - odd-angle / `C < 0` gives local `< 1`
  - odd-angle / `C > 0` gives local `> 1`
- Then prove the generic tangent-classification bridge needed to use those lemmas
  for a live `RealizedDownArrowInfinityBranch` or `RealizedUpArrowInfinityBranch`.
- Keep rejecting Aristotle artifacts that rebuild `OpenMath/OrderStars.lean` or
  add surrogate witness fields.
