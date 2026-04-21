# Cycle 280 Results

## Worked on
- `OpenMath/OrderStars.lean`
- `.prover-state/issues/order_star_tangent_classification_bridge_after_cone_control.md`

## Approach
- Followed the cycle-280 strategy in order.
- Read `.prover-state/strategy.md` first, then triaged the four ready Aristotle
  result directories before editing the live file.
- Inspected the theorem-local cone bundles:
  - `7362206e-685f-431c-89ea-27cc3327acbd`
  - `2ca3d296-5953-4725-a0bf-1f565c9af2ff`
- Rejected the contradiction bundles:
  - `ab436bfb-e548-4e3b-978b-9b6b65c3cdf1`
  - `0a239bce-1458-4111-9659-63249a161ec9`
  because they shortcut through non-live contradiction assumptions instead of
  proving facts about the live branch interface.
- Ported the usable proof shape from the portable theorem-local Aristotle files
  into the live `OrderStars.lean` without importing or copying any parallel
  `OrderStars.lean`.
- Added one reusable quantitative helper for the `> 1` cone cases:
  - `norm_add_mul_gt_one_of_close_to_one`
- Proved the three remaining live cone-control lemmas:
  - `local_plus_near_even_angle_of_neg_errorConst`
  - `local_plus_near_odd_angle_of_pos_errorConst`
  - `local_minus_near_odd_angle_of_neg_errorConst`
- Recompiled the live file after the edits with:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean`

## Result
SUCCESS

Cycle 280 closes the entire concrete cone-control layer in the live file. The
following four local hypotheses are now available in `OpenMath/OrderStars.lean`:

- `local_minus_near_even_angle_of_pos_errorConst`
- `local_plus_near_even_angle_of_neg_errorConst`
- `local_plus_near_odd_angle_of_pos_errorConst`
- `local_minus_near_odd_angle_of_neg_errorConst`

The live file remains sorry-free and the compile check above succeeded.

## Dead ends
- `2ca3d296-5953-4725-a0bf-1f565c9af2ff` shipped a parallel `OrderStars.lean`,
  so only the theorem-local proof idea was reusable.
- `ab436bfb-e548-4e3b-978b-9b6b65c3cdf1` and
  `0a239bce-1458-4111-9659-63249a161ec9` were not mergeable contradiction
  results; they rely on non-live shortcut assumptions rather than the live
  branch seam.
- After the cone lemmas were finished, the next step was not the contradiction
  theorem itself but the missing generic tangent-classification bridge. The repo
  still has only forward exact-ray theorems for concrete angles, not an inverse
  theorem classifying an arbitrary `IsDownArrowDir R θ` / `IsUpArrowDir R θ`.

## Discovery
- The exact local analytic input below `ConcreteRationalApproxToExp` is now much
  narrower than in cycle 279. The cone-control work is complete.
- The next blocker is specifically the theorem-local bridge from a generic
  realized tangent direction to one of the four concrete 355B angle/sign
  families already encoded by the live exact-ray theorems.
- I wrote that blocker up in:
  - `.prover-state/issues/order_star_tangent_classification_bridge_after_cone_control.md`

## Suggested next approach
- Stay in `OpenMath/OrderStars.lean`.
- Prove the generic tangent-classification bridge in contradiction-ready form:
  - down-arrow tangent gives local `< 1` cone control
  - up-arrow tangent gives local `> 1` cone control
- Once that bridge is live, attack only the realized down-arrow contradiction
  theorem first, reusing the existing cycle-278 helper layer unchanged.
