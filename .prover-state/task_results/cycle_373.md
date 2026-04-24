# Cycle 373 Results

## Worked on
Split `OpenMath/PadeOrderStars.lean`, which was over the 6000-line hard cap.

## Approach
Confirmed the baseline target built, inspected the file outline, and extracted the Padé order-star material into layered modules:

- `OpenMath/PadeOrderStars/Core.lean`: upstream local branch/order-web infrastructure.
- `OpenMath/PadeOrderStars/OddDownArrowSlice.lean`: odd down-arrow fixed-radius/radius-phase chain plus the down-arrow dispatcher.
- `OpenMath/PadeOrderStars/UpArrowSlice.lean`: up-arrow mirrors and zero-cosine/sign bridge block.

`OpenMath/PadeOrderStars.lean` now imports the split chain and keeps only the downstream no-escape/Ehle wrapper layer. `OpenMath.lean` now imports `OpenMath.PadeOrderStars` so the split modules are built by `lake build`.

## Result
SUCCESS.

Line counts:

- Before: `OpenMath/PadeOrderStars.lean` had 7310 lines.
- After: `OpenMath/PadeOrderStars.lean` has 398 lines.
- New modules: `Core.lean` 2032 lines, `OddDownArrowSlice.lean` 2825 lines, `UpArrowSlice.lean` 2064 lines.

Verification:

- `lake env lean OpenMath/PadeOrderStars/Core.lean`
- `lake env lean OpenMath/PadeOrderStars/OddDownArrowSlice.lean`
- `lake env lean OpenMath/PadeOrderStars/UpArrowSlice.lean`
- `lake env lean OpenMath/PadeOrderStars.lean`
- `lake build`

All completed successfully. No `sorry`/`admit` was introduced.

## Dead ends
The first direct `lake env lean OpenMath/PadeOrderStars.lean` failed before the split because dependency `.olean` files were missing from the local build cache. Running the target build generated the needed dependencies and confirmed the baseline module was clean.

## Discovery
The odd down-arrow chain and up-arrow mirrors share several helpers that were `private` in the monolithic file. To keep the split acyclic and avoid duplicating proofs, only the helpers actually needed across module boundaries were lifted from `private`, including:

- Padé sign helpers: `padePhiErrorConst_pos_of_even`, `padePhiErrorConst_neg_of_odd`.
- Order-web/ray helpers: `mem_orderWeb_of_im_zero_of_re_pos`, `padeR_exp_neg_continuousOn_angleArc`, `exact_ray_mem_rayConeNearOrigin`, `exact_angle_arc_mem_rayConeNearOrigin`, `padeR_mem_orderWeb_zero`, `padeR_mem_orderWeb_on_posRealAxis_of_small_radius`.
- Shared radius-phase and second-order helpers used by the up-arrow mirror: `oddDownArrowRadiusPhase*`, `padeRExpNegSecondCoeff`, `padeR_exp_neg_second_order_local_bound`, `error_lipschitz_on_ball_of_padeQ_ne_zero`, and the fixed-radius clopen support helper.

Aristotle was intentionally not used for this cycle: the strategy marked this as a pure code-motion split with no new proof gaps. I checked for queued/in-progress Aristotle projects and found none; the ready CollocationAlgStability bundles were stale and intentionally left untouched per the cycle strategy.

## Suggested next approach
With `PadeOrderStars.lean` under the cap and all split modules below 6000 lines, the planner can resume theorem selection from the current `plan.md` target. Keep future Padé order-star additions in the relevant submodule rather than the wrapper file.
