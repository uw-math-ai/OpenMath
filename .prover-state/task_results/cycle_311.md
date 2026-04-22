# Cycle 311 Results

## Worked on
- Triaged the required ready Aristotle bundles before editing:
  - `af144331-a434-42f9-b7df-76daec67f48a`
  - `2187c386-b574-467d-94ed-a0700415a9cb`
  - stale cycle-310 `PadeOrderStars` bundles
    `41beb937`, `b70c686c`, `51d7ed5f`, `ee23b4ba`, `3b230c5d`
- Tried to build the cycle-311 local cone infrastructure below
  `PadeRConcreteNoEscapeInput`.
- Added and proved two quantitative helper lemmas in
  `OpenMath/OrderStars.lean`:
  - `main_minus_bound_of_re_pos`
  - `main_plus_bound_of_re_neg`
- Wrote a focused blocker issue:
  `.prover-state/issues/pade_local_cone_feeder_false_at_zero_cos.md`

## Approach
- Followed the required order:
  1. triaged previous Aristotle outputs
  2. added sorry-first skeletons for the new cone/sign seam
  3. compiled the sorry-first state
  4. submitted a focused 5-job Aristotle batch
  5. waited once, refreshed once, and inspected only the compatible result
- For the generic cone work, reduced the local norm estimates to two reusable
  quantitative main-term lemmas about `‖1 - a u‖` when `u.re` has fixed sign.
- Tried to prove the honest cosine-sign cone lemmas by a unified
  `coeff := |C|`, `base := if 0 ≤ C then η else -η` argument.

## Result
- SUCCESS:
  - triaged the stale/stub Aristotle bundles as requested
  - landed the two quantitative helper lemmas in `OrderStars.lean`
  - wrote the blocker issue with the exact zero-cosine failure mode
  - kept `OpenMath/OrderStars.lean` and `OpenMath/PadeOrderStars.lean`
    compiling cleanly
- FAILED:
  - did not land the public generic cosine-sign cone lemmas
  - did not land the Padé arrow-direction to cone-control corollaries

## Dead ends
- `2187c386...` was rejected immediately as a live patch because it rebuilt
  parallel `OpenMath/*.lean` stub files.
- The five cycle-310 `PadeOrderStars` bundles were stale for the live seam; they
  only touched already-landed wrapper work and did not help the new cone-control
  target.
- The attempted theorem route

  ```lean
  IsDownArrowDir (padeR n d) θ -> cone with ‖·‖ < 1
  IsUpArrowDir (padeR n d) θ -> cone with 1 < ‖·‖
  ```

  is blocked by zero-cosine rays. Forward Euler / `padeR 1 0` at `θ = π/4`
  gives exact-ray `< 1` behavior while nearby angles already flip to `> 1`, so
  no symmetric cone feeder can hold there.
- The unified public cone proof in Lean also hit the 200000-heartbeat cap, so I
  removed the temporary public skeletons rather than leave new `sorry`s behind.

## Discovery
- The real blocker is not just a brittle contradiction proof: the planned
  `IsDownArrowDir/IsUpArrowDir -> sign -> cone` interface is mathematically
  wrong at zero-cosine rays.
- What *is* sound and now formalized is the quantitative main-term layer:
  once a future theorem supplies an explicit signed real-part margin, the
  `main_minus_bound_of_re_pos` / `main_plus_bound_of_re_neg` lemmas are ready to
  absorb the local error term.
- Aristotle batch submitted this cycle:
  - `a33edb0e`: `local_minus_near_angle_of_pos_mul_cos` — `IN_PROGRESS` at refresh
  - `a4fe7b7c`: `local_plus_near_angle_of_neg_mul_cos` — `IN_PROGRESS` at refresh
  - `fc12448c`: down-arrow sign extraction — `IN_PROGRESS` at refresh
  - `a466ffde`: up-arrow sign extraction — `IN_PROGRESS` at refresh
  - `b778f09e`: feeder wrappers — `COMPLETE`, but only as thin wrappers around the
    still-open sign-extraction lemmas, so not incorporable as a live patch

## Suggested next approach
- Do not retry the false symmetric-cone target from arbitrary
  `IsDownArrowDir` / `IsUpArrowDir`.
- Retarget the local feeder seam to an explicit nonzero cosine-sign hypothesis,
  or to a one-sided wedge statement that excludes zero-cosine rays.
- Reuse the landed helper lemmas in `OrderStars.lean` when formalizing that
  corrected interface.
- If the still-running Aristotle jobs finish later, inspect them only for
  reusable proof fragments for the honest cosine-sign infrastructure, not for
  the false arrow-direction wrapper route.
