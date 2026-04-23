# Cycle 364 Results

## Worked on
- `OpenMath/CollocationAlgStability.lean`
- The live `(358c)` seam behind `nodePoly_interval_zero_aux_of_algStable`
- Fresh Aristotle batch for:
  - `antiderivative_remainder_exact`
  - `nodePoly_interval_zero_aux_of_algStable`
  - `stabilityMatrix_quadForm_eq_neg_integral`
  - `boundary_theta_nonneg_of_algStable`
  - `orthogonal_degree_eq_boundaryPoly`

## Approach
- Read the cycle strategy, the cycle-363 blocker issue, and the current live
  file first.
- Added the theorem-local antiderivative scaffold immediately above
  `nodePoly_interval_zero_aux_of_algStable`:
  - `antiderivativePoly`
  - node-evaluation and endpoint lemmas
  - `modByMonic` remainder lemmas for `nodePoly t`
  - a local quadratic-form expansion
  - the new helper surface `antiderivative_remainder_exact`
- Rewrote `nodePoly_interval_zero_aux_of_algStable` from a bare `sorry` into a
  structured proof with named intermediate claims (`hr_natDegree`, `hr_eval`,
  `hquad`, `hexact`, `hquot_zero`, `hr_eq_Q`, `hquad_zero`, `hnode`).
- Submitted the fresh focused Aristotle batch after the scaffold compiled.
- Did the single refresh and then continued manually on the same blocker.

## Result
- PARTIAL SUCCESS: the theorem-local scaffold requested by the planner is now
  live in `CollocationAlgStability.lean`, and the file/build both verify.
- BLOCKED: the lower-degree zero theorem still does not close.
- Verification run:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/CollocationAlgStability.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.CollocationAlgStability`
- Aristotle status after the single refresh:
  - `c079a3e9-4c78-4766-b961-c9b74333e532` (`antiderivative_remainder_exact`): `IN_PROGRESS` at 6%
  - `fb765e3d-98de-4254-afd3-2b928f226032` (`nodePoly_interval_zero_aux_of_algStable`): `IN_PROGRESS` at 4%
  - `7b2bf1cb-5eb9-4e45-ad12-8591dd23f0f0` (`stabilityMatrix_quadForm_eq_neg_integral`): `QUEUED`
  - `409155c2-ac8b-476c-8e1c-f11f8a91cfb5` (`boundary_theta_nonneg_of_algStable`): `IN_PROGRESS` at 4%
  - `b3b1362b-0567-4a48-b42d-d65635586332` (`orthogonal_degree_eq_boundaryPoly`): `QUEUED`

## Dead ends
- The current antiderivative-of-`q` route for the lower-degree zero theorem
  collapses once `Qpoly /ₘ nodePoly t = 0` is proved: the remainder becomes
  `Qpoly`, and the scaffold only yields an identity about `q * Qpoly`.
- That collapse proves the quadratic form vanishes, but it removes the
  `nodePoly t * q` term entirely, so it does not imply
  `∫ ((nodePoly t) * q).eval = 0`.
- None of the fresh Aristotle jobs finished after the single allowed refresh, so
  there was nothing safe to incorporate this cycle.

## Discovery
- The blocker is sharper than “prove the special remainder exactness identity”.
  In the lower-degree case, even a successful proof of that exactness identity
  is insufficient if the quotient vanishes, because the argument then never
  reaches the target `nodePoly t * q` integral.
- The live structured proof now isolates the exact failed last step as `hnode`
  inside `nodePoly_interval_zero_aux_of_algStable`.
- Recorded the blocker in:
  `.prover-state/issues/cycle_364_358A_zero_helper_antiderivative_collapse.md`

## Suggested next approach
- Rework the zero-theorem route so a nontrivial `nodePoly t` quotient survives
  in the lower-degree case, or switch to the transformed-basis argument from the
  textbook instead of forcing the current antiderivative decomposition.
- If the mathematics truly requires the degree-`s - 1` sign statement first,
  explicitly allow that dependency reversal in the next cycle rather than
  continuing to push the current collapsing route.
