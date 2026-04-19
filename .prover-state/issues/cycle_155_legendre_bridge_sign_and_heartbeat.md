# Issue: Legendre bridge has sign mismatch and recurrence proof hits heartbeat budget

## Blocker
Closing `ButcherTableau.gaussLegendre_B_double` still depends on a usable bridge from the recursive
`shiftedLegendreP` definition in `OpenMath/Legendre.lean` to Mathlib's
`Polynomial.shiftedLegendre`. Aristotle produced a correct conceptual bridge, but it is not the
statement the planner originally suggested:

`shiftedLegendreP n x = (-1)^n * eval x (map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n))`

The extra `(-1)^n` factor matters. Without carrying that sign carefully, the coefficient expansion
and leading-coefficient argument for `gaussLegendre_B_double` are wrong.

The extracted recurrence proof for the bridge also stalls under the local heartbeat budget when
ported into this workspace, so it is not yet cheap enough to inline into the theorem body.

## Context
- Remaining sorrys are unchanged:
  - `OpenMath/Legendre.lean:199` `gaussLegendre_B_double`
  - `OpenMath/Legendre.lean:227` `gaussLegendreNodes_of_B_double`
- Aristotle job `1d9822aa-9d1d-4d23-abf6-501995a5f6a8` completed with a verified bridge project and
  explicitly reported the sign correction above.
- Aristotle job `25f0bc02-fd9c-4e56-a5fe-dcb75e9a92c0` completed, but the generated proof relies on
  a new helper file and still contains an unfinished `exact?` in the orthogonality block.
- Aristotle job `88562ee9-0604-4af8-af76-4cd109783926` completed, but its approach raises
  `maxHeartbeats` to `400000`, which violates the project constraint.
- Aristotle jobs `9d969800-dcdf-43bf-9b3a-0b2d6cf1f8f6` and `c9418788-b71f-4072-bab7-238eaf5b1ea8`
  remain `IN_PROGRESS`.
- Aristotle jobs `d206f904-7ca0-487b-a04d-810746020839` and
  `de165c89-6ceb-4a51-a674-ee4da6c4264b` finished `COMPLETE_WITH_ERRORS`.

## What was tried
- Checked all seven planner-listed Aristotle jobs first, per cycle instructions.
- Extracted and inspected the completed artifacts.
- Tested the bridge proof from Aristotle in an isolated Lean snippet against the current workspace.
- Confirmed that:
  - the naïve bridge statement without `(-1)^n` is false;
  - the sign-correct bridge is plausible;
  - the coefficient-comparison recurrence proof is too heavy as-is in this environment.

## Possible solutions
- Rework the bridge proof around Mathlib's existing theorem
  `Polynomial.neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq` instead of rebuilding the full
  coefficient recurrence from scratch.
- Prove a lighter local lemma giving only the coefficient formula needed for `gaussLegendre_B_double`
  after transporting through the sign-correct bridge, rather than a full standalone bridge theorem.
- If the bridge remains too expensive, switch to a direct polynomial recurrence inside
  `gaussLegendre_B_double` for the coefficient representation, and use Mathlib only for the
  nonvanishing top coefficient via `Polynomial.coeff_shiftedLegendre`.
