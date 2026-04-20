# Issue: shifted-Legendre sum recurrence still exceeds the cycle heartbeat budget

## Blocker
The natural next step toward closing `OpenMath/Legendre.lean` is the explicit
sum formula
`shiftedLegendreP s x = ∑ l, shiftedLegCoeff s l * x^l`,
which in turn needs a coefficient-level recurrence proof.

The existing recurrence proof harvested from older artifacts compiles only with
heavy simplification. In the current repository it times out under the project
budget of `maxHeartbeats ≤ 200000`, so it cannot be merged as-is.

## Context
- Reusable helper file added:
  [OpenMath/LegendreHelpers.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/LegendreHelpers.lean)
- Remaining target file:
  [OpenMath/Legendre.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/Legendre.lean:224)
- The new helper file already proves:
  - `shiftedLegCoeff_diag_ne_zero`
  - `orthogonality_sum_zero`
- The missing piece is the theorem sketched in Aristotle scratch file:
  [.prover-state/aristotle/cycle_179/03_shifted_legendre_sum_recurrence.lean](/mmfs1/gscratch/amath/mathai/OpenMath/.prover-state/aristotle/cycle_179/03_shifted_legendre_sum_recurrence.lean)

## What was tried
- Ported the older coefficient helper infrastructure into a standalone module.
- Kept only the sorry-free parts that compile comfortably in the current tree.
- Tried to port the older recurrence proof with the project heartbeat cap.
- The recurrence port timed out during `simp`/normalization and could not be
  justified without violating the project rule against larger heartbeat caps.
- Submitted a fresh cycle-179 Aristotle batch targeting:
  - bridge theorem
  - explicit sum formula
  - coefficient recurrence
  - `gaussLegendre_B_double`
  - converse theorem

## Possible solutions
- Decompose the recurrence proof into smaller coefficient lemmas so each case
  avoids the large `simp_all +decide` blocks.
- Prove the bridge to Mathlib’s `Polynomial.shiftedLegendre` directly and bypass
  the explicit-sum route for `gaussLegendre_B_double`.
- If Aristotle returns a smaller recurrence proof, use that to finish
  `shiftedLegendreP_eq_sum`, then re-run the finite-sum Gaussian exactness proof.
