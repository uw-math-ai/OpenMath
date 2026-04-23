# Cycle 370 Results

## Worked on
- CI fix for GitHub Actions run `24845526044`
- `OpenMath/CollocationAlgStability.lean`
- Aristotle batch for the remaining Theorem 358A frontier

## Approach
- Pulled the failing GitHub Actions job logs. The failure was not a Lean type
  error; `lake build` was dying during clean-run dependency fetches with
  external `git` exit `128`.
- Reproduced the clean-fetch failure locally from a fresh clone. The first
  attempt flaked during package clone; the retry succeeded and a full
  `lake build` completed.
- Hardened `.github/workflows/lean_ci.yml` by forcing HTTP/1.1 and retrying
  `lake build` up to 3 times with `.lake/packages` cleanup between attempts.
- Incorporated the previously ignored sign-convention bug in
  `algStabilityBoundaryPoly`:
  Mathlib's `Polynomial.shiftedLegendre` differs from the textbook `P_n^*` by
  `(-1)^n`, so I introduced `shiftedLegendreStarPoly` and rewrote the boundary
  polynomial in the textbook-sign basis.
- Proved the forward-side Theorem 358A infrastructure manually:
  - `shiftedLegendreStarPoly` eval/degree/leading-coefficient lemmas
  - interval orthogonality and square-integral positivity
  - scalar uniqueness for degree-`n` orthogonal polynomials
  - `orthogonal_degree_eq_boundaryPoly`
  - `boundary_theta_nonneg_of_algStable`
- Left only `thm_358A_if` as the remaining `sorry`, and wrote a blocker issue
  with the concrete missing bridge.

## Result
- SUCCESS on the CI fix.
- PARTIAL SUCCESS on Theorem 358A:
  the `only if` direction is now repaired under the corrected sign convention,
  and the file is reduced to one remaining `sorry` (`thm_358A_if`).
- `lake env lean OpenMath/CollocationAlgStability.lean` succeeds.
- `lake build` succeeds locally after the CI workflow hardening.

## Dead ends
- The current `stabilityMatrix_quadForm_eq_neg_integral` machinery cannot be
  reused directly for `thm_358A_if`, because it already assumes
  `hAlg : t.IsAlgStable`.
- The remaining reverse implication appears to need a fresh bridge from the
  boundary-node hypothesis to weight nonnegativity and PSD of the algebraic
  stability matrix.

## Discovery
- The previous frontier was blocked in part by a genuine modeling bug:
  `algStabilityBoundaryPoly` had the wrong sign convention relative to the
  stated textbook polynomial `P_s^* - θ P_{s-1}^*`.
- A prior Aristotle artifact
  (`995901fc-98bc-4885-a95e-c5dc63a0cabb`) contains a plausible route for the
  reverse implication using Lagrange basis polynomials and quadrature exactness.
  That route was not integrated this cycle because it is a larger proof stack,
  not a small local repair.
- Aristotle batch submitted this cycle:
  - `ccf88ddf-93b1-450b-8d70-74b2aaa14864`
  - `a6da066b-10b2-4ce5-bf05-ac61da149bc6`
  - `5f2ebb0e-4c72-42d9-b32c-281d1b68b517`
  - `292dfe56-3f87-4c53-b3ff-081074a9414f`
  - `18acc2c0-52dc-4b7b-aef0-ccc1116f2de5`
  After the mandated 30-minute wait and single refresh, all 5 were still
  `IN_PROGRESS`, so there was nothing usable to incorporate in-cycle.

## Suggested next approach
- Continue from the blocker issue by porting the Lagrange-basis route from the
  older Aristotle sketch into the live file, adapted to the corrected
  `shiftedLegendreStarPoly` convention.
- Once `thm_358A_if` is closed, rerun `lake env lean OpenMath/CollocationAlgStability.lean`
  and `lake build`, then remove the remaining `sorry`.
