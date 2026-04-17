# Cycle 089 Results

## Worked on
- `OpenMath/MultistepMethods.lean`
- Closed `hQ₁pp` inside `hasDerivAt_Gtilde_one`
- Investigated `reversed_poly_C3_condition`
- Re-checked the remaining `continuousOn_Gtilde_closedBall` sorry

## Approach
- Checked recent Aristotle jobs first. One prior job on `continuousOn_Gtilde_closedBall` was `COMPLETE`; several algebraic jobs were still `IN_PROGRESS`, so I did not wait on them.
- Recomputed the C₃ reversed-polynomial algebra against the project’s `orderCondVal` definition and tested it against `bdf3`.
- Found that the old target `3σ̃''(1) + ρ̃'''(1) + 3ρ̃''(1) = 0` is false for `bdf3`; the usable identity for the cancelled-derivative computation is
  `6σ̃''(1) + 2ρ̃'''(1) + 3ρ̃''(1) - ρ̃'(1) = 0`.
- Updated the local C₃ statement to that corrected formula and used it in the `hQ₁pp` calculation.
- Proved `hQ₁pp` by expanding `Q₁''(1)`, deriving `ρ̃'''(1) = 3 R''(1)` and `ρ̃''(1) = 2 R'(1)`, then reducing to the corrected C₃ identity and `rhoCRev_poly_derivative_eval_one`.

## Result
- SUCCESS: `hQ₁pp` is closed.
- PARTIAL: `reversed_poly_C3_condition` now has the corrected statement, but its proof is still `sorry`.
- UNCHANGED: `continuousOn_Gtilde_closedBall` remains `sorry`.
- `lake env lean OpenMath/MultistepMethods.lean` succeeds.

## Dead ends
- Trying to force the old C₃ template from cycle 88/89 failed; it leaves an extra first-moment term and is not true for `bdf3`.
- A full generalized proof of the corrected C₃ identity got stuck in low-level normalization of reindexed finite sums (`Fin.rev`, `x-2` vs `x-1-1`, and distribution under sums).

## Discovery
- The statement of `reversed_poly_C3_condition` needed correction, not just a stronger proof script.
- After that correction, `hQ₁pp` becomes structurally clean and matches the intended `-m.rhoCDeriv 1 / 3`.
- Remaining sorry count in `OpenMath/MultistepMethods.lean` is now 2.

## Suggested next approach
- Prove the corrected C₃ identity by introducing explicit abbreviations for the reindexed moment sums before applying `linear_combination`, instead of rewriting large sum expressions in place.
- Then return to `continuousOn_Gtilde_closedBall`, likely by adding the boundary-root hypothesis already identified in prior cycles and in the completed Aristotle attempt.
