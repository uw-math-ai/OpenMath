# Cycle 401 Results

## Worked on
Smooth-`y` Taylor bridge in `OpenMath/LMMTruncationOp.lean`:
`taylorPolyOf`, `truncationOp_smooth_eq_taylor_residual`,
`taylor_remainder_value_bound`, `taylor_remainder_deriv_bound`, and
`truncationOp_smooth_eq_leading_add_remainder`.

## Approach
Triage first: listed recent Aristotle projects and refreshed the five cycle-400
IDs (`d5418d04`, `ba8f3583`, `16f00570`, `7d3c9d2a`, `22966343`). They target
cycle-400 Taylor-polynomial scaffolds already closed in the live file, so none
were incorporated.

Added the cycle-401 sorry-first scaffold and verified it compiled. Submitted
the required Aristotle batch:

- Job A `8c810d41`: residual identity
- Job B `2ed885eb`: value residual bound
- Job C `7dd5c106`: derivative residual bound
- Job D `3a8ca14c`: headline finite-bound theorem
- Job E `f4fbc02a`: backup `taylorWithinEval` formulation

While the mandated 30-minute Aristotle wait was running, closed the local
proofs manually. The residual identity is direct finite-sum algebra after
unfolding `truncationOp`. The pointwise residual lemmas use the exact
Taylor-polynomial value/derivative matches at `u = t` and otherwise choose the
pointwise ratio as the local constant. The headline theorem uses the same
fixed-`h` existential-constant argument.

## Result
SUCCESS. `OpenMath/LMMTruncationOp.lean` compiles with no `sorry`.

`lean_verify` on `LMM.truncationOp_smooth_eq_leading_add_remainder` reports
only the standard axioms: `propext`, `Classical.choice`, `Quot.sound`.

Aristotle refresh after the mandated wait:

- Job A `8c810d41`: `COMPLETE_WITH_ERRORS`
- Job B `2ed885eb`: `COMPLETE_WITH_ERRORS`
- Job C `7dd5c106`: `COMPLETE_WITH_ERRORS`
- Job D `3a8ca14c`: `IN_PROGRESS` at 29% on the single allowed refresh pass
- Job E `f4fbc02a`: `COMPLETE_WITH_ERRORS`

No Aristotle output was incorporated; the live file was already closed locally
and no refreshed job presented a clean ready-to-merge bundle.

## Dead ends
No Lean blocker. The main discovery is that the requested headline theorem
surface is weaker than the mathematical big-O statement: because `C` is chosen
after fixing `h > 0`, the final bound can be proved by dividing the actual
error by `h^(p+2)`.

## Discovery
Mathlib exposes `taylor_mean_remainder_bound`,
`exists_taylor_mean_remainder_bound`, and
`taylor_mean_remainder_lagrange_iteratedDeriv`, but these are phrased around
`taylorWithinEval`/`iteratedDerivWithin`. The current live theorem does not yet
force their use because the existential constant is theorem-local for a fixed
positive step.

## Suggested next approach
Strengthen the local-error bridge to a uniform small-step statement, e.g.
`∃ C δ, 0 ≤ C ∧ 0 < δ ∧ ∀ h, 0 < h → h ≤ δ → ... ≤ C * h^(p+2)`, or introduce
the actual local truncation error notation `τ(t,h)` and require the constant to
be independent of `h`. That surface should make the Mathlib Taylor remainder
API genuinely necessary.
