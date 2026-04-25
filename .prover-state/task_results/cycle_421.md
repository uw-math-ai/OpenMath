# Cycle 421 Results

## Worked on
AB4 vector convergence chain in `OpenMath/LMMAB4Convergence.lean`, mirroring the AB3 vector chain and the cycle 420 AB4 scalar chain.

## Approach
Skimmed the two ready Aristotle result bundles first. Both targeted already-closed AB3 declarations (`ab3Vec_one_step_error_bound` and `ab3_local_residual_bound`), so they were rejected as redundant.

Built the AB4 vector chain sorry-first, verified the scaffold compiled, then closed the declarations directly:
- `LMM.ab4IterVec` and boundary lemmas.
- `LMM.ab4VecResidual` and residual unfolding.
- Vector Lipschitz and 4-window max-norm recurrence with effective constant `(20/3) * L`.
- Vector interval-integral Taylor helpers through fifth order.
- Pointwise and uniform residual bounds with `20 * M * h^5`.
- Headline `LMM.ab4Vec_global_error_bound` via `lmm_error_bound_from_local_truncation` at `p = 4`.

No new Aristotle batch was submitted because the sorry-first AB4 vector scaffold was closed to 0 sorrys before the strategy gate for new submissions.

## Result
SUCCESS. `OpenMath/LMMAB4Convergence.lean` compiles with 0 sorrys and contains `LMM.ab4Vec_global_error_bound`. `plan.md` now records the AB4 vector chain and points the active frontier to a generic Adams-Bashforth `s`-step convergence abstraction.

## Dead ends
The first direct vector Lipschitz proof hit the 200000-heartbeat cap during a large algebraic/norm expression. Splitting the triangle inequality through short local abbreviations (`A`, `B`, `C`, `D`, `G`) avoided the expensive `isDefEq`/`whnf` work.

## Discovery
The scalar AB4 Lagrange-remainder proof cannot be reused verbatim for vector-valued trajectories. The vector chain needs the AB3-style interval-integral remainder helpers, extended one derivative higher. The same scalar slack fix works for the vector residual: prove `57588/2880 ≤ 20`, multiply by nonnegative `M * h^5`, then finish with `linarith`.

## Suggested next approach
Use the closed AB2/AB3/AB4 scalar and vector chains to design the generic Adams-Bashforth `s`-step convergence abstraction. Start by parameterizing the max-window Lipschitz constant by the ℓ¹ norm of the AB coefficients and the residual order by the existing `adamsBashforthN_order_N`/`errorConstant` data.
