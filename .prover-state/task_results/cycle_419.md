# Cycle 419 Results

## Worked on
Adams-Bashforth 3-step vector convergence chain in
`OpenMath/LMMAB3Convergence.lean`.

## Approach
Triaged the two completed cycle-418 Aristotle bundles first:
`16e061c6-b378-4b44-a168-03790f35b464` and
`b199f8ce-7690-4fac-9c43-1f0b71800784`. Both target scalar AB3 helpers
were already manually proved in the live file, so I rejected the bundles as
redundant.

Added the AB3 vector iteration, vector residual surface, one-step Lipschitz
and max-window recurrence, interval-integral vector Taylor helpers, pointwise
residual bound, uniform local residual bound, and headline global error bound.
The global theorem uses `lmm_error_bound_from_local_truncation` at `p = 3`
with effective Lipschitz constant `(11 / 3) * L`.

Submitted the required cycle-419 Aristotle batch from scaffolds under
`.prover-state/aristotle_scaffolds/cycle_419/`:

- `5da7319d-287a-4925-8a81-cbfe01406510`:
  `job_a_iteratedDeriv_four_bounded_on_Icc_vec.lean`
- `87637e1a-7994-483a-8d45-ae41c2a22181`:
  `job_b_y_fourth_order_taylor_remainder_vec.lean`
- `b0a28576-0064-4253-a105-309340518cf3`:
  `job_c_derivY_third_order_taylor_remainder_vec.lean`
- `893afb82-6924-4c6b-8892-4546226311c8`:
  `job_d_ab3Vec_pointwise_residual_bound.lean`
- `6d62aa43-e081-447b-9775-b4e6dfb0eb7b`:
  `job_e_ab3Vec_one_step_error_bound.lean`

Post-wait Aristotle status refresh:

- `5da7319d-287a-4925-8a81-cbfe01406510`: COMPLETE. Rejected as redundant
  because `iteratedDeriv_four_bounded_on_Icc_vec` is already closed manually in
  the live file.
- `87637e1a-7994-483a-8d45-ae41c2a22181`: IN_PROGRESS, 8%.
- `b0a28576-0064-4253-a105-309340518cf3`: IN_PROGRESS, 6%.
- `893afb82-6924-4c6b-8892-4546226311c8`: IN_PROGRESS, 10%.
- `6d62aa43-e081-447b-9775-b4e6dfb0eb7b`: IN_PROGRESS, 10%.

The remaining cycle-418 jobs were checked in the same post-wait list:
`0dd9f346-5325-4ec3-9f72-6ec9f4a827c5` is COMPLETE and redundant because
the scalar pointwise residual helper is already closed; `93418f8b-824f-4e2a-9fd7-f546332eacef`
is COMPLETE_WITH_ERRORS and redundant for the same reason; and
`ea0a7416-57a6-479f-8fc8-53b81203e295` is still IN_PROGRESS.

## Result
SUCCESS. The live target file is sorry-free and compiles with
`lake env lean OpenMath/LMMAB3Convergence.lean`. `lean_verify` reports only
the standard Mathlib axioms for `LMM.ab3Vec_global_error_bound` and
`LMM.ab3Vec_one_step_error_bound`.

Updated `plan.md` with the cycle-419 vector AB3 entry and moved the active
frontier to AB4 scalar or a possible generic Adams-Bashforth abstraction.

## Dead ends
None. The vector Taylor layer was slightly longer than AB2, but the recursive
interval-integral pattern scaled cleanly.

## Discovery
The AB2 vector helper pattern generalizes well if factored locally into a
generic second-order derivative remainder and a generic third-order vector
Taylor remainder. This avoids Lagrange-form scalar Taylor entirely and keeps
the vector AB3 pointwise residual proof close to the scalar algebra.

## Suggested next approach
Start AB4 scalar at order `p = 4`, or first factor the now-visible AB2/AB3
duplication into a small generic Adams-Bashforth helper if the planner wants
to reduce the AB4 proof size.
