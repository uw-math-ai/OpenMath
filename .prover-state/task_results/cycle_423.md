# Cycle 423 Results

## Worked on

Adams-Bashforth 5-step vector convergence chain in
`OpenMath/LMMAB5Convergence.lean`, alongside the scalar AB5 chain from
cycle 422.

## Approach

Followed the AB4 vector chain structure and the AB5 scalar coefficient
arithmetic. Added `ab5IterVec`, the AB5 vector residual, the 5-window
Lipschitz and max-error recurrences with effective constant `(551/45) * L`,
vector Taylor remainder helpers through sixth order, the pointwise
`59 * M * h^6` residual estimate, the uniform local residual bound, and
the headline `ab5Vec_global_error_bound` via
`lmm_error_bound_from_local_truncation` at `p = 5`.

Used a sorry-first scaffold and verified it compiled before filling proofs.
Submitted the required five Aristotle jobs, slept 30 minutes, and performed
one refresh:

- `d8c9fa72-5cc3-4718-86e9-89830e077df8` (`ab5Vec_one_step_lipschitz`):
  `IN_PROGRESS`, 15%.
- `ecb451c8-f9a3-49a9-a2f3-69dfe7d9759e`
  (`ab5Vec_one_step_error_bound`): `COMPLETE_WITH_ERRORS`.
- `9202af0e-688a-4e44-97f7-4cc0cd4ef0a8`
  (`ab5Vec_pointwise_residual_bound`): `IN_PROGRESS`, 14%.
- `66e55a49-ae8d-45ec-9454-308a7510bd73`
  (`ab5Vec_local_residual_bound`): `COMPLETE_WITH_ERRORS`.
- `f51379c9-15d5-46ea-b0d7-e8b38460ef80`
  (`ab5Vec_global_error_bound`): `COMPLETE_WITH_ERRORS`.

Per policy, the still-running jobs were forfeited after the one refresh.
No Aristotle output was incorporated.

## Result

SUCCESS. `OpenMath/LMMAB5Convergence.lean` compiles with 0 sorries and 0
errors under:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAB5Convergence.lean
```

The file is 2876 lines, under the 3000-line soft cap. `plan.md` now marks
the AB5 vector chain complete and updates the active frontier to the generic
Adams-Bashforth `s`-step convergence abstraction.

## Dead ends

Aristotle did not produce usable proofs in the required window. The
mechanical AB4-vector/AB5-scalar transcription worked manually.

One local heartbeat issue appeared in a coefficient norm subproof when using
`nlinarith`; replacing those closures with short `calc` chains avoided
raising `maxHeartbeats`.

## Discovery

The vector sixth-order Taylor remainder is most manageable by reusing the
fifth-order vector Taylor helper on `deriv y` locally, then integrating the
degree-5 derivative remainder. The AB5 pointwise residual algebra mirrors the
scalar slack computation exactly once the vector expression is split into
short named terms.

## Suggested next approach

With AB2-AB5 scalar and vector convergence chains now closed, the planner can
start a small generic Adams-Bashforth `s`-step convergence abstraction. The
AB4 and AB5 vector proofs show that the generic proof should expose named
coefficient-weighted norm terms rather than relying on one monolithic
triangle inequality or large arithmetic goal.
