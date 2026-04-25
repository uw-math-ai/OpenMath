# Cycle 407 Results

## Worked on
Vector-valued forward-Euler convergence chain in
`OpenMath/LMMTruncationOp.lean`, lifting the cycle-406 scalar chain to
finite-dimensional normed vector state spaces.

## Approach
Followed the strategy's sorry-first / Aristotle-first workflow.

1. Verified the cycle-406 Aristotle results were already present in the
   live scalar section.
2. Added the vector scaffold at the bottom of `LMMTruncationOp.lean`:
   `forwardEulerIterVec`, `forwardEulerVec_one_step_error_bound`,
   private `iteratedDeriv_two_bounded_on_Icc_vec`,
   private `forwardEulerVec_pointwise_residual_bound`,
   `forwardEulerVec_local_residual_bound`, and
   `forwardEulerVec_global_error_bound`.
3. Ran
   `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMTruncationOp.lean`;
   the scaffold elaborated with exactly five intended proof sorries.
4. Submitted five Aristotle jobs in one batch, slept via `sleep 1800`,
   then did a single refresh pass.
5. Incorporated the clean uniform-derivative-bound and local-residual
   proofs, mined the one-step/global proof shape from rejected stub
   bundles, and completed the vector Taylor residual manually using the
   integrated mean-value route.

## Result
SUCCESS. `OpenMath/LMMTruncationOp.lean` is sorry-free and builds with the
NVMe toolchain command. `plan.md` §1.2 now records the cycle-407
Forward-Euler vector convergence chain.

New public API:

```lean
noncomputable def LMM.forwardEulerIterVec
theorem LMM.forwardEulerVec_one_step_error_bound
theorem LMM.forwardEulerVec_local_residual_bound
theorem LMM.forwardEulerVec_global_error_bound
```

Private helpers:

```lean
private theorem LMM.iteratedDeriv_two_bounded_on_Icc_vec
private theorem LMM.forwardEulerVec_pointwise_residual_bound
```

## Aristotle jobs
- `56daf6b2-543c-48ee-a575-4284a78e5a2d` (Job A): COMPLETE. Accepted and
  transplanted the compactness proof using
  `ContDiff.continuous_iteratedDeriv`.
- `99cf87dc-ea6f-46e7-9881-545dcb2cf4da` (Job B): COMPLETE_WITH_ERRORS.
  Rejected as a direct patch, but it identified the correct interval
  integral route. The live proof uses
  `norm_image_sub_le_of_norm_deriv_le_segment'`,
  `intervalIntegral.integral_deriv_eq_sub`, and
  `intervalIntegral.norm_integral_le_of_norm_le`.
- `2c6b4413-c5bd-4687-8038-d2cf781454da` (Job C):
  COMPLETE_WITH_ERRORS. Rejected as a patch because the bundle added a
  stub `OpenMath/MultistepMethods.lean`. Mined the vector one-step proof
  pattern (`norm_sub_le`, `norm_add_le`, `norm_smul`, Lipschitz +
  `nlinarith`) and completed it in the live project.
- `7a12acaf-4967-4192-9061-fbb75c22746c` (Job D): COMPLETE. Accepted and
  transplanted the local residual wrapper.
- `2792f924-8fb7-40d8-b904-246b7640e8ed` (Job E):
  COMPLETE_WITH_ERRORS. Rejected as a patch because the bundle added a
  stub `OpenMath/MultistepMethods.lean`; mined the scalar-shaped
  Grönwall assembly and completed the live theorem.

## Dead ends
The direct Job B proof did not transplant as-is: it used fragile interval
integral rewrites and some names that did not elaborate in the live
project. The repaired proof avoids a vector-valued Lagrange equality and
instead:

1. bounds `‖deriv y s - deriv y t‖ ≤ M * (s - t)` on every subsegment
   `[t, s]`;
2. rewrites the residual as
   `∫ s in t..t+h, (deriv y s - deriv y t)`;
3. bounds this integral by `∫ s in t..t+h, M * (s - t) = M / 2 * h^2`.

## Discovery
`Mathlib.Analysis.SpecialFunctions.Integrals.Basic` supplies the scalar
interval integral identities needed to evaluate
`∫ s in t..t+h, M * (s - t)`. The vector-valued residual proof otherwise
only needs calculus and interval-integral infrastructure already pulled
through the local truncation file.

## Suggested next approach
Use `forwardEulerVec_global_error_bound` as the consumer-side template for
future vector and companion-matrix convergence work. The next natural
step is still the deferred `s ≥ 2` companion-matrix recurrence, where the
error sequence should be a real norm/max-norm sequence so it can feed the
existing `lmm_error_bound_from_local_truncation` bridge.
