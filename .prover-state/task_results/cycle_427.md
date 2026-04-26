# Cycle 427 Results

## Worked on

Vector mirror of the generic Adams-Bashforth convergence scaffold in
`OpenMath/LMMABGenericConvergence.lean`.

## Approach

1. Re-read `.prover-state/strategy.md`, `plan.md`, and cycle 426 results.
2. Triage-read the stale Aristotle result
   `87637e1a-7994-483a-8d45-ae41c2a22181`. Rejected it as instructed:
   it targets `y_fourth_order_taylor_remainder_vec`, which already exists
   as closed private infrastructure in AB3/AB4/AB5 vector chains. Its
   standalone output also raised `maxHeartbeats` to 400000, so it was not
   suitable for transplant.
3. Added the vector generic AB scaffold in place:
   `abIterVec`, `abIterVec_step`, `abErrVec`, `abResidualVec`,
   `abErrWindowVec`, `abErrWindowVec_nonneg`,
   `abLip_window_bound_vec`, `abIter_lipschitz_one_step_vec`, and
   `ab_global_error_bound_generic_vec`.
4. Used the sorry-first workflow: left exactly three sorries
   (`abErrWindowVec_nonneg`, `abIter_lipschitz_one_step_vec`,
   `ab_global_error_bound_generic_vec`) and verified
   `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
   OpenMath/LMMABGenericConvergence.lean`.
5. Submitted the required Aristotle batch and slept 30 minutes before one
   status refresh:
   - `9d22c3b1-78e5-4f4a-b0c7-0e890a6352fc`: COMPLETE, usable helper proof.
   - `105cd36e-c7ce-478b-a372-9377f8dd42ec`: COMPLETE_WITH_ERRORS. The
     one-step proof was generated against a standalone/stubbed environment,
     so it was used only as a guide.
   - `8268fb5e-005d-4f99-9bf1-cedadd75f607`: still IN_PROGRESS at the single
     allowed refresh; not polled again and not used.
6. Closed the remaining proofs manually by transliterating the scalar
   generic proof to norms and smul:
   `norm_sum_le`, `norm_smul`, per-summand Lipschitz bounds, and the same
   two `← Finset.sum_mul` rewrites to factor the finite sum.

## Result

SUCCESS.

`OpenMath/LMMABGenericConvergence.lean` compiles with no sorries. The three
required public declarations are present and proved:

- `LMM.abIterVec`
- `LMM.abIter_lipschitz_one_step_vec`
- `LMM.ab_global_error_bound_generic_vec`

Verification run:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMABGenericConvergence.lean
```

No existing AB2/AB3/AB4/AB5/AB6 convergence file was modified.

## Dead ends

- The Aristotle one-step output was not directly transplantable because it
  replaced the project imports with `Mathlib` and introduced a stub for
  `lmm_error_bound_from_local_truncation`. The proof shape was still useful.
- The stale `87637e1a` Taylor-remainder bundle remains intentionally
  rejected. No `OpenMath/TaylorBounds.lean` module was introduced.

## Discovery

- The scalar generic one-step proof ports cleanly to vector spaces once the
  scalar absolute-value sum bound is replaced by `norm_sum_le` and each term
  is bounded via `norm_smul`.
- The existing `abLip` constant is shape-agnostic; no duplicate `abLipVec`
  definition is needed.
- The abstract Gronwall consumer
  `lmm_error_bound_from_local_truncation` works unchanged because it only
  consumes a real-valued nonnegative error sequence.

## Suggested next approach

Refactor one concrete AB vector chain (probably AB2Vec first) through
`ab_global_error_bound_generic_vec` as a small pilot. Keep the Taylor
residual bound local to the per-step file and replace only the window-max
one-step/Gronwall plumbing.
