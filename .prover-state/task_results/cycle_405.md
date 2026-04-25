# Cycle 405 Results

## Worked on
Added the textbook finite-horizon specialization of exponential discrete
Gronwall in `OpenMath/LMMTruncationOp.lean`:

- `LMM.discrete_gronwall_exp_horizon`
- `LMM.lmm_error_bound_from_local_truncation`

## Approach
Followed the sorry-first and Aristotle-first workflow.

1. Inserted `discrete_gronwall_exp_horizon` with a single `sorry` immediately
   after `discrete_gronwall_exp`.
2. Verified the target file compiled with only the expected sorry warning.
3. Submitted a five-job Aristotle batch and slept via `sleep 1800` before one
   refresh pass.
4. Extracted the complete Aristotle bundles and used the clean subproofs to
   close the live theorem explicitly.

The live proof specializes `discrete_gronwall_exp` with `a := h * L` and
`b := C * h ^ (p + 1)`. It then proves the two textbook horizon estimates:

- `Real.exp ((h * L) * n) ≤ Real.exp (L * T)` by rewriting the exponent to
  `L * (n * h)` and applying `Real.exp_le_exp` plus
  `mul_le_mul_of_nonneg_left hnh hL`.
- `(n : ℝ) * h ^ (p + 1) ≤ T * h ^ p` by rewriting as
  `((n : ℝ) * h) * h ^ p` and multiplying `hnh` on the right by
  `h ^ p ≥ 0`.

The first summand is bounded with `mul_le_mul_of_nonneg_right`. The forcing
summand is bounded by first increasing the exponential factor and then the
time-power factor, using nonnegativity of `C`, `h ^ (p+1)`, and `exp(L*T)`.

## Aristotle bundles
Submitted and refreshed once after the required wait:

- `9f0b0d4f-8f9a-4d63-808d-e020c758c00f`
  (`discrete_gronwall_exp_horizon`): COMPLETE. Accepted the proof strategy,
  but did not transplant verbatim because it compressed key ordered-ring
  steps through broad `positivity`/`nlinarith`; the live proof spells out the
  monotonicity lemmas requested by the planner.
- `88f0f92d-a179-4e8d-9bfc-42ed24171e94`
  (`cycle405_exp_time_bound`): COMPLETE. Incorporated the core proof:
  `Real.exp_le_exp` after multiplying `hnh` by nonnegative `L`.
- `2a056ab8-2d2a-4e84-8589-b788dde2338d`
  (`cycle405_pow_time_bound`): COMPLETE. Incorporated the power/time bound,
  keeping it inline in the live proof rather than adding a public helper.
- `49177543-ddab-48a0-b7b5-c0691cf1616a`
  (`cycle405_discrete_gronwall_exp_horizon_direct`): COMPLETE. Rejected as a
  direct transplant because it was a scaffold theorem importing the live file
  with the target sorry and used broad `nlinarith` compression. Its
  `discrete_gronwall_exp` application matched the live proof structure.
- `bc030e59-5fec-414a-934c-ca42c2bc45f6`
  (`cycle405_horizon_linarith_assembly`): COMPLETE. Accepted as a sanity check
  that the final assembly is purely order-theoretic; the live proof uses
  `.trans (add_le_add ...)` instead of a separate linarith-only helper.

No bundle rebuilt `LMM`, `truncationOp`, `errorConstant`, or `HasOrder`; no
bundle requiring a new live helper file was imported.

## Result
SUCCESS.

- `OpenMath/LMMTruncationOp.lean` compiles cleanly with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMTruncationOp.lean`.
- `lean_verify LMM.discrete_gronwall_exp_horizon` reports only
  `[propext, Classical.choice, Quot.sound]` and no source warnings.
- Added the optional packaging lemma
  `LMM.lmm_error_bound_from_local_truncation`.
- Updated `plan.md` under §1.2 with the new horizon Gronwall bridge.

## Dead ends
No mathematical dead end. The only rejected transplant was the generated
direct scaffold proof because it was too compressed and lived in a scaffold
context that imported the target theorem while it still had a sorry.

## Discovery
The cleanest live assembly is to view the forcing summand as

```lean
(Real.exp ((h * L) * (n : ℝ)) * C) * ((n : ℝ) * h ^ (p + 1))
```

and then apply monotonicity in two separate steps: first the exponential
factor, then the time-power factor. This avoids needing any division or
case split on `h = 0`.

## Suggested next approach
Cycle 406 should build the missing one-step error recurrence interface that
feeds `lmm_error_bound_from_local_truncation`. Start with the simplest scalar
Lipschitz scalar-ODE recurrence,
`e (n+1) ≤ (1 + h * L) * e n + C * h^(p+1)`, before attempting the full
multistep companion-matrix Lipschitz infrastructure. Once that recurrence is
available, the global `O(h^p)` theorem should be one application of the new
horizon Gronwall packaging lemma.
