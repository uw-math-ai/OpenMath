# Cycle 451 Results

## Worked on
Adams-Bashforth 7-step finite-dimensional vector quantitative convergence chain in
`OpenMath/LMMAB7VectorConvergence.lean`.

## Approach
Mirrored the cycle-450 scalar AB7 chain and the cycle-425 AB6 vector lift:
added `LMM.ab7IterVec`, `LMM.ab7VecResidual`, one-step Lipschitz and
max-window recurrence bounds, eighth-order vector Taylor helpers, pointwise
and local residual bounds, generic AB vector bridge lemmas, and
`LMM.ab7Vec_global_error_bound`.

Rejected stale Aristotle bundle `e0dc83ae-0729-473b-aabd-7c1fdd2c1a00` as
redundant: it targets `LMMBDF2VectorConvergence.lean`, which already exists
on the live tree and is sorry-free from cycle 449.

Submitted five Aristotle jobs for AB7 vector triage after the sorry-first file
compiled:
- `ce7eaf76-1269-4f6e-a43c-9926b06cfe94`
- `a4db6fcc-67b4-4b41-bb25-d09f5573e94e`
- `29ee838e-7fc0-4d1d-b97e-4f02510f2f06`
- `50b6e2ef-b676-4d1e-98aa-0224608599f8`
- `e3b7bfab-25d4-4f43-958e-5a7cec6d6164`

After the required 30-minute sleep, all five were still `QUEUED`, so the
proofs were closed manually.

## Result
SUCCESS. The AB7 vector chain is closed with no sorries. The pointwise
residual coefficient is the scalar AB7 coefficient
`159970508328/304819200`, slacked to `525`, giving `‖τ_n‖ ≤ 525*M*h^8`.
The effective Lipschitz constant is `(40633/945)*L`.

No upstream helper promotions were needed. The eighth-order vector Taylor
helpers were ported privately from the AM6 vector pattern and reuse the
already-public seventh-order AB6 vector helpers.

## Dead ends
Aristotle produced no completed output in the allotted check window. No
mathematical blocker was encountered.

## Discovery
The same kernel-budget trick from cycle 450 was needed: use `clear_value`
after the 16 Taylor component names and after the eight residual chunks in
`ab7Vec_pointwise_residual_bound`. The slack inequality was kept explicit via
`mul_assoc` and `mul_le_mul_of_nonneg_right`, avoiding a large `linarith`
normalization over the pointwise context.

## Suggested next approach
Proceed to AM8 scalar quantitative convergence as the next Adams-family
target. If AM8 stalls, use BDF3 scalar quantitative convergence as the
alternate frontier.

## Verification
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAB7VectorConvergence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.LMMAB7VectorConvergence`
- `lean_verify LMM.ab7Vec_global_error_bound`: standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`), no source warnings.
