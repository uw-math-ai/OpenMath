# Cycle 443 Results

## Worked on
Adams-Moulton 6-step vector quantitative convergence chain in
`OpenMath/LMMAM6VectorConvergence.lean`.

## Approach
Created the sorry-first AM6 vector scaffold mirroring the AM5 vector file and
the scalar AM6 chain, verified the scaffold with
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/LMMAM6VectorConvergence.lean`, then submitted five Aristotle jobs:

- `2c19dff0-dee5-4e8b-973e-d701fb895d02`: `am6Vec_one_step_error_pair_bound`
- `0aecb55d-bca8-448a-992f-1b1628c4c96a`: `iteratedDeriv_eight_bounded_on_Icc_vec`
- `d76a4ce0-f7cd-47e4-8b63-d5350964a5e6`: `y_eighth_order_taylor_remainder_vec`
- `a8b33071-08be-4d7f-a2dd-72986d560011`: `derivY_seventh_order_taylor_remainder_vec`
- `67e400f2-f280-4bb9-aed6-8abd4272bef5`: `am6Vec_residual_combine`

After `sleep 1800`, all five jobs were still `QUEUED`, so there was no
Aristotle output to inspect or incorporate. I manually ported the structural
AM6 scalar / AM5 vector proof pattern, added private eighth-order vector
Taylor helpers, and kept the AM6 residual combination factored through a
separate helper.

## Result
SUCCESS. `OpenMath/LMMAM6VectorConvergence.lean` is sorry-free and proves
`LMM.am6Vec_global_error_bound`:

`‖yseq N - y (t₀ + (N : ℝ) * h)‖ ≤ Real.exp ((7 * L) * T) * ε₀ + K * h ^ 7`

under the planned side condition `((N : ℝ) + 5) * h ≤ T`.

Updated `plan.md` so the current target files include both
`OpenMath/LMMAM6Convergence.lean` and
`OpenMath/LMMAM6VectorConvergence.lean`, and the active frontier now names the
AM7 scalar/vector chain.

## Dead ends
No Lean proof dead ends. Aristotle did not produce usable output because all
five jobs remained queued after the mandated wait.

## Discovery
The AM6 vector chain can be closed cleanly by reusing the public seventh-order
vector Taylor helper on `deriv y` for the derivative remainder, then integrating
that bound to obtain the eighth-order value remainder. The scalar AM6
factored coefficient inequality and separated residual-combine helper port
directly to vector norms.

## Suggested next approach
Start the AM7 scalar/vector chain. Expect the main new cost to be ninth-order
Taylor helpers and a larger residual algebra/combine split; keep the AM6
factoring pattern rather than trying one large terminal `linarith`.
