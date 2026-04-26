# Cycle 453 Results

## Worked on
AM8 vector quantitative convergence was the primary target.  After it stalled
on the tenth-order vector residual infrastructure, I followed the fallback:
promoted the AM7 vector Taylor helper ladder and started the BDF3 scalar
quantitative convergence chain.

## Approach
I first inspected the two ready Aristotle AB7 vector bundles
`50b6e2ef-b676-4d1e-98aa-0224608599f8` and
`a4db6fcc-67b4-4b41-bb25-d09f5573e94e`.  Both targeted the already-closed
`OpenMath/LMMAB7VectorConvergence.lean`, and both used stale standalone
imports, so I did not rebase the live file onto them.

I then submitted five AM8 vector scaffold jobs to Aristotle and slept for the
required 30 minutes before a single status pass:

- `44ac525a-4bed-486e-a525-6aeafe7906fc`: COMPLETE.  Filled only
  `am8Vec_localTruncationError_eq` by `rfl` in the scaffold after replacing
  OpenMath imports with `import Mathlib`; no live tracked AM8 vector module was
  available to incorporate it into.
- `a2b23ad4-42df-4949-ad11-4f05751b0a5a`: IN_PROGRESS, 7%.
- `1f0a84ab-6d8e-424f-b4d9-2b0f41805153`: IN_PROGRESS, 4%.
- `6565e69d-94ea-4559-b22e-5d09e2fdede5`: QUEUED.
- `4917694c-6568-4665-a3d8-aa76423a11c7`: QUEUED.

I attempted a mechanical AM7-vector to AM8-vector rewrite, but discarded it:
the scalar `*` to vector `•` conversion around the ten-term residual identity
was too fragile without the tenth-order vector Taylor helpers in place.

## Result
SUCCESS on the fallback work.

Promoted these AM7 vector Taylor helpers from private to public in
`OpenMath/LMMAM7VectorConvergence.lean`:

- `iteratedDeriv_nine_bounded_on_Icc_vec`
- `am7Vec_y_eighth_order_taylor_remainder_vec`
- `y_ninth_order_taylor_remainder_vec`
- `derivY_eighth_order_taylor_remainder_vec`

Added `OpenMath/LMMBDF3Convergence.lean` with:

- `LMM.IsBDF3Trajectory`
- `LMM.bdf3_localTruncationError_eq`
- `LMM.bdf3_one_step_lipschitz`
- `LMM.bdf3_pointwise_residual_bound`
- `LMM.bdf3_local_residual_bound`

The BDF3 residual estimate uses the identity
`tau = R_y(3) - (18/11) R_y(2) + (9/11) R_y(1) - (6h/11) R_y'(3)` and
slackens the exact coefficient `153/22` to `7`, giving
`|tau_n| <= 7*M*h^4`.

## Dead ends
The AM8 vector port needs a dedicated tenth-order vector Taylor ladder before
the residual split can be made kernel-safe.  The scalar AM8 constants carried
forward are:

- weights over denominator `3628800` with sign pattern `+,+,-,+,-,+,-,+,-`
- implicit weight `1070017/3628800`
- growth constant `15`
- residual exact coefficient `4555920744497/6858432000`, slackened to `665`
- pivotal one-step identity
  `(hL/3628800) * (28877438 - 16050255*hL) >= 0`

Those constants were not landed in a tracked AM8 vector file this cycle.

## Discovery
The next AM8 vector attempt should start by proving only:

- `iteratedDeriv_ten_bounded_on_Icc_vec`
- `y_tenth_order_taylor_remainder_vec`
- `derivY_ninth_order_taylor_remainder_vec`

Once those compile, port the AM8 residual in the same four-helper split used
by AM7 vector and AM8 scalar: algebra identity, bound identity, ten-term
triangle, and final combine lemma.

## Suggested next approach
For AM8 vector, land the three tenth-order vector Taylor helpers first and
only then port the residual split.  For the BDF3 fallback chain, continue from
`bdf3_one_step_lipschitz` by developing the stable three-window Lyapunov
recurrence for the BDF3 companion matrix roots `1` and
`(7 +/- sqrt(-39))/(22)`, then combine it with
`bdf3_local_residual_bound` for the global `O(h^3)` theorem.
