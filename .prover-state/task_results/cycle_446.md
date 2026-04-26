# Cycle 446 Results

## Worked on
BDF1 (backward Euler) scalar quantitative convergence chain — new file
`OpenMath/LMMBDF1Convergence.lean`. First entry of the BDF quantitative
convergence frontier announced in `plan.md` after closing the
AB2–AB6 + AM2–AM7 §1.2 stack.

## Aristotle bundles
The two listed "ready" bundles were rejected without incorporation,
following the strategy:

- `d76a4ce0-…` targets `OpenMath/LMMAM6VectorConvergence.lean` — already
  sorry-free (`grep -c sorry` = 0).
- `2f036517-…` targets `OpenMath/LMMAM3VectorConvergence.lean` — already
  sorry-free (`grep -c sorry` = 0).

These are stale leftovers from earlier cycles and pulling code from them
risks reintroducing stub dependency files (the recurring failure mode from
cycles 362–366, 389, 433, 435, 442–445). Both bundles were left in place;
no upstream OpenMath files were modified.

No new Aristotle batch was submitted this cycle: the BDF1 sorry-first
scaffold mirrors the AM2 / forward-Euler templates so closely that the full
proofs were written directly. Aristotle compute can be saved for the next
BDF cycle (vector BDF1 or BDF2 scalar).

## Approach
1. Mirror the AM2 implicit template (`OpenMath/LMMAM2Convergence.lean`),
   specialised to the 1-step case:
   - `IsBDF1Trajectory h f t₀ y` — predicate
     `y_{n+1} = y_n + h · f(t₀ + (n+1)·h, y_{n+1})`.
   - `bdf1_localTruncationError_eq` — textbook unfolding
     `backwardEuler.localTruncationError h t y = y(t+h) − y(t) − h · y'(t+h)`.
   - `bdf1_one_step_lipschitz` — implicit Lipschitz inequality
     `(1 − h·L) · |y_{n+1} − y(t_{n+1})| ≤ |y_n − y(t_n)| + |τ_n|` under
     the small-step regime `h·L ≤ 1/2`.  Used the cycle-438 lesson: the
     implicit substitution is performed via `conv_lhs => rw [hstep]` so
     it does not rewrite inside `f tn1 (y …)`.
   - `bdf1_one_step_error_bound` — divide out `(1 − h·L)`; the slackened
     constants are growth `2L` and residual coefficient `2`, matching the
     strategy.
2. `bdf1_pointwise_residual_bound` (private) — split the BDF1 residual as
   `R_BDF1 = R_FE − h · (y'(t+h) − y'(t))`.
   - Bound `|R_FE| ≤ M/2 · h²` by the same `taylor_mean_remainder_lagrange_iteratedDeriv`
     argument used in `forwardEuler_pointwise_residual_bound`
     (private in `LMMTruncationOp.lean`, ported locally).
   - Bound `|y'(t+h) − y'(t)| ≤ M · h` via
     `norm_image_sub_le_of_norm_deriv_le_segment'` applied to `deriv y`
     with derivative `iteratedDeriv 2 y`.
   - Combine: `(3/2) · M · h² ≤ 2 · M · h²` via `nlinarith`.
3. `bdf1_local_residual_bound` — uniform `|τ_n| ≤ 2M · h²` on the finite
   horizon `(n+1)·h ≤ T`, using the local helper
   `iteratedDeriv_two_bounded_on_Icc'` (port of the private helper from
   `LMMTruncationOp`).
4. `bdf1_global_error_bound` — assemble via
   `lmm_error_bound_from_local_truncation` at `p = 1`, growth constant
   `2L`, residual coefficient `2C`.

## Result
SUCCESS. `OpenMath/LMMBDF1Convergence.lean` compiles cleanly under
`lake env lean OpenMath/LMMBDF1Convergence.lean` with zero warnings, zero
sorries, and 432 lines.  No upstream files modified.

## Dead ends
None encountered. The proof structure followed the AM2 / forward-Euler
templates faithfully; the only minor judgment call was choosing
forward-Euler-Taylor + segment-derivative-bound (yields `(3/2)·M·h²`,
slackened to `2·M·h²`) over a direct backward-Taylor approach (would have
required the reverse-direction Lagrange remainder lemma which does not
match the standard Mathlib form).

## Discovery
- The BDF1 residual `y(t+h) − y(t) − h · y'(t+h)` decomposes cleanly as
  `R_FE − h · (y'(t+h) − y'(t))`.  This avoids needing a backward Taylor
  remainder lemma and reuses the same Taylor-residual proof pattern as
  forward Euler.
- The implicit `(1 − h·L)` factor inversion is handled by exhibiting
  `(1 − h·L)·((1 + h·(2L))·en + 2·τ) ≥ en + τ` under `h·L ≤ 1/2`, which
  closes by `nlinarith [hx_nn, hsmall]`.  This packaging is simpler than
  AM2's `nlinarith [hx_nn, hx_small]` because BDF1 has no other implicit
  weights to track.
- `iteratedDeriv_two_bounded_on_Icc` and `forwardEuler_pointwise_residual_bound`
  are both `private` to `LMMTruncationOp.lean`. Following the strategy's
  "Reuse public helpers if available; otherwise port theorem-locally and
  keep `private`" rule, the helpers were ported privately into the new
  file — no upstream API changes.

## Suggested next approach
1. **BDF1 vector quantitative convergence** (`LMMBDF1VectorConvergence.lean`)
   — mirror this scalar chain in finite-dimensional normed spaces, reusing
   the vector forward-Euler Taylor remainder helper from `LMMTruncationOp`
   (`forwardEulerVec_pointwise_residual_bound` is private but the
   integral-FTC residual proof can be ported locally, or that helper can
   be promoted upstream first per the cycle 438 lesson).
2. **BDF2 scalar quantitative convergence** — 2-step implicit; mirror AM2
   structurally but adapt the recurrence to BDF2 weights
   `α = ![1/3, −4/3, 1]`, `β = ![0, 0, 2/3]`. The implicit-divide step
   factors out `(2/3)·h·L`; the local residual is `O(h³)` (BDF2 has
   order 2 with `errorConstant 2 = −2/9`).  Use the AM2 template plus
   the AB3 third-order Taylor helpers (`y_third_order_taylor_remainder`,
   `derivY_second_order_taylor_remainder`) for the residual bound.
3. After BDF1 vector + BDF2 scalar, continue up the BDF stack:
   BDF2 vector → BDF3 scalar/vector → … → BDF6 scalar/vector.  BDF7 is
   not zero-stable (cycle 379), so it falls outside the quantitative
   convergence stack.
