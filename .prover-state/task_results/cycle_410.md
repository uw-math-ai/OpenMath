# Cycle 410 Results

## Worked on

Vector-valued Adams–Bashforth 2-step convergence chain in
`OpenMath/LMMTruncationOp.lean`. Mirrors the cycle 408 scalar AB2 chain in the
finite-dimensional normed-vector setting that cycle 407 used for forward Euler.

## Approach

Followed the planner's blueprint exactly: built the chain in the same order as
cycle 408, importing types and `intervalIntegral` Taylor remainder
infrastructure from cycle 407. Closed every sorry directly without an
Aristotle round — the proofs follow cycle 408 / 407 templates closely enough
that no compute was needed.

New declarations (all sorry-free):

1. `LMM.ab2IterVec` — vector AB2 iteration
   `y_{n+2} = y_{n+1} + h • ((3/2) • f(t_{n+1}, y_{n+1}) − (1/2) • f(t_n, y_n))`
   with two starting samples; plus the `_zero`, `_one`, `_succ_succ` simp lemmas.
2. `LMM.ab2VecResidual` + `LMM.ab2Vec_localTruncationError_eq` — names the
   textbook AB2 vector residual
   `y(t + 2h) − y(t + h) − h • ((3/2) • y'(t + h) − (1/2) • y'(t))` and unfolds
   it (rfl). The strategy item literally referenced
   `LMM.localTruncationError`, but `localTruncationError` is scalar-only
   (returns `ℝ`); the natural vector mirror is the named residual above, which
   is what the rest of the chain consumes.
3. `LMM.ab2Vec_one_step_lipschitz` — single-step linearised increment with two
   Lipschitz contributions and additive `‖τ_n‖`.
4. `LMM.ab2Vec_one_step_error_bound` — max-norm recurrence
   `EN (n+1) ≤ (1 + h·2L) · EN n + ‖τ_n‖`.
5. Private helpers:
   - `iteratedDeriv_three_bounded_on_Icc_vec` — compact-interval bound on `‖y'''‖`.
   - `derivY_second_order_taylor_remainder_vec` — `‖y'(t+r) − y'(t) − r • y''(t)‖ ≤ M/2 · r²`,
     proved via `intervalIntegral` + `norm_image_sub_le_of_norm_deriv_le_segment'`.
   - `y_third_order_taylor_remainder_vec` — `‖y(t+r) − y(t) − r • y'(t) − r²/2 • y''(t)‖ ≤ M/6 · r³`,
     proved via FTC for `y` + the second-order remainder above as the integrand bound.
   - `ab2Vec_pointwise_residual_bound` — combined Taylor remainders → `(9/4)·M·h³`.
6. `LMM.ab2Vec_local_residual_bound` — uniform `‖τ_n‖ ≤ C·h³` from a `ContDiff ℝ 3 y`
   solution.
7. `LMM.ab2Vec_global_error_bound` — final
   `‖y_N − y(t₀ + N·h)‖ ≤ exp(2L·T)·ε₀ + K·h²` for `(N+1)·h ≤ T`, packaged via
   the existing `lmm_error_bound_from_local_truncation` Grönwall bridge at `p = 2`
   with effective Lipschitz constant `2L` (same shape as cycle 408).

## Result

SUCCESS — `lake env lean OpenMath/LMMTruncationOp.lean` and `lake build
OpenMath.LMMTruncationOp` both pass with zero errors. No sorries anywhere in
the file. Tracked file size: 2860 lines (well under the 3000-line cap).

## Dead ends / fix-ups during build

- First scaffold of `halg` got the sign of `τ` wrong (`+ τ` instead of `- τ`).
  Re-derived the AB2 algebraic decomposition by adding/subtracting
  `zn1 + h • ((3/2) • f tn1 zn1 − (1/2) • f tn zn)` and confirmed the
  textbook identity has `− τ`.
- Tried `hy.iteratedDeriv_right` to extract `ContDiff ℝ 1 (iteratedDeriv 2 y)`;
  doesn't exist (Lean parsed it as a struct projection on the underlying
  `Exists` of `ContDiff`). Replaced with `hy.differentiable_iteratedDeriv 2`,
  which is the canonical mathlib API.
- `intervalIntegral.integral_comp_sub_right` + `simp; rw` collapsed too far —
  ended up rewriting the integral of `(s − t)^2` directly via `integral_pow`
  on the substituted bounds `[0, r]`.

## Discovery

- `ContDiff.differentiable_iteratedDeriv (m : ℕ) (h : ContDiff 𝕜 n f)
  (hmn : m < n) : Differentiable 𝕜 (iteratedDeriv m f)` is the right hammer
  for "I have C^k, I want differentiability of an iterated derivative below
  k". This is cleaner than going through `iterate_deriv'` + `iteratedDeriv_eq_iterate`.
- The third-order vector Taylor remainder cleanly reduces to the second-order
  one via FTC: integrate `g'(s) = y'(t+s) − y'(t) − s • y''(t)` from `0` to
  `r`, bound the integrand by `M/2 · s²`, integrate to get `M/6 · r³`. No
  need for Lagrange-style mean-value remainders (which mathlib only gives in
  the scalar setting).
- `module` tactic closes the AB2 LTE algebraic identity in one line once the
  scalar coefficients are normalised by hand.

## Suggested next approach

Natural follow-ups in the 406 → 407 → 408 → 410 pattern:

1. Adams–Moulton 2-step vector chain (implicit, order 3, residual `O(h^4)`)
   — would need a fixed-point argument for the implicit step, which is new
   infrastructure.
2. AB3 scalar chain (order 3, three starting samples, residual `O(h^4)`) —
   pure mirror of cycle 408 with `α = [0, 0, -1, 1], β = [5/12, -16/12, 23/12, 0]`.
   No new tactics required; effective Lipschitz constant becomes `(5 + 16 + 23)/12 · L`.
3. Alternatively: lift `lmm_error_bound_from_local_truncation` to vector
   sequences (`e : ℕ → E`) so future LMM vector chains don't have to take a
   `max ‖·‖` detour and can apply the Grönwall bridge directly.
