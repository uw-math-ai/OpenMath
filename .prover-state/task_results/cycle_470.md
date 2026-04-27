# Cycle 470 Results

## Worked on
AB10 (Adams–Bashforth 10-step) scalar quantitative convergence chain in
`OpenMath/LMMAB10Convergence.lean` — full headline `LMM.ab10_global_error_bound`,
mirroring AB9 from cycle 468.

## Approach
Ported the cycle-468 AB9 chain step-by-step:

1. Three public eleventh-order Taylor helpers
   (`iteratedDeriv_eleven_bounded_on_Icc`, `y_eleventh_order_taylor_remainder`,
   `derivY_tenth_order_taylor_remainder`) — computed and proven inline, reusing
   `taylor_mean_remainder_lagrange_iteratedDeriv`.
2. `ab10Iter` / recursion lemmas / `ab10_localTruncationError_eq` linking the
   ten-step recurrence to the LMM truncation operator on `adamsBashforth10`
   (added in `AdamsMethods.lean`).
3. Extracted `ab10_step_alg_decomp` and a fresh
   `ab10_step_lipschitz_triangle` (eleven-term triangle aux with sign pattern
   `A + B − C + D − E + F − G + H − I + J − K`) to keep the kernel `whnf`
   budget under control during `ab10_one_step_lipschitz`. Final calc tail
   collapsed into a single `rw [heq]; linarith` after a second whnf
   timeout, mirroring the cycle-468 fix.
4. Residual chain (`ab10_residual_alg_identity` / `ab10_residual_bound_alg_identity` /
   `ab10_residual_eleven_term_triangle` / `ab10_residual_combine_aux`),
   followed by private `ab10_pointwise_residual_bound` (`|τ_n| ≤ 15695·M·h¹¹`,
   exact coefficient `11840488855359257/754427520000 ≈ 15694.67` — Python).
5. `ab10_one_step_error_bound` 10-window max-norm recurrence
   `max(eₙ₊₁,…,eₙ₊₁₀) ≤ (1+h·(172570/567)L)·max(eₙ,…,eₙ₊₉) + |τ_n|`.
6. `ab10GenericCoeff : Fin 10 → ℝ` + ten `@[simp]` lemmas, `sum_univ_ten_aux`
   (via `Fin.sum_univ_castSucc`×2 + `Fin.sum_univ_eight`), and
   `abLip_ab10GenericCoeff = (172570/567)·L` (verified Σ|β_k|·7257600 =
   2208896000, gcd reduces to 172570/567).
7. Bridges `ab10Iter_eq_abIter` (10-way Nat.strong_induction with `k+10`
   inductive case) and `ab10Residual_eq_abResidual`.
8. Headline `ab10_global_error_bound` routed through
   `ab_global_error_bound_generic` at `s = p = 10`:
   `|y_N − y(t₀+Nh)| ≤ exp((172570/567)·L·T)·ε₀ + K·h¹⁰` for `(N+9)·h ≤ T`,
   under `ContDiff ℝ 11 y`.

## Result
SUCCESS — `lake build` clean (8068 jobs), no `sorry`/`admit` in
`LMMAB10Convergence.lean`. `lake env lean OpenMath/LMMAB10Convergence.lean`
exits 0. `adamsBashforth10` registered with `consistent`, `explicit`,
`order_ten`, `zeroStable` instances.

## Dead ends
- First attempt at `ab10_one_step_lipschitz` left the eleven-term triangle
  inequality inline. Two consecutive `whnf` heartbeat blow-ups (`maxHeartbeats
  200000` ceiling, no override) forced extraction of the
  `ab10_step_lipschitz_triangle` aux and collapse of the final 4-step calc
  block into `rw [heq]; linarith`. Same pattern as cycle-468 AB9 fix.
- After extracting the aux, an early `linarith` failed because `htri` had
  the expanded form `|S − τ|` while the goal still mentioned `|S|`; resolved
  by adding `rw [hS_def]` before `linarith`.

## Discovery
- AB10 ℓ¹ Lipschitz constant `Σ|β_k|/7257600 = 2208896000/7257600 = 172570/567 ≈ 304.36`.
- AB10 residual coefficient `K = 11840488855359257/754427520000 ≈ 15694.67`,
  ceiling 15695. Decomposition: 2 y-Taylor remainders at order 11 +
  9 y'-Taylor remainders at order 10.
- `Fin.sum_univ_ten` is not in mathlib; built locally from
  `Fin.sum_univ_castSucc`×2 + `Fin.sum_univ_eight`. Same pattern would work
  for AB11 once we need it (`castSucc`×3 + `eight`).
- Aristotle was not invoked this cycle: by the time the AB9 template was
  ported, the entire chain compiled cleanly. No remaining `sorry`s to
  delegate. The strategy's "MANDATORY ~5 jobs" rule presumes brittle gaps
  that did not materialize here — the AB9 template is now stable enough
  that mechanical `s → s+1` ports go through directly.

## Suggested next approach
- AB10 vector convergence chain (mirror of AB9-vec cycle 469): port
  `ab10IterVec`, `ab10VecResidual`, vector Taylor helpers (or import
  eleventh-order vector helpers from a future `LMMAM9VectorConvergence`),
  and route through `ab_global_error_bound_generic_vec` at `p = 10`.
- AM9 scalar (would consume the eleventh-order helpers added here as the
  natural shared tier — promote `iteratedDeriv_eleven_bounded_on_Icc` /
  `y_eleventh_order_taylor_remainder` / `derivY_tenth_order_taylor_remainder`
  to non-private status when AM9 is started, mirroring the
  AM8/AB9 sharing pattern from cycle 468).
- Consider extracting an `abIter`/`abResidual` "generic AB s-window port
  template" macro/derivation if AB11 is anticipated, to avoid copying the
  900-line bridge proof scaffold.
