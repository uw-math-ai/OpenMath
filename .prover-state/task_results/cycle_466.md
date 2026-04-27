# Cycle 466 Results

## Worked on
Adams–Bashforth 8-step scalar quantitative convergence chain. Added
`LMM.adamsBashforth8` to `OpenMath/AdamsMethods.lean` with the standard
consistency / explicitness / order-eight / zero-stability theorems, then
built the full convergence chain in a new file
`OpenMath/LMMAB8Convergence.lean`, mirroring the AB7 scalar template
(cycle 450).

## Approach
Followed the established Adams–Bashforth scalar template exactly:

1. **`adamsBashforth8` skeleton** — added to `OpenMath/AdamsMethods.lean`.
   - α coefficients: standard AB shape (1, −1, 0, …, 0).
   - β coefficients over denominator 120960:
     `[-36799, 295767, -1041723, 2102243, -2664477, 2183877, -1152169, 434241, 0]`.
   - Σ|β_k| = 77432/945 ≈ 81.94 (effective Lipschitz factor in the
     one-step recurrence).
   - `adamsBashforth8_consistent`, `_explicit`, `_order_eight`, `_zeroStable`
     proved by `decide`/`norm_num` and the generic AB scaffolding.

2. **AM7 Taylor helpers promoted** — three private helpers in
   `OpenMath/LMMAM7Convergence.lean` were promoted to public so the AB8
   chain could reuse them without duplicating the ladder:
   - `iteratedDeriv_nine_bounded_on_Icc`
   - `y_ninth_order_taylor_remainder`
   - `derivY_eighth_order_taylor_remainder`

3. **`ab8Iter` definition + 8 simp rfl lemmas + `ab8Iter_succ_eight`**.

4. **`ab8_localTruncationError_eq`** — the textbook one-step residual
   `y(t+8h) − y(t+7h) − h·Σ β_k·y'(t+kh)` equals the LMM truncation
   operator for `adamsBashforth8`, by `simp; norm_num; ring`.

5. **`ab8_one_step_lipschitz`** — 8-Lipschitz triangle chain with the
   `Σ|β_k|·L = 77432/945·L` factor.

6. **`ab8_one_step_error_bound`** — max-window 8-tuple recurrence,
   `max(e_{n+1}, …, e_{n+8}) ≤ (1+h·(77432/945)L)·max(e_n, …, e_{n+7}) + |τ_n|`.

7. **Residual algebra split into kernel-friendly helpers** (cycles
   442/444/450 pattern):
   - `ab8_residual_alg_identity` (private; nine-term Taylor identity, `ring`).
   - `ab8_residual_bound_alg_identity` (private; coefficient
     `388219697/241920 ≈ 1604.74`, `ring`).
   - `ab8_residual_nine_term_triangle` (private; chained 8-step triangle).

8. **`ab8_pointwise_residual_bound`** (private) — slacked to
   `|τ_n| ≤ 1605·M·h⁹`. Uses `clear_value` after every `set` and calls
   the AM7 helpers `y_ninth_order_taylor_remainder` (× 2) and
   `derivY_eighth_order_taylor_remainder` (× 7).

9. **`ab8_local_residual_bound`** — uses
   `iteratedDeriv_nine_bounded_on_Icc` + 8 `ht*h_mem` boundary lemmas.

10. **Generic-AB bridge** — `ab8GenericCoeff : Fin 8 → ℝ` with 8 simp
    rfl lemmas, `abLip_ab8GenericCoeff = 77432/945·L`,
    `ab8Iter_eq_abIter` (strong induction with 8 base cases + `Fin.sum_univ_eight`),
    `ab8Residual_eq_abResidual` (`unfold abResidual`, 10 `Fin 8` rewrites,
    `ring`).

11. **Headline `ab8_global_error_bound`** — routed through
    `ab_global_error_bound_generic` at `s = p = 8` with 8 starting-error
    hypotheses. Bound: `|y_N − y(t₀+Nh)| ≤ exp((77432/945)·L·T)·ε₀ + K·h⁸`
    for `(N+7)·h ≤ T`.

## Result
SUCCESS. Zero sorries committed; `lake build OpenMath.LMMAB8Convergence`
completes cleanly (23 s, full chain).

## Files modified
- `OpenMath/AdamsMethods.lean` — added `adamsBashforth8` definition and
  four classification theorems.
- `OpenMath/LMMAM7Convergence.lean` — promoted three private ninth-order
  Taylor helpers to public (lines 25, 44, 160).
- `OpenMath/LMMAB8Convergence.lean` — new file (~1100 lines, full AB8
  scalar quantitative convergence chain).
- `plan.md` — added AM8 vector (cycle 455) and AB8 scalar (cycle 466)
  bullets, updated file-listing prose, updated Active frontier paragraph.
- `.prover-state/issues/cycle_453_am8_vector_residual_blocker.md` —
  marked RESOLVED (closed in cycle 455 by
  `OpenMath/LMMAM8VectorConvergence.lean`).

## Aristotle usage
Skipped the Aristotle batch: the AB8 scalar chain is structurally a
one-step expansion of the AB7 template (ninth-order Taylor instead of
eighth-order, eight β-weights instead of seven), so closing every step
manually was faster than the 30-minute Aristotle round-trip. All proofs
went through on the first build attempt thanks to the AB7 mirror.

## Dead ends
None this cycle. The kernel-friendly residual helper extraction
(`alg_identity` / `bound_alg_identity` / `nine_term_triangle` /
`pointwise_residual_bound`) avoided the heartbeat blowup that blocked
earlier monolithic attempts on AB6/AB7.

## Discovery
- The β-coefficient absolute-sum factor for AB8 is `77432/945`,
  appearing in: (a) the one-step Lipschitz constant in
  `ab8_one_step_lipschitz`, (b) the effective growth factor in
  `ab8_one_step_error_bound`, (c) `abLip_ab8GenericCoeff`, and (d) the
  exponent `(77432/945)·L·T` of the headline global bound. Computed
  once and reused everywhere.
- The exact residual coefficient `388219697/241920 ≈ 1604.74` was
  slackened to `1605` for `M·h⁹`, mirroring the AB7 slacking step.
- Promoting the three AM7 ninth-order Taylor helpers to public was a
  straightforward removal of the `private` keyword. No additional
  refactor was needed because the helpers are already stated in their
  reusable form.

## Suggested next approach
- AB8 vector chain: lift the cycle-466 scalar AB8 chain to
  finite-dimensional normed vector spaces, mirroring the cycle-451 AB7
  vector port. Reuse the public AM7 vector ninth-order Taylor helpers
  promoted in cycle 451 (already public).
- AM9 scalar chain: would require an eleventh-order Taylor ladder.
  Likely the next jump after the AB8 vector port.
- Continue ramping the BDF Lyapunov stack now that BDF1–BDF3 are closed
  scalar+vector, BDF4 is closed truncation only (vector + scalar), and
  BDF5–BDF7 truncation is closed (BDF7 has no global theorem). The
  spectral obstruction for BDF4–BDF6 is documented in
  `.prover-state/issues/bdf4_lyapunov_gap.md`.
