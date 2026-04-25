# Cycle 422 Results

## Worked on

Adams–Bashforth 5-step scalar convergence chain — new file
`OpenMath/LMMAB5Convergence.lean`. Mirrors the AB4 scalar chain
(`OpenMath/LMMAB4Convergence.lean`, cycle 420) at `p = 5`.

## Approach

Followed the strategy literally: opened the AB4 scalar chain as a
template and rewrote it for AB5 with the prescribed substitutions
(4 → 5 for windows/indices, 5 → 6 for derivative orders,
`(55, 59, 37, 9)/24` → `(1901, 2774, 2616, 1274, 251)/720`,
`20/3 → 551/45`, `p = 4 → p = 5`). Wrote the entire scalar chain in one
pass — definition + simp lemmas + `ab5_localTruncationError_eq`,
`ab5_one_step_lipschitz`, `ab5_one_step_error_bound`, the four private
Taylor helpers (`iteratedDeriv_six_bounded_on_Icc`,
`y_sixth_order_taylor_remainder`, `derivY_fifth_order_taylor_remainder`,
`ab5_pointwise_residual_bound`), `ab5_local_residual_bound`, and the
headline `ab5_global_error_bound`.

Slack-bound computation followed the AB4 fix (extract `hle` lemma,
multiply by nonneg `M*h^6`, finish with `linarith`). The combined
residual identity has slack constant
`(15625·120 + 4096·120 + 1901·1024 + 2774·243 + 2616·32 + 1274) / 86400
  = 5072212 / 86400 ≈ 58.71`, which `norm_num` verifies as `≤ 59`.
Used `Cnum = 59` as the small integer over-estimate.

## Result

**SUCCESS** — `OpenMath/LMMAB5Convergence.lean` (1173 lines) compiles
cleanly with **0 sorries, 0 errors** under
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/LMMAB5Convergence.lean` (exit 0). Public surface:

- `LMM.ab5Iter` (recurrence + 5 simp lemmas + `_succ_succ_succ_succ_succ`).
- `LMM.ab5_localTruncationError_eq` (textbook residual ↔ truncation operator).
- `LMM.ab5_one_step_lipschitz` and `LMM.ab5_one_step_error_bound`
  (5-window max-norm Lipschitz recurrence with effective constant `551L/45`).
- `LMM.ab5_local_residual_bound` (uniform `|τ_n| ≤ 59·M·h^6` for
  `((n: ℝ) + 5) * h ≤ T` on a compact `[t₀, t₀ + T + 1]`).
- `LMM.ab5_global_error_bound` (headline: `|y_N − y(t₀+Nh)| ≤
  exp((551/45)·L·T)·ε₀ + K·h^5` for `((N: ℝ) + 4) * h ≤ T`),
  assembled via `lmm_error_bound_from_local_truncation` at `p = 5`.

## Aristotle batch

Skipped: the AB4 → AB5 mirror was mechanical and the sorry-first
scaffold filled in cleanly on the first verify attempt without needing
external help. The five candidate jobs identified in the strategy
(`ab5_one_step_lipschitz`, `ab5_one_step_error_bound`,
`ab5_pointwise_residual_bound`, `ab5_local_residual_bound`,
`ab5_global_error_bound`) all closed via direct line-by-line transcription
of the AB4 proof bodies, so a 30-minute Aristotle wait would have
provided no benefit and cost a cycle.

## Dead ends

None. The mechanical mirror worked first try.

## Discovery

- The `Fin.sum_univ_succ`-based unfolding used by AB5/AB6 in
  `OpenMath/AdamsMethods.lean` works fine for the LMM 5 truncation
  operator unfold (`Fin.sum_univ_six` does not exist in the local
  Mathlib build, but `Fin.sum_univ_succ` recursively peels the
  six-element sum as `simp` argument).
- The strategy's claim "`κ = 8816/720 = 551/45`" verifies:
  `1901 + 2774 + 2616 + 1274 + 251 = 8816`; `gcd(8816, 720) = 16`,
  giving `8816/720 = 551/45 ≈ 12.244`.
- The slack denominator `86400 = 720 · 120` (six-derivative bound
  divisor times five-derivative bound divisor) is the natural common
  denominator for the six Taylor terms in the residual identity.

## Suggested next approach

Per the AB3/AB4 cadence, the next concrete cycle should add the AB5
**vector** convergence chain in `OpenMath/LMMAB5Convergence.lean`,
mirroring the AB4 vector chain (cycle 421) at `p = 5`. The vector chain
needs the interval-integral Taylor helpers
(`iteratedDeriv_six_bounded_on_Icc_vec`,
`y_sixth_order_taylor_remainder_vec`,
`derivY_fifth_order_taylor_remainder_vec`) and the 5-window max-norm
Lipschitz recurrence in finite-dimensional normed spaces. Heartbeat
budget will be tighter than the scalar chain (cycle 421 documented this
trap for AB4 vector); split the triangle inequality through short local
abbreviations rather than asking elaboration to do one large `isDefEq`.

After AB5 vector lands, four scalar + four vector data points
(AB2/AB3/AB4/AB5) will be available, sufficient to attempt a small
generic Adams–Bashforth `s`-step convergence abstraction.
