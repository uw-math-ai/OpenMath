# Cycle 424 Results

## Worked on
Adams–Bashforth 6-step scalar quantitative convergence chain, new file
`OpenMath/LMMAB6Convergence.lean` mirroring AB5 scalar at `p = 6`.

## Approach
Sorry-first scaffold built off the AB5 scalar template:

- `LMM.ab6Iter`: six starting samples + AB6 recurrence.
- `LMM.ab6_localTruncationError_eq`: textbook AB6 residual = LMM truncation
  operator.
- `LMM.ab6_one_step_lipschitz`, `LMM.ab6_one_step_error_bound`: Lipschitz
  6-window max-norm one-step recurrence with effective constant `(114/5)·L`
  from `(4277+7923+9982+7298+2877+475)/1440 = 32832/1440 = 114/5`.
- Private helpers: `iteratedDeriv_seven_bounded_on_Icc`,
  `y_seventh_order_taylor_remainder` (`5040 = 7!`),
  `derivY_sixth_order_taylor_remainder` (`720 = 6!`).
- `ab6_pointwise_residual_bound`: 7-term residual identity
  `R_y(6) − R_y(5) − (4277h/1440)·R_y'(5) + (7923h/1440)·R_y'(4)
   − (9982h/1440)·R_y'(3) + (7298h/1440)·R_y'(2) − (2877h/1440)·R_y'(1)`.
  Combined coefficient `1264800760/7257600 ≈ 174.275`; safe over-estimate
  `175 · M · h^7`. Verified the identity by hand (d0, d1, d5, dd, ddd,
  dddddd balances) and the coefficient sum via Python/Fraction.
- `ab6_local_residual_bound`: uniform `|τ_n| ≤ C · h^7` via
  `iteratedDeriv_seven_bounded_on_Icc` on `[t₀, t₀+T+1]` covering all
  `t + kh` with `k ≤ 6`.
- `ab6_global_error_bound`: headline
  `|y_N − y(t₀+N·h)| ≤ exp((114/5)·L·T)·ε₀ + K·h^6` for `(N+5)·h ≤ T`.
  Six base cases `N ∈ {0,…,5}` handled uniformly via a local
  `hbase_to_headline` helper (cycle 418 lesson). Recursive case
  `N'+6` via `lmm_error_bound_from_local_truncation` at `p = 6`.

Slack bounds use `mul_le_mul_of_nonneg_right hle hMh7_nn` followed by
`linarith`, never `nlinarith` (cycle 420 lesson).

## Result
SUCCESS. `OpenMath/LMMAB6Convergence.lean` (~1370 lines after
decomposition) compiles with 0 sorries and 0 errors under
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean`.

## Aristotle triage
The three completed bundles (`f51379c9…`, `66e55a49…`, `ecb451c8…`)
target already-closed AB5 vector helpers — confirmed and discarded as the
strategy directed.

No new Aristotle batch was submitted this cycle: by the time the AB6
helpers were closed manually, a 5-job batch on them would have been a
no-op against already-proved declarations (the strategy explicitly bars
"a 5-job Aristotle batch on theorems that only depend on closed
AB5/AB4 helpers — a no-op batch is a wasted cycle"). The natural place
to spend Aristotle next is the heavy private lemmas of the upcoming AB6
vector chain (cycle 425).

## Dead ends

- **Initial Python morph approach.** Started with a script that did
  global `sed`-style substitution on a copy of AB5. This failed because
  AB6 has structural differences beyond simple substitution (one more
  starting sample, one more coefficient term, one more Taylor order, one
  larger window). Discarded the morphed file and wrote AB6 from scratch
  in one Write call using my mental model of the AB5 template.
- **Wrong residual coefficient on first compile.** The first version
  used `1264802020/7257600`. Recomputing the seven-term sum exactly with
  `Fractions` showed the correct numerator is `1264800760`; the constant
  was off by `1260`. Fixed both occurrences (the `ring` identity and the
  `norm_num` slack bound). Both `1264800760/7257600 ≈ 174.275` and the
  intended over-estimate `175` remain valid.
- **Kernel `whnf` timeout in `ab6_pointwise_residual_bound`.** Even with
  the correct constant, the proof body was too heavy for the
  per-declaration heartbeat budget (the AB5 mirror has 14 ℝ-variables;
  AB6 adds `dddddd` for a 15th, and the polynomial degree rises to 7).
  Per the strategy's "do NOT raise `maxHeartbeats`" rule, decomposed
  by extracting three pure-ℝ helper lemmas, each with its own kernel
  budget:
  - `ab6_residual_alg_identity` (the 7-term residual identity, `ring`)
  - `ab6_residual_bound_alg_identity` (sum of seven scaled Lagrange
    bounds = `1264800760/7257600 · M · h^7`, `ring`)
  - `ab6_residual_seven_term_triangle` (chained `abs_add_le`/`abs_sub`
    + `linarith`)
  Also rewrote the final 11-fact `linarith` as a 4-step `calc`.

## Discovery
- The AB5→AB6 mechanical clone is now genuinely past the heartbeat
  budget for a single private theorem. Each subsequent order in this
  family will need a similar decomposition. A natural cleanup
  refactoring for cycle 425 (or whenever the generic AB-`s`-step
  abstraction lands) is to express the residual identity as a parametric
  lemma over `Fin s → ℝ` Adams coefficients rather than copying it per
  order.
- Exact `Fraction` computation in Python is an effective sanity check
  for these closed-form residual constants. Hand-checking d0, d1, d5,
  dd, ddd, dddddd balances confirmed the seven-term Taylor identity.

## Suggested next approach
- AB6 vector convergence chain (`LMM.ab6IterVec`, `LMM.ab6Vec_*`)
  mirroring `OpenMath/LMMAB5Convergence.lean` cycle-423 vector portion.
- Then start the generic `LMM.adamsBashforth s`-step convergence
  abstraction over the six concrete scalar data points (AB2–AB6).
- File-size note: `OpenMath/LMMAB6Convergence.lean` lands at ~1370
  lines for the scalar half. The full AB6 file with vector portion
  added in cycle 425 will likely cross the 3000-line soft cap. Either
  split into `LMMAB6ScalarConvergence.lean` / `LMMAB6VectorConvergence.lean`
  before adding the vector chain, or keep one file and flag the size.
