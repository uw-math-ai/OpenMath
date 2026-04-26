# Cycle 442 Results

## Worked on
Created `OpenMath/LMMAM6Convergence.lean` — the Adams–Moulton 6-step
scalar quantitative convergence chain (~1587 lines), one stencil step up
from `LMMAM5Convergence.lean` (cycle 437). AM6 is the implicit
order-7 LMM with weights `[-863, 6312, -20211, 37504, -46461, 65112,
19087]/60480` and error constant `-275/24192`; the chain culminates in a
discrete-Gronwall global error bound

  `|y_n - y(t_0 + n·h)| ≤ exp(7L·T)·(starting error + 8·89·M·h^7)`

assembled via `lmm_error_bound_from_local_truncation` at `p = 7`.

## Approach
Sorry-first scaffold mirroring the AM5 file, scaled up by one degree
everywhere. Key blocks:

- Three private Taylor helpers added inline:
  `iteratedDeriv_eight_bounded_on_Icc`,
  `y_eighth_order_taylor_remainder` (Lagrange remainder at `n := 7` with
  `8! = 40320`), and `derivY_seventh_order_taylor_remainder` (`n := 6`
  on `deriv y` which is `ContDiff ℝ 7`).
- `IsAM6Trajectory` predicate carrying the six-step recurrence.
- `am6_localTruncationError_eq` (closed by
  `unfold; simp [Fin.sum_univ_succ, …]; ring`).
- `am6_one_step_lipschitz` — explicit eight-term abs decomposition with
  the implicit `(1 - (19087/60480)·hL)` factor on the LHS and seven
  Lipschitz scaled bounds on the RHS, plus `|τ|`.
- `am6_one_step_error_bound` — divides by the implicit factor and
  slackens to the strategy-mandated `(1 + h·(7L))` rolling-max growth
  with a `2·|τ|` residual term. The key inequality

    `1 + (176463/60480)·hL ≤ (1 - (19087/60480)·hL)·(1 + 7·hL)`

  closed by an explicit factorisation
  `(hL/60480)·(227810 - 133609·hL) ≥ 0` after `nlinarith` timed out.
- `am6_one_step_error_pair_bound` — 6-window rolling-max recurrence on
  `(en, en1, …, en5)` for the Gronwall stage.
- Three private algebra helpers: `am6_residual_alg_identity`,
  `am6_residual_bound_alg_identity` (sum equals
  `(1121952791/12700800)·M·h^8`, slackened to `89`), and
  `am6_residual_eight_term_triangle` (eight-term triangle inequality).
- Added a fourth helper `am6_residual_combine` mid-cycle to break a
  kernel `whnf` timeout in `am6_pointwise_residual_bound` — see below.
- `am6_pointwise_residual_bound`, `am6_local_residual_bound`, and the
  `am6_global_error_bound` Gronwall-assembly with side condition
  `((N : ℝ) + 5)·h ≤ T` and six base cases (N = 0..5) before the
  inductive `N' + 6` step.

## Result
SUCCESS — `lake env lean OpenMath/LMMAM6Convergence.lean` produces
0 errors and 0 warnings. The full quantitative chain is closed without
sorries.

## Dead ends
- `nlinarith [hx_nn, hx_small, hsmall]` could not discharge the key
  algebraic step
  `1 + (176463/60480)·hL ≤ (1 - (19087/60480)·hL)·(1 + 7·hL)` within
  the heartbeat budget. Replaced with an explicit factoring
  `(hL/60480)·(227810 - 133609·hL) ≥ 0` plus `linarith`.
- `nlinarith [hsmall]` likewise timed out on the trivial linear
  `1 ≤ (1 - (19087/60480)·hL)·2`. Replaced with plain `linarith`.
- `linarith [this]` on
  `(1121952791/12700800)·M·h^8 ≤ 89·M·h^8` triggered an `isDefEq`
  timeout because `mul_le_mul_of_nonneg_right` returned the inequality
  with `M·h^8` parenthesised differently from the goal. Fixed by
  inserting explicit `ring`-rewrites of both sides into
  `89 * (M * h^8)` form.
- The most stubborn issue: `am6_pointwise_residual_bound` hit a
  kernel-level `whnf` timeout at the theorem boundary (status `[error]
  (deterministic) timeout at `whnf``) even after each tactic elaborated
  cleanly. Root cause: the proof term combining 8 `set`-bindings, 8 abs
  bounds, the triangle inequality, the algebraic-equality bridge, and
  the slack in a single trailing `linarith` produced a kernel-check
  payload too large for the heartbeat budget (the AM5 analog with 7
  bindings stays under the limit). Resolved by extracting an
  `am6_residual_combine` private helper that takes A,…,H and the bounds
  as plain variables and folds the triangle-plus-bounds-plus-slack
  reasoning in isolation, leaving the main theorem to call the helper
  with the eight `set`-aliased subterms.

## Discovery
- The AM5 → AM6 step is qualitatively a kernel-cost step, not an
  elaboration-cost step. `linarith`/`nlinarith` proofs that produce
  small certificates work at AM5 (7 vars, degree ≤ 7) but the same
  shape at AM6 (8 vars, degree ≤ 8) generates a kernel proof term that
  the 200000-heartbeat checker cannot verify. The fix pattern that
  generalises: extract the bound-combination tactic into a dedicated
  private lemma whose hypotheses are pure variables, so the kernel
  checks the heavy `linarith` term once in a small context rather than
  inside the giant 8-`set` ambient context of the main residual bound.
- The AM5 file inlines its triangle inequality directly; AM6 needed it
  factored. As we move to AM7+/AB7+ the pattern of extracting
  triangle/combination helpers will become mandatory rather than
  optional.

## Suggested next approach
- Cycle 443 (per strategy): vector AM6 quantitative convergence chain
  in `OpenMath/LMMVecAM6Convergence.lean`, lifting the scalar chain
  through `IsAM6VectorTrajectory` and the existing vector LMM
  Gronwall infrastructure (mirroring AM5 → vec-AM5).
- Cycle 444+: AM7-step scalar convergence is the natural escalation.
  Order-8 method, weights with denominator `120960`, error constant
  `19087/89600`, eighth-degree residual sum slackened to a comparable
  ~100·M·h^9 bound. The kernel-cost pattern observed here will recur;
  plan to extract the triangle and combine helpers from the start.
- Promote `iteratedDeriv_eight_bounded_on_Icc` and the eighth/seventh
  order Taylor helpers from `private` in this file to a public
  `OpenMath/TaylorRemainders.lean` module if/when AM7 reuses them.
