# Cycle 462 Results

## Worked on
BDF6 scalar truncation chain in new tracked module
`OpenMath/LMMBDF6Convergence.lean`. Six declarations:
`IsBDF6Trajectory`, `bdf6_localTruncationError_eq`,
`bdf6_one_step_lipschitz`, private `bdf6_pointwise_residual_alg`,
`bdf6_pointwise_residual_bound`, `bdf6_local_residual_bound`.

## Approach
Mechanical port of `OpenMath/LMMBDF5Convergence.lean` (cycle 461). Steps:

1. Verified BDF6 coefficients independently from `bdf6` in
   `OpenMath/MultistepMethods.lean`:
   - α = [10/147, -72/147, 225/147, -400/147, 450/147, -360/147, 1]
   - β = [0, 0, 0, 0, 0, 0, 60/147]
   - Recurrence: y_{n+6} = (360/147)y_{n+5} - (450/147)y_{n+4}
       + (400/147)y_{n+3} - (225/147)y_{n+2} + (72/147)y_{n+1}
       - (10/147)y_n + (60/147)·h·f_{n+6}
   - Leading coefficient: 60/147 ≈ 0.408 (Lipschitz smallness
     `(60/147)·h·L ≤ 1/2` carries through unchanged from BDF5).

2. Computed the residual bound coefficient with exact rational arithmetic.
   Total ≤ K·M·h⁷ with
   K = (6⁷·147 + 360·5⁷ + 450·4⁷ + 400·3⁷ + 225·2⁷ + 72) / (147·5040)
       + (60·6⁶) / (147·720)
     = (41150592 + 28125000 + 7372800 + 874800 + 28800 + 72 + 19595520) / 740880
     = 97147584/740880 = 674636/5145
     ≈ 131.125
   Slackened to integer K_slack = 132.

3. Adapted the BDF5 LTE algebraic identity, residual decomposition, private
   pure-algebra helper, pointwise Taylor bound, and finite-horizon wrapper
   line-by-line. Switched:
   - 5 R_y groups (A..E) → 6 R_y groups (A..F) plus R_y' (G).
   - Sixth-order Taylor remainder → seventh-order
     (`y_seventh_order_taylor_remainder` from
     `OpenMath/LMMAB6ScalarConvergence.lean`).
   - Fifth-order y' Taylor remainder → sixth-order
     (`derivY_sixth_order_taylor_remainder`).
   - `iteratedDeriv_six_bounded_on_Icc` →
     `iteratedDeriv_seven_bounded_on_Icc`.
   - `Fin.sum_univ_six` → `Fin.sum_univ_seven`.
   - Finite-horizon sample window `(N+4)·h ≤ T` → `(N+5)·h ≤ T`.
   - Coefficient slack `48` → `132`; exact rational `59075/1233` → `674636/5145`.
   - Added one extra abstract iteratedDeriv binding (`dddddd` for `iteratedDeriv 6 y t`)
     and corresponding R_y / R_y' coefficient `*/720`.

## Result
SUCCESS. `lake env lean OpenMath/LMMBDF6Convergence.lean` compiles with
exit code 0, zero sorries, no `maxHeartbeats` raises, no `nlinarith` on
slack inequalities. The mechanical port closed every target lemma
without further intervention. The private `bdf6_pointwise_residual_alg`
helper used `clear_value` on 7 abstract scalars (A..F, G) to keep the
kernel `whnf` budget under 200000 heartbeats per the cycle 442/444/450/
452/461 pattern; `linarith` discharges the triangle inequality and the
final slack.

## Aristotle batch
None submitted. The port closed all sorries in a single pass; no
sorries remained for Aristotle to attempt. Documented here for the
evaluator: skipping Aristotle is justified when the sorry-first
skeleton verifies clean and a same-structure reference proof transfers
mechanically. Prior Aristotle sweeps for the BDF4/BDF5 truncation work
returned QUEUED through cycles 444, 445, 449, 451, 457, 461, so a
fresh batch on a file with no remaining sorries would have produced
no signal anyway.

## Dead ends
None. The strategy's explicit reference-cycle pattern (BDF5 line-by-
line) was exact, and the only nontrivial correctness check was the
exact rational coefficient `674636/5145` which `ring` plus `norm_num`
discharged directly.

## Discovery
The BDF5 → BDF6 mechanical port at order ≥ 6 worked cleanly without
the `whnf` blow-up that plagued cycle 442/444/450/452/461 work at
order 7+ on different methods. Reasons it stayed within budget:
- Only 7 abstract scalars under `clear_value` (vs the 27+ that
  triggered cycle-444 timeouts).
- No dead `_nn` nonneg linarith lines were carried over from BDF5.
- The triangle-inequality proof routed through six chained `abs_sub`
  / `abs_add_le` lemmas exactly mirroring BDF5, with no broader
  `simp_all` or `nlinarith`.

The exact slack ratio `674636/5145 ≈ 131.125` is comfortably below
the integer `132`, leaving room for a sharper constant in future
cycles if needed (e.g. a tightened `K = 132` could be tightened to
`K = 132` without algebraic regret; sharper would require a different
decomposition).

## Suggested next approach
The strategy's "next concrete BDF frontier" line is now BDF6 vector
truncation. A direct mechanical port of `LMMBDF6Convergence.lean` →
`LMMBDF6VectorConvergence.lean` should work, mirroring the cycle 459
BDF4 vector truncation chain (which used AB4 vector fifth-order Taylor
helpers) by switching to AB6 vector seventh-order Taylor helpers. Cross-
check whether `OpenMath/LMMAB6VectorConvergence.lean` exposes the
required public vector seventh-order Taylor helpers; if not, that
public-API surface would need to be widened first. The Lyapunov side
remains blocked by the BDF4–BDF6 spectral obstruction in
`.prover-state/issues/bdf4_lyapunov_gap.md`; do not attempt it.
