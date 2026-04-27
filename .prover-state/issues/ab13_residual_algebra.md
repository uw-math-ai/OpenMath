# Issue: AB13 14-witness packed-polynomial residual algebra and headline

## Blocker

`OpenMath/LMMAB13Convergence.lean` (created in cycle 486) currently
ships with two `sorry`s:

- `LMM.ab13_pointwise_residual_bound` — the AB13 14th-order pointwise
  residual bound `|τ_n| ≤ 529729 · M · h^14`.
- `LMM.ab13_global_error_bound` — the headline global error bound
  routed through `ab_global_error_bound_generic` at `s = p = 13`.

Both depend on a 14-witness packed-polynomial residual identity that
mirrors `LMM.ab12_residual_alg_identity` (in
`OpenMath/LMMAB12Convergence.lean`) but at one greater width. The
remainder of the AB13 chain — `adamsBashforth13` itself plus
`adamsBashforth13_consistent`, `_explicit`, `_order_thirteen`,
`_zeroStable`; the generic coefficient bridge
(`ab13GenericCoeff`, `abLip_ab13GenericCoeff = (1439788039057/638512875) · L`,
`ab13Iter`, the twelve `ab13Iter_zero..twelve` simp lemmas,
`ab13Iter_succ_thirteen`, `ab13_localTruncationError_eq`,
`ab13Residual_eq_abResidual`, `ab13Iter_eq_abIter`); and the one-step
recurrences (`ab13_one_step_lipschitz`,
`ab13_one_step_error_bound`) — are all closed in the file.

## Context

The slack constant is the integer

```
529729 = ⌈ 5616577262114645115720677 / 10602754543180800000 ⌉
       ≈ 529728.12
```

verified via exact `Fraction` arithmetic in `/tmp/ab13_slack.py` (cycle
486). The growth constant for the 13-window max-norm Lipschitz
recurrence is `Σ|β_k| · L = (1439788039057 / 638512875) · L`, also
verified by exact arithmetic and proven inside the live file.

The numeric coefficients of `adamsBashforth13.β`, ordered from
`f_n` through `f_{n+12}`, are

```
( 703604254357,  -9160551085734,   55060974662412,  -202322913738370,
  507140369728425, -915883387152444, 1226443086129408, -1233589244941764,
  932884546055895, -524924579905150,  214696591002612,  -61497552797274,
  13064406523627 ) / 2615348736000
```

with `2615348736000 = 420 · 13!`. Σβ = 1 was verified.

## What was tried

In cycle 486 we generated `LMMAB13Convergence.lean` (~426 lines) by
mirroring `LMMAB12Convergence.lean` at width `s = 13`. The file
imports the public 14th-order scalar Taylor helpers
(`y_fourteenth_order_taylor_remainder`,
`derivY_thirteenth_order_taylor_remainder`,
`iteratedDeriv_fourteen_bounded_on_Icc`) from
`OpenMath/LMMAM12Convergence.lean`, so no duplication is needed
upstream.

The following AB12 cycle-479 / AB12-vector cycle-483 lessons must be
respected when finishing this work:

- Use packed-polynomial helpers (`ab13_yPoly14` / `ab13_dPoly13`) in
  the residual algebraic identity. **Do not** inline the 14-witness
  Taylor expansions in each hypothesis (cycles 480 / 482 / 483 / 484
  blew the 200K heartbeat ceiling that way).
- Use `subst` of every hypothesis followed by `module` (with
  `norm_num` *before* `module` for the coefficient bridge). **Do
  not** use `match_scalars <;> ring` or structural `rfl`
  decomposition (cycles 476 / 480 failed).
- Do not mechanically `sed`-rewrite the AB12 file in place (cycles
  424 / 480 left wrong coefficients and wrong window sizes when this
  was attempted). Recompute every numerical witness when extending.
- Strip dead `_nn` linarith lines in giant residual contexts
  (cycle 444 lesson — `whnf` budget timeouts at AM7+ with 27+ set
  bindings).
- Do not raise `maxHeartbeats` above 200000.

The cycle 486 main session was tight on time after the AB13 method
registration and convergence file scaffolding (with full coefficient
verification via Lagrange-and-integrate Python script). One Aristotle
job (`9340dd8c-5b03-4d09-b869-aac813484352`) was submitted with the
live `LMMAB13Convergence.lean` and asked to fill the two sorries; if
it returns COMPLETE that proof can be transplanted directly. If it
returns COMPLETE_WITH_ERRORS, a manual finish is still required.

## Possible solutions

The fastest manual path mirrors `LMMAB12Convergence.lean` at one
greater width:

1. Extract `ab13_residual_alg_identity` taking 14 witnesses
   `A, B, C, D, E, F, G, H, I, J, K, L, M, N` (vs. AB12's 13). Use
   `subst hA … hN; ring` (or `module` if `ring` doesn't close it
   inside 200K heartbeats).
2. Extract `ab13_residual_bound_alg_identity` (pure ring identity:
   the slack rational sum equals `5616577262114645115720677 /
   10602754543180800000 · Mb · h^14`).
3. Extract `ab13_residual_triangle_aux` and
   `ab13_residual_fourteen_term_triangle` (14-term triangle
   inequality reducing absolute-value witness sum).
4. Extract `ab13_residual_combine_aux` parameterized over the 14
   abstract Taylor remainders.
5. Build `ab13_pointwise_residual_bound` using 14 Taylor remainder
   applications (`y_fourteenth_order_taylor_remainder` for the two
   `y(t+13h)` / `y(t+12h)` witnesses, and
   `derivY_thirteenth_order_taylor_remainder` for the twelve
   `deriv y (t+kh)` witnesses, k = 1..12), then `clear_value` over
   the 27 set bindings before invoking the algebraic identity.
6. Build `ab13_local_residual_bound` (already mostly written in the
   live file with a `by sorry` only in the inner application).
7. Build `ab13_global_error_bound` mirroring `ab12_global_error_bound`
   step-for-step, with 13 `hiterk` simp lemmas (k = 0..12) and 13
   start-error hypotheses.

Estimated implementation: ~700 additional lines, ~1 cycle of
careful work mirroring AB12's structure with width-13 expansions.

## References

- Live file: `OpenMath/LMMAB13Convergence.lean` (cycle 486)
- Method definitions: `OpenMath/AdamsMethods.lean` (cycle 486)
- Template: `OpenMath/LMMAB12Convergence.lean` (cycle 479)
- 14th-order Taylor helpers: `OpenMath/LMMAM12Convergence.lean`
  (cycle 484)
- Strategy: `.prover-state/strategy.md` (cycle 486)
- Aristotle job: `9340dd8c-5b03-4d09-b869-aac813484352`
