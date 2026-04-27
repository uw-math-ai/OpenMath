# Cycle 464 Results

## Worked on

BDF7 scalar local truncation chain. Created
`OpenMath/LMMBDF7Convergence.lean` containing:

- `LMM.IsBDF7Trajectory` — supplied implicit trajectory predicate with the
  7-step BDF recurrence and leading factor `420/1089`.
- `LMM.bdf7_localTruncationError_eq` — textbook 7-step residual reduction.
- `LMM.bdf7_one_step_lipschitz` — defect estimate
  `|defect| ≤ (420/1089)·h·L·|e_{n+7}| + |τ_n|`.
- private `LMM.bdf7_pointwise_residual_alg` — pure-algebra abstract bound on
  eight scalars (seven `R_y(k)` and one `R_y'(7)`).
- `LMM.bdf7_pointwise_residual_bound` — `|τ| ≤ 366·M·h⁸` using the public
  AM6-scalar 8th-order Taylor helpers
  (`y_eighth_order_taylor_remainder`,
  `derivY_seventh_order_taylor_remainder`).
- `LMM.bdf7_local_residual_bound` — uniform `O(h⁸)` bound on a finite
  horizon (`(n + 7) * h ≤ T`).

Reused public helpers from `OpenMath/LMMAM6Convergence.lean`
(`iteratedDeriv_eight_bounded_on_Icc`, `y_eighth_order_taylor_remainder`,
`derivY_seventh_order_taylor_remainder`); no duplication.

## Approach

Mirrored `OpenMath/LMMBDF6Convergence.lean` end-to-end with one extra sample
window (`yn7`/`tn7`/`zn7`), one extra Taylor remainder (`R_y(7)`), one extra
α-coefficient block, and the new leading constant `420/1089`. Re-typed each
block fresh (no sed-style port). The pure-algebra core uses `clear_value`
after the eight `set` bindings and routes the eight individual triangle
inequalities through `linarith`, with the abstract coefficient sum closed by
`ring`. The abs-bound is closed by a single `linarith` against the hypothesis
list plus the `ring`-verified equality `(7^8/40320 + (2940/1089)·6^8/40320 +
… + (420/1089)·7^7/5040) · M · h⁸ = (17914498/49005)·M·h⁸`, slacked to
`366·M·h⁸`.

Used `Fin.sum_univ_eight` (which exists in Mathlib via
`Mathlib/NumberTheory/GaussSum.lean` usage) for the LTE unfolding, plus
`iteratedDeriv_one`, `iteratedDeriv_zero`, and `ring` to close.

## Result

SUCCESS. The file compiles cleanly with
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/LMMBDF7Convergence.lean` (exit 0) and contains zero `sorry`. All six
target declarations (one structure + five theorems) landed.

## Residual coefficient

Computed via Python `Fraction` arithmetic:

```
c = 7^8/40320
  + (2940/1089) * 6^8/40320
  + (4410/1089) * 5^8/40320
  + (4900/1089) * 4^8/40320
  + (3675/1089) * 3^8/40320
  + (1764/1089) * 2^8/40320
  + (490/1089) * 1/40320
  + (420/1089) * 7^7/5040
  = 17914498/49005
  ≈ 365.5647
```

Slacked to integer `K = 366`.

## Aristotle

The full sorry-first scaffold compiled cleanly on the first attempt and the
six theorems closed in the same edit, so there were no live `sorry`s left to
batch-submit to Aristotle. The strategy's Aristotle-first checkpoint was
attempted but produced a no-op (no jobs to send) — every target was already
proved. Logging this so future cycles know that mechanical mirroring of a
prior BDF chain can land the whole truncation chain in one pass.

## Dead ends

None. The mirror of BDF6 transferred cleanly with the documented changes
(extra Taylor remainder, new leading factor, eight-element sum, eighth-order
helpers).

## Discovery

- `Fin.sum_univ_eight` is available and works for unfolding LTE on
  `bdf7 : LMM 7` (which indexes over `Fin 8`).
- The BDF6→BDF7 step requires only one new `R_y` slot in the abstract
  algebra core; no need to track `R_y(0)` since `α_0` enters multiplied by
  zero remainder. The strategy's "A,…,G,H" labelling (seven y-remainders + one
  derivative remainder) matches the algebraic identity exactly.
- `clear_value` after the eight `set` bindings keeps the residual `linarith`
  call within budget (cycle 458 / 461 / 462 lesson confirmed for BDF7).

## Suggested next approach

Per the strategy's fallback plan, the next natural BDF target is the BDF7
**vector** truncation chain. The new file `OpenMath/LMMBDF7VectorConvergence.lean`
would mirror this scalar chain using the 8th-order vector Taylor helpers
currently `private` inside `OpenMath/LMMAB7VectorConvergence.lean`
(`iteratedDeriv_eight_bounded_on_Icc_vec`,
`y_eighth_order_taylor_remainder_vec`,
`derivY_seventh_order_taylor_remainder_vec`). A small upstream edit to
promote those three helpers to public would unblock the vector mirror.

The BDF4/5/6 Lyapunov gap (`.prover-state/issues/bdf4_lyapunov_gap.md`)
remains structurally blocked and should not be reopened mid-stream.
