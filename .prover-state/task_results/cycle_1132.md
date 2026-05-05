# Cycle 1132 Results

## Worked on

`adamsMoulton3_toGLM_hasOrderGe3 : adamsMoulton3.toGLM.HasOrderGe3` in
`OpenMath/LMMAsGLM.lean`, inserted between `bdf3_toGLM_hasOrderGe3` and
the `namespace Matrix` block. New private `AM3GE3` namespace holding
the four Nordsieck vectors (`qN`, `q'N`, `q''N`, `q'''N`) and the
factored helper `q'''_obligation`.

This is the cycle 804 strategy target — the planner's strategy.md still
points at AM3 as the next §530 LMM-as-GLM `HasOrderGe3` witness in the
AB3 (cycle 800) → BDF3 (cycle 802) → AM3 sequence.

## Approach

Copy-and-adapt the BDF3GE3 recipe verbatim:

- Shift constant `C := s² − 2 β_s s = 9 − 2·(3/8)·3 = 27/4` for
  `adamsMoulton3` (`β_s = 9/24 = 3/8`).
- `qN`, `q'N` identical to AB3GE3 / BDF3GE3 (shift only enters at
  `q''` and `q'''`).
- `q''N (j) = j² − 27/4` on the y-block, `2j` on the f-block.
- `q'''N (j) = j³ − 3·(27/4)·j` on the y-block,
  `3·(j² − 27/4)` on the f-block.
- `q'''_obligation` discharged by `fin_cases k` with six identical
  `· simp [...]; norm_num` branches, exactly mirroring BDF3GE3.
- Headline `adamsMoulton3_toGLM_hasOrderGe3` mirrors the BDF3 headline
  with method/namespace renamed.

The first `?_` (the `(U q)` sum branch) closed with bare `simp` — no
trailing `norm_num` needed (matches the AB3 first `?_`, not the BDF3
one which had a fractional residual).

## Result

SUCCESS — `lake env lean OpenMath/LMMAsGLM.lean` compiles cleanly in
~3 min wall time (CPU 3m1s) with no warnings or errors.

## Dead ends

None this cycle — the recipe transferred directly. The cycle 802
strategy correctly anticipated `C = 27/4` for AM3, and the helper-
extraction template was already proven on the BDF3 sibling.

## Discovery

- The `(U q)` first-branch tactic shape behaves like AB3 (bare `simp`
  closes), not BDF3 (which needed `simp; norm_num`). This refines the
  strategy's "two scenarios" guidance: for the first `?_`, AB3-style
  bare `simp` works whenever the closure-row `β` row, after
  multiplying by the constant `qN` vector, simplifies to a clean
  numeric goal that `simp` itself can close. AM3's `β = [1/24, -5/24,
  19/24, 9/24]` and constant `qN ≡ 1` on the y-block, `≡ 0` on the
  f-block, lets `simp` finish without fraction arithmetic.
- File size went from 2371 → 2452 lines (+81). Still well under the
  3000-line soft cap.
- Wall time at 178 s is on the high end for a Fin 6 HasOrderGe3
  witness (BDF3 was ~115 s in cycle 802) but well within the heartbeat
  budget — no warnings emitted. The slight slowdown is consistent with
  the slightly more complex `β` literal.

## Suggested next approach

The §530 `HasOrderGe3` LMM witness pipeline now covers AB3, BDF3, AM3
— all `s = 3` `Fin 6` methods with shift constants 9, 63/11, 27/4
respectively. Natural next-cycle targets in priority order:

1. **`Fin 8` family** (BDF4, AM4, AB4) with `HasOrderGe3` — the cycle
   804 strategy explicitly flagged this as the right next-cycle
   target. Note cycle 786 hit heartbeat issues on `Fin 10` GE2; the
   `Fin 8` heartbeat profile under the helper-extraction recipe is
   untested and should be the **primary** investigation target of its
   own cycle.

2. **§510/§512/§515 GLM Dahlquist equivalence** — the textbook jump
   from §530 to §51X is the natural follow-on once the LMM witness
   table is complete enough.

3. **`HasOrderGe4` for AB3 / BDF3 / AM3**: extend the Nordsieck-vector
   recipe to a fifth obligation. AM3 is order 4 in the textbook, so
   `HasOrderGe4` should be reachable; AB3 is order 3 so it cannot
   embed at order ≥ 4 (good negative test).

Avoid restarting §38 / §386 / §388 work — see `disproven.md`.
