# Cycle 784 Results

## Worked on
§530 LMM-as-GLM order witnesses for `adamsBashforth3` in
`OpenMath/LMMAsGLM.lean`, plus the AB4 GE1 stretch wrapper.

## Approach
Followed the strategy verbatim:

1. Inserted `adamsBashforth3_toGLM_hasOrderGe1` (one-line wrapper) right
   after `adamsBashforth2_toGLM_hasOrderGe1` (line ~1656). Reuses
   `LMM.toGLM_hasOrderGe1` with `adamsBashforth3_consistent`
   (`OpenMath/AdamsMethods.lean:476`).
2. Inserted `adamsBashforth3_toGLM_hasOrderGe2` right after
   `adamsBashforth2_toGLM_hasOrderGe2` (line ~1757). Used the cycle-782
   AB2 GE2 body verbatim with `2 → 3` substitutions in the
   `Fin (2 * _)` / `Nat.two_mul` casts and `adamsBashforth2 →
   adamsBashforth3` swap.
3. Took the optional stretch — added `adamsBashforth4_toGLM_hasOrderGe1`
   wrapper using `adamsBashforth4_consistent`
   (`OpenMath/AdamsMethods.lean:494`).

## Result
SUCCESS — all three theorems compile. `lake env lean
OpenMath/LMMAsGLM.lean` exits 0. The natural Nordsieck Taylor template
with `q' j = j, 1` and `q'' j = j², 2j` closed both AB3 GE2 obligation
branches (`B 𝟙 + V q' = q + q'` and `2 (B c) + V q'' = q + 2 q' + q''`)
without per-branch `fin_cases k` splits — the `intro k; fin_cases k;
all_goals simp [..., Fin.sum_univ_succ]; all_goals norm_num` block
worked on `Fin 6` within heartbeat budget.

No `whnf`/heartbeat blowup observed on AB3 GE2. Consistent with the
strategy's prediction: AB3 GE2 is strictly easier than the BDF3 GE3
case that blew the budget in cycle 780 (order 2 vs 3, no cubic terms;
explicit so the implicit-row B-block vanishes).

## Dead ends
None — the strategy template fit on the first attempt.

## Discovery
- `Fin 6` `Fin.sum_univ_succ` expansion + `norm_num` is feasible at
  order 2 within 200000 heartbeats for explicit LMMs. The cycle-780
  blowup on BDF3 GE3 was specifically about (a) order 3's cubic terms
  in the `q'''` slot and (b) the `whnf` slowdown unique to that case.
- The AB pattern (`q' j = j, 1`; `q'' j = j², 2j`) for explicit
  `β_s = 0` LMMs is portable across step counts without any shift —
  the natural template, no `C` correction, suffices for GE2.

## Suggested next approach
The next planning steps would be:

1. **`bdf3_toGLM_hasOrderGe2`**: needs a non-trivial shift constant `C`
   because BDF3 has `β_s ≠ 0` (just like AM2 needed `C = 7/3` at order
   3 in cycle 780). Compute `C = s² - 2 β_s s` for BDF3's `β_s`.
2. **`adamsBashforth3_toGLM_hasOrderGe3`**: cycle 780 explicitly noted
   the `Fin 6` order-3 `whnf` blowup. Needs specialized lemmas for
   `LMM.toGLM` evaluation that avoid the `simp [LMM.toGLM]` unfolding
   that triggers `whnf`. Plan a separate cycle for that.
3. **`adamsMoulton3_toGLM_hasOrderGe*`**: AM3 has `s = 3, β_s ≠ 0`,
   `Fin 6`. Implicit shift constant required, GE2 likely tractable
   along the BDF3 path once `C` is known.
4. **`adamsBashforth4_toGLM_hasOrderGe2`**: explicit, `s = 4`, `Fin 8`.
   Since the `Fin 6` AB3 GE2 fit easily, `Fin 8` AB4 GE2 with the same
   natural template is likely tractable too — try the verbatim
   adaptation next.
