# Cycle 1144 Results

## Worked on

`adamsMoulton5_toGLM_hasOrderGe2` (and the trivial `_hasOrderGe1`
corollary) in `OpenMath/LMMAsGLM.lean`, the §530 LMM-as-GLM
order-≥ 2 witness for the AM5 6-input implicit method (`s = 5`,
`Fin 10`, `β_s = 475/1440 ≠ 0`, classical order 6).

## Approach

Followed the planner's copy-paste-ready scaffold verbatim. Inserted
a new `namespace AM5GE2` block immediately after the AB5GE2
theorem (between line 1727 and the AB5GE3 namespace), with the
unshifted natural Nordsieck Taylor template:

- `qN`     = `[1,1,1,1,1, 0,0,0,0,0]`
- `q'N`    = `[0,1,2,3,4, 1,1,1,1,1]`
- `q''N`   = `[0,1,4,9,16, 0,2,4,6,8]`

Both per-row obligations close with the
`fin_cases k; all_goals simp [...]; all_goals norm_num` shape,
matching the cycle 1140 AB5GE2 recipe — no per-case extraction
needed for the `Fin 10` rows.

## Result

SUCCESS. `OpenMath/LMMAsGLM.lean` compiles cleanly in ~2m24s
(comparable to cycle 1140 AB5GE2). New theorems landed:

- `adamsMoulton5_toGLM_hasOrderGe2`
- `adamsMoulton5_toGLM_hasOrderGe1`

## Dead ends

The strategy's draft scaffold included a trailing `norm_num` after
the `(U·𝟙)_0` row's `simp` block, citing the cycle 802 BDF3GE3
note that implicit closure rows may need it. On AM5 this was *not*
needed: the inline `simp [LMM.toGLM, adamsMoulton5, Fin.addCases,
Fin.sum_univ_succ, AM5GE2.qN]` *closes* the goal on its own,
exactly as AM3GE2 (line 2040) does without `norm_num`. Compiling
with the trailing `norm_num` produced
`error: No goals to be solved` at line 1784. Removing the
`norm_num` fixed it on the first retry.

## Discovery

- AM5's `β_s = 475/1440 ≠ 0` enters the proof through the
  expansion of `adamsMoulton5.toGLM.B 0 j` rows in the q' and q''
  obligations (the `simp [adamsMoulton5, ...]` step normalizes the
  `Fin.cast`/`Fin.addCases` lookup of the β coefficients
  `[27/1440, -173/1440, 482/1440, -798/1440, 1427/1440, 475/1440]`).
  These rationals show up in the q' obligation's `(B·𝟙)_k + (V·q')_k =
  q_k + q'_k` for the past-`y` rows `k = 0..4`, where
  `(B·𝟙)_k = β·𝟙 = ∑β = 1` (consistency) but only after `norm_num`
  collapses the rationals.
- For the U-row sum (the `_0` slot only, as `Fin (s+1−s) = Fin 1`
  contributes one constraint here at `i = 0`), `simp` closes the
  goal by itself — this matches cycle 1132 AM3GE2's behaviour on
  the smaller `s = 3` case, **not** the cycle 802 BDF3GE3 case
  which apparently has additional residue. The strategy's
  prediction of "needs `norm_num`" was conservative; in practice
  the `Fin 1` block is short enough that `simp`'s default
  `norm_num`-like closure on numeric literals suffices.

## Suggested next approach

The next rung on the explicit ladder per the strategy is **AM5
HasOrderGe3** with shift constant
`C = s² − 2 β_s s = 25 − 2·(475/1440)·5 = 25 − 4750/1440
       = 25 − 475/144 = 3125/144`.
The shifted Nordsieck template is

  `q''N(past-y, j) := j² − 3125/144`,
  `q'''N(past-y, j) := j³ − 3·(3125/144)·j`.

This is structurally the AB5GE3 / AM4GE3 hybrid: same shifted
Taylor template as AB5GE3 but with the C constant from AM4GE3
generalized. The per-case `Fin 10` extraction recipe from cycle
1142 AB5GE3 (helpers `q'''_obligation_four`, `_seven`, `_eight`,
`_nine`) likely transfers. Schedule this as cycle 1145 or 1146.

After AM5 GE3, the next ladder targets are AB6 GE2 and BDF5 /
BDF6 GE2.

## Notes on engagement

This cycle was a 30-minute exercise as the planner predicted:
type the scaffold, hit one false-positive `norm_num` line,
delete it, recompile clean. No Aristotle, no MCP search, no
freelancing.
