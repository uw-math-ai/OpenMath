# Cycle 1146 Results

## Worked on
`adamsMoulton5_toGLM_hasOrderGe3` in `OpenMath/LMMAsGLM.lean`.

## Approach
Mechanical mirror of the cycle 1142 `AB5GE3` block (lines 1800–1944)
into a new `AM5GE3` namespace inserted between
`adamsBashforth5_toGLM_hasOrderGe3` and the trapezoidal block. Three
substitutions per the strategy:

- `adamsBashforth5` → `adamsMoulton5`
- shift constant `25` → `3125 / 144`  (= s² − 2 β_s s for s=5, β_s=475/1440)
- `3 * 25` → `3 * (3125 / 144)`

Pre-extracted the `k = 4, 7, 8, 9` cases of `q'''_obligation` into
private theorems (`q'''_obligation_four / _seven / _eight / _nine`)
so they get fresh heartbeat budgets, exactly mirroring the AB5GE3
schedule. The remaining `k = 0, 1, 2, 3, 5, 6` rows are inlined in
the parent.

The headline `(U·q)_i` closure row uses `simp [...]` only (no trailing
`norm_num`) per the cycle 1144 AM5GE2 pattern.

## Result
SUCCESS. `lake env lean OpenMath/LMMAsGLM.lean` returns clean (no
errors, no warnings) in ~2m45s. The new theorem
`adamsMoulton5_toGLM_hasOrderGe3 : adamsMoulton5.toGLM.HasOrderGe3`
lands sorry-free.

## Dead ends
None — the templated recipe worked on first try. The shift constant
`3125 / 144` reduced cleanly under `norm_num` for all `Fin 10` rows,
including the heaviest `k = 4, 7, 8, 9` cases. No additional helper
extraction was needed beyond the four already scheduled.

## Discovery
The `r = 2s` Nordsieck shift formula `C = s² − 2 β_s s` continues to
hold across the implicit AM ladder: AM3 (β_s=5/12, s=3, C=27/2),
AM4 (β_s=251/720, s=4, C=...), AM5 (β_s=475/1440=19/57.6, s=5,
C=3125/144). The strategy's algebra (25 − 475/144 = 3125/144) is
correct.

For AM5 specifically: 25 = 3600/144, so 3600/144 − 475/144 = 3125/144.

`norm_num` handles the fractional shift `3125/144` without any
additional tactics — the heartbeat budget for AM5GE3 rows is
comparable to AB5GE3 despite the implicit β_s ≠ 0.

## Suggested next approach
Per the strategy's "After AM5 GE3 lands" forward look:

1. **AB6 GE2** (`s = 6`, `Fin 12`, `β_s = 0`, classical order 6) —
   first GE2 rung at `Fin 12`, an unshifted Nordsieck template
   (matches AB5GE2 / AM5GE2 shape on `Fin 10`).
2. **AB6 GE3** (shift `C = 36`, since `β_s = 0`).
3. **BDF5 GE2** / **BDF5 GE3** with shift constants from BDF5's
   `β_5` coefficient.

The AB6 / AM6 step from `Fin 10` to `Fin 12` is the natural next
incremental challenge — `Fin.sum_univ_succ` has to peel two more
layers, which may push the per-case heartbeat budget high enough to
require pre-emptively factoring more than four helper cases. The
recipe above scales 1-to-1 by adding two more `q'''_obligation_*`
helpers. Defer GE4 globally (proven blocked per cycle 1138's
obstruction file).
