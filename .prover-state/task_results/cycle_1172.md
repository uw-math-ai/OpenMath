# Cycle 1172 Results

## Worked on

`adamsMoulton7_toGLM_hasOrderGe3` in
`OpenMath/LMMAsGLM/Section530Step7.lean`. Added a new namespace
`AM7GE3` and headline theorem after the existing
`adamsBashforth7_toGLM_hasOrderGe3`. Existing theorems
(`adamsMoulton7_toGLM_hasOrderGe2`, `adamsBashforth7_toGLM_hasOrderGe3`,
etc.) were not touched.

## Approach

Mechanical mirror of the AB7GE3 template (lines 185–481), per the
planner's strategy. Substitutions:

- `AB7GE3` → `AM7GE3`
- `adamsBashforth7` → `adamsMoulton7`
- `adamsBashforth7_consistent` → `adamsMoulton7_consistent`
- Pascal-style shift constant `49` → `386561/8640`
  (= 49 − 14·(36799/120960) = s² − 2 β_s s with β_s = 36799/120960).

Per-row helper tactic shape:

- `q'_obligation`: `simp [...]` followed by `norm_num`.
- `q''_obligation_six`, `..._eight..._thirteen`: `simp [...]; norm_num`.
- `q''_obligation_seven` (k = 7 boundary, past-`h·f` slot unshifted at
  order 2): `simp [...]` alone — matches AM7GE2 cycle 1170 pattern.
- `q''_obligation` dispatcher: `simp [...]; norm_num` for k = 0..5,
  `exact` to helpers for k = 6..13.
- `q'''_obligation_four..._thirteen` (10 helpers): all
  `simp [...]; norm_num`. The k = 7 boundary requires `norm_num`
  because `C ≠ 0` leaves a numeric residue (analogous to AB7GE3
  cycle 1168).
- `q'''_obligation` dispatcher: `simp [...]; norm_num` for k = 0..3,
  `exact` to helpers for k = 4..13.

Headline closure mirrors the AM7GE2 pattern with `adamsMoulton7` in
the simp set and `AM7GE3.qN` for the unrolling.

## Result

SUCCESS — `lake env lean OpenMath/LMMAsGLM/Section530Step7.lean`
compiled in **2m2s** wall (3m48s user) with no errors or warnings.
First-try landing per planner expectation.

File grew from 481 → 793 lines (+312 LOC), well below the 3000-line
hard cap.

## Dead ends

None. The mechanical mirror landed first try.

## Discovery

- The shift constant `C = 386561/8640 ≈ 44.74` is a relatively large
  irrational-looking rational, but `norm_num` closes the k = 7
  past-`h·f` `q'''` residue without trouble (≈ same wall time as the
  AB7GE3 analog with `C = 49`).
- The `q''` k = 7 row genuinely closes with `simp` alone in the
  AM-family pattern, even with `β_s ≠ 0`. The Nordsieck shift only
  appears on the past-`y` slots at order 2; past-`h·f` is `2 j`
  unshifted, matching AM7GE2 (cycle 1170) and AB7GE2 (cycle 1166).
- Total wall time (2m02s) is in line with cycles 1168 (AB7GE3) and
  1170 (AM7GE2) — the s = 7 / Fin 14 helper-extraction recipe is
  thoroughly stabilized.

## Suggested next approach

Per the strategy, the §530 LMM-as-GLM `HasOrderGe3` rotation
continues:

1. **Cycle 1174**: `bdf7_toGLM_hasOrderGe2` — Fin 14 BDF7 mirror of
   BDF6GE2 (cycle 1162) with `s : 6 → 7`. Should be a clean mirror
   like AM7GE2 was.
2. **Cycle 1176**: `bdf7_toGLM_hasOrderGe3` — Fin 14 BDF7 mirror of
   BDF6GE3 (cycle 1164). Need to compute `C = s² − 2 β_s s` for BDF7
   first; per `OpenMath/AdamsMethods.lean` (or BDF source) extract
   `bdf7.β` last entry. The BDF6GE3 constant was 1524/49.

After cycle 1176 the s = 7 frontier closes for AB7 / AM7 / BDF7.
Cycle 1178+ should weigh whether to open s = 8 (note `bdf8` is
zero-unstable per Dahlquist) or pivot to a different §530 / §54
frontier (DIMSIM, ARK).
