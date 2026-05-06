# Cycle 1180 Results

## Worked on
`adamsBashforth8_toGLM_hasOrderGe3` in
`OpenMath/LMMAsGLM/Section530Step8.lean` — extending the `s = 8`
LMM-as-GLM order-≥ 3 rotation per cycle 1180 strategy.

## Approach
Mechanical mirror of the cycle 1168 `AB7GE3` namespace
(`OpenMath/LMMAsGLM/Section530Step7.lean:185–481`) into a new
`AB8GE3` namespace, with substitutions:

- `7 → 8` (`Fin (2 * 7)` → `Fin (2 * 8)`, `Fin 14` → `Fin 16`,
  `Nat.two_mul 7` → `Nat.two_mul 8`)
- `adamsBashforth7 → adamsBashforth8`
- Shift constant `49 → 64` (`s² − 2 β_s · s = 64` since
  `β_s = 0` for explicit AB methods, so `C = s² = 64`)

Helper-extraction shape:

- `q'_obligation`: single `fin_cases k`; `all_goals simp […];
  all_goals norm_num`.
- `q''` per-row helpers `seven`..`fifteen` (nine helpers, k = 7..15).
  Boundary `q''_obligation_eight` (k = 8, first past-`h·f` row,
  `β_s = 0`) closes with **`simp` alone**; all others
  `simp [...]; norm_num`.
- Aggregate `q''_obligation`: seven inline arms `simp […]; norm_num`
  for k = 0..6, then nine `exact q''_obligation_*` arms for k = 7..15.
- `q'''` per-row helpers `four`..`fifteen` (twelve helpers, k = 4..15).
  All close with `simp [...]; norm_num`, including the k = 8 boundary
  (`q'''_obligation_eight`) — `C = 64 ≠ 0` leaves a numeric residue
  so `norm_num` is required (cycle 1168 rule for `C ≠ 0`).
- Aggregate `q'''_obligation`: four inline arms for k = 0..3, then
  twelve `exact q'''_obligation_*` arms for k = 4..15.

Headline `adamsBashforth8_toGLM_hasOrderGe3` mirrors AB7GE3 exactly:
two `?_` arms (`(U q)` Nordsieck closure via
`adamsBashforth8.toGLM_V_nordsieckQ_eq adamsBashforth8_consistent`,
plus the per-row `q` sanity check) and three `exact` arms
(`q'_obligation`, `q''_obligation`, `q'''_obligation`).

## Result
SUCCESS — `lake env lean OpenMath/LMMAsGLM/Section530Step8.lean`
clean build in **2m0.7s** wall time (vs. the AB8GE2 1m38.9s baseline
from cycle 1178; the +22s reflects the q''' row ladder). No sorries
remain. AB family boundary nuances held exactly as predicted at
`s = 8`:

- `q''_obligation_eight` (k = 8 boundary): `simp` alone — adding
  `norm_num` would have triggered "no goals to be solved".
- `q'''_obligation_eight` (k = 8 boundary): `simp + norm_num` — the
  `C = 64` shift leaves a residual numeric goal.

## Dead ends
None. The mechanical mirror went through on the first build with no
heartbeat issues; the per-row helper extraction kept each individual
goal well under the 200000-heartbeat budget. The "acceptable minimum"
fallback of splitting a single helper into halves was not needed.

## Discovery
The AB family `s = 8` rotation now has `HasOrderGe1`, `HasOrderGe2`,
and `HasOrderGe3` witnesses, all in the leaf
`Section530Step8.lean`. The order-3 boundary-row rules established at
`s = 7` (cycle 1168) — `q''_eight` simp-alone, `q'''_eight`
simp+norm_num when `C ≠ 0` — generalise verbatim. Confirms the
cycle-1168-style "`C = s² − 2 β_s · s` for explicit AB" formula, with
`β_s = 0` collapsing to `C = s²`.

## Suggested next approach
Continue the planner-prescribed `s = 8` rotation:

1. `adamsMoulton8_toGLM_hasOrderGe2` — implicit AM with `β_s ≠ 0`,
   so `C ≠ 0` even at order 2; mirror `AM7GE2` template from
   `Section530Step7.lean`.
2. Then `adamsMoulton8_toGLM_hasOrderGe3` (mirror `AM7GE3`).
3. Then `bdf8_toGLM_hasOrderGe2` and `bdf8_toGLM_hasOrderGe3`.

Each lands as a sibling namespace inside the existing
`Section530Step8.lean` leaf — do not touch the umbrella imports.

The `disproven.md` cap at order 4 (cycle 1138 obstruction) stops the
rotation there; do not push beyond `HasOrderGe3` on any LMM-as-GLM.
