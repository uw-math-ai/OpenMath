# Cycle 1140 Results

## Worked on
`adamsBashforth5_toGLM_hasOrderGe2` in `OpenMath/LMMAsGLM.lean`, the
`s = 5`, `Fin 10` order-≥ 2 LMM-as-GLM witness. This is the
`HasOrderGe2` rung at `s = 5`, the prerequisite the cycle 786
heartbeat-cap wall blocked, and the prerequisite for the cycle 1141
follow-up (`adamsBashforth5_toGLM_hasOrderGe3`).

## Approach
Applied the cycle 800 helper-extraction recipe (per the cycle 1140
strategy):

- Created `namespace AB5GE2` with three `private noncomputable def`s
  for `qN`, `q'N`, `q''N` (the natural Nordsieck Taylor template, no
  shift constant — `q' j = j` on past-`y`, `1` on past-`h·f`;
  `q'' j = j²` on past-`y`, `2j` on past-`h·f`).
- Two `private theorem` helpers `q'_obligation` and `q''_obligation`,
  each taking `k : Fin 10`, with the obligation statements copied
  literally from the `HasOrderGe2` definition body in
  `OpenMath/GeneralLinearMethod.lean:189` (so the `q'_obligation`
  shape is `(∑ j, B k j) + ∑ l, V k l * q' l = q k + q' k`, and the
  `q''_obligation` shape is the second-derivative compatibility row).
- Each helper closes with `fin_cases k; all_goals simp [...]; all_goals
  norm_num` — the cycle 1132/1134/1136 standard.
- The top-level `theorem adamsBashforth5_toGLM_hasOrderGe2` packages
  the `qN/q'N/q''N` triple, dispatches the `V·q = q` row to
  `adamsBashforth5.toGLM_V_nordsieckQ_eq adamsBashforth5_consistent`,
  closes the `U·q = 𝟙` row inline (single `simp` cluster across
  `Fin 5`), and forwards the two `Fin 10` rows to the helpers.

## Result
**SUCCESS** — `OpenMath/LMMAsGLM.lean` compiles clean (no errors,
no warnings) under `lake env lean OpenMath/LMMAsGLM.lean` in
**~2m2s wall** (vs. the ~2m3s baseline before adding the theorem,
i.e. a negligible delta). No `Fin 10` case needed individual
extraction; the master `all_goals simp; all_goals norm_num` cluster
inside each helper closes all ten cases under the 200 000 heartbeat
budget. This confirms the cycle 800 helper-extraction recipe (each
`Fin 10` obligation living in its own `private theorem`) is on its own
sufficient — the cycle 786 wall was specifically about the **inline**
`HasOrderGe2` body trying to do all four rows in one tactic block, not
about any single `Fin 10` row being intrinsically expensive.

## Dead ends
First scaffold used `fin_cases k <;> · simp [...]; norm_num`, which
chained `norm_num` after every `simp`-closed branch and produced ten
"no goals to be solved" errors per helper. Switching to the explicit
`fin_cases k; all_goals simp [...]; all_goals norm_num` pattern (the
AB4 template) fixed it — `all_goals` skips already-closed goals.

## Discovery
- The cycle 786 heartbeat wall on `Fin 10` AB5 `HasOrderGe2` is
  **fully** dissolved by helper extraction: no per-case `Fin 10`
  literal split was required. This means the same helper-pattern
  shape that worked at `s = 4` (cycles 1132/1134/1136) lifts directly
  to `s = 5` for order-≥ 2 with no additional infrastructure.
- The wall-clock cost of the new theorem is negligible (~0s delta on a
  ~2m baseline). This means cycle 1141's HasOrderGe3 attempt at `s = 5`
  has a comfortable budget headroom — the q'''-row is the hard one
  (shift constant + extra obligation), but the q'/q''-rows already
  scale fine.

## Suggested next approach
Cycle 1141: target `adamsBashforth5_toGLM_hasOrderGe3` in the same
file, immediately after `adamsBashforth5_toGLM_hasOrderGe2`. Use a
fresh `AB5GE3` namespace mirroring `AB4GE3` (cycle 1134, line ~2298 in
the current file). The recipe:

1. Reuse `qN/q'N/q''N` shapes from `AB5GE2`; add `q'''N j = j³` on
   past-`y`, `3 j² + C` on past-`h·f` with shift constant `C`.
2. The shift constant `C` for AB5 (s=5, β_5 = 0) follows the cycle
   1134 ladder: AB2 → 1, AB3 → 4, AB4 → 16. Empirically `C` for AB5
   is most likely **25** (per the strategy hint), but compute by
   matching the q'''-row residue at `k = past-y 0` after expansion —
   this is `s² − 2 β_s s = 25 − 0 = 25` for AB5, which the strategy
   already pre-computed.
3. Each `Fin 10` obligation goes into its own `private theorem`. If
   any one of them overruns the heartbeat budget, split that case via
   the cycle 1134 pattern (`AB4GE3.q'''_obligation_seven` style with
   a literal `(⟨k, by decide⟩ : Fin 10)` index).
4. Cycle 786 noted the q'''-row at `k = past-y 0` is the natural
   wall — keep an eye on that case; if it overruns, extract first.
