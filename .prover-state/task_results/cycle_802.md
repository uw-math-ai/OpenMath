# Cycle 802 Results

## Worked on
`bdf3_toGLM_hasOrderGe3 : bdf3.toGLM.HasOrderGe3` in
`OpenMath/LMMAsGLM.lean` — direct continuation of cycle 800
(`adamsBashforth3_toGLM_hasOrderGe3`), using the helper-extraction
recipe from `AB3GE3`.

## Approach
Mirrored the cycle 800 `AB3GE3` block verbatim in a new private
namespace `BDF3GE3`, with the BDF3-specific shift constant
`C := s² − 2 β_s s = 9 − 2·(6/11)·3 = 9 − 36/11 = 63/11`.

The four Nordsieck vectors were extracted as
`private noncomputable def`s:
- `qN`: `1` on past-y, `0` on past-f
- `q'N`: `j` on past-y, `1` on past-f
- `q''N`: `j² − 63/11` on past-y, `2j` on past-f
- `q'''N`: `j³ − 3·(63/11)·j` on past-y, `3·(j² − 63/11)` on past-f

The q''' obligation was extracted as a `private theorem` (`q'''_obligation`)
and discharged via `fin_cases k` with one `simp [...]; norm_num` per
branch. The four parent obligations (V·q preconsistency; U·q sum;
B·q' / V·q'; second-derivative) close inside the parent theorem.

## Result
**SUCCESS** — `bdf3_toGLM_hasOrderGe3` is sorry-free and
`lake env lean OpenMath/LMMAsGLM.lean` exits 0 in ~115 s wall time.

## Dead ends
None this cycle — the recipe transferred cleanly. One small departure
from AB3: the `(U q)` sum (second `?_`) needed an additional
`norm_num` after `simp` because the BDF3 closure row has fractional
`U` coefficients that AB3 (with `β_s = 0`) does not. This matches the
existing `bdf3_toGLM_hasOrderGe2` pattern (line 1859) which also
appends `norm_num`.

## Discovery
The helper-extraction recipe is now confirmed transferable from
`AB3GE3` (β_s = 0, no fractional U coefficients) to `BDF3GE3`
(β_s = 6/11, fractional U coefficients in the closure row). Wall
time scaled from ~85 s (AB3) to ~115 s (BDF3); the fractional-arithmetic
cost is real but well within budget. This is encouraging for the
analogous `AM3GE3` target with `β_s = 3/8, C = 27/4`.

## Suggested next approach
1. **`adamsMoulton3_toGLM_hasOrderGe3`** — same recipe, with
   `s = 3, β_s = 9/24 = 3/8, C = s² − 2 β_s s = 9 − 9/4 = 27/4`.
   Use a distinct private namespace `AM3GE3`. This is the cycle 800
   "Suggested next approach" item 2 and the natural cycle 804 target.
2. **`bdf4_toGLM_hasOrderGe3`** — would extend the recipe to `Fin 8`
   (eight GLM input slots). For BDF4, `β_s = 12/25` so
   `C = 16 − 2·(12/25)·4 = 16 − 96/25 = 304/25`. Wall-time risk on
   `Fin 8` is unknown — cycle 786 noted that `Fin 10` GE2 q'' obligations
   already exhaust the budget, but `Fin 8` may still be tractable for
   GE3 with helper extraction. Worth a dedicated planner cycle to
   gauge feasibility.
3. The `q'''_obligation` in `BDF3GE3` does six per-`fin_cases`
   `simp; norm_num` calls. If wall time becomes a concern at `Fin 8`,
   a `lean_profile_proof` run on a BDF3 branch would tell us where the
   heartbeats actually go (likely the inlined `Fin.addCases` reduction,
   per the cycle 800 analysis).
