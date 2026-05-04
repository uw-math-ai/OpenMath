# Cycle 790 Results

## Worked on
§530 GLM order ≥ N witnesses for IRK 2-stage and 3-stage families,
landed in `OpenMath/RKAsGLM.lean` per cycle 790 strategy.

## Approach
Plug-and-play: for each method `t`, feed the existing tableau-level
`_orderN` and `_consistent` certificates through the existing
bridges `t.toGLM_hasOrderGeN`. For "lower from higher" cases,
project HasOrderGe4/3 down using the same `⟨h.1, h.2.1, …⟩`
destructuring pattern already established for `rk4` (RKAsGLM lines
601–666).

Added the import `OpenMath.LobattoIIIB3` and `OpenMath.RadauIA2`.
`rkRadauIIA2_*` lemmas live in `OpenMath/StiffEquations.lean`,
which is transitively pulled in via `RadauIA2`.

## Result
SUCCESS — all 15 GLM-side witnesses landed and the file compiles
cleanly with `lake env lean OpenMath/RKAsGLM.lean` (exit 0; only
pre-existing simp-arg lint warnings on lines 748/803/824). New
theorems:

2-stage (6):
- `rkLobattoIIIA2_toGLM_hasOrderGe2`
- `rkLobattoIIIC2_toGLM_hasOrderGe2`
- `rkRadauIA2_toGLM_hasOrderGe2`
- `rkRadauIA2_toGLM_hasOrderGe3`
- `rkRadauIIA2_toGLM_hasOrderGe2`
- `rkRadauIIA2_toGLM_hasOrderGe3`

3-stage Lobatto IIIA / IIIB / IIIC (9):
- `rkLobattoIIIA3_toGLM_hasOrderGe2`, `_3`, `_4`
- `rkLobattoIIIB3_toGLM_hasOrderGe2`, `_3`, `_4`
- `rkLobattoIIIC3_toGLM_hasOrderGe2`, `_3`, `_4`

All landed sorry-free using the projection patterns the strategy
specified (`⟨order4.1, order4.2.1⟩` for HasOrderGe2 from order-4,
4-tuple for HasOrderGe3 from order-4, direct apply for HasOrderGe4).

## Dead ends
None. The strategy's assessment that all 15 are 1–3 line bridges
held up exactly. No shape mismatches.

## Discovery
- `RadauIA2.lean` and `LobattoIIIB3.lean` were not yet imported
  by `RKAsGLM.lean`; importing both is enough to bring all
  needed certificates into scope (StiffEquations comes through
  RadauIA2).
- The compiler emits a noisy `PANIC at Lean.Expr.appArg!` from a
  simp simproc during compilation (not from the new code), but
  the build still succeeds with exit 0 and the panic does not
  produce an error diagnostic. Pre-existing condition in this
  file, unrelated to the cycle 790 changes.

## Suggested next approach
- Embedded-pair main-method GLM bridges
  (`rkRKF45.mainMethod.toGLM_hasOrderGe5`,
  `rkDormandPrince54.mainMethod.toGLM_hasOrderGe5`,
  `rkBogackiShampine32.mainMethod.toGLM_hasOrderGe3`,
  `rkHeunEuler21.mainMethod.toGLM_hasOrderGe2`). The strategy
  flagged these as the natural next batch; they need an extra
  `.mainMethod` indirection layer with its own
  `_main_orderN` / `_consistent` certificates. A focused cycle
  on these four short bridges should land cleanly.
- After that, pivot to §531 (GLM local / global truncation
  error), now that the §530 witness density is high.
- Continue to avoid LMM HasOrderGe2 for s ≥ 5 and LMM HasOrderGe3
  for s ≥ 3 (heartbeat-blocked; cycles 780, 786, 789 confirm).
