# Cycle 788 Results

## Worked on
§530 LMM-as-GLM order witnesses for `adamsMoulton4` and `bdf4`,
following the cycle 786 BDF3 / AB4 template.

## Approach
Per strategy.md, copied the cycle-786 BDF3 `HasOrderGe2` block verbatim
in `OpenMath/LMMAsGLM.lean` (immediately after the existing AB4
`HasOrderGe2` block), substituting `Fin (2*3) → Fin (2*4)`,
`Fin 3 → Fin 4`, `Nat.two_mul 3 → Nat.two_mul 4`, and the method /
consistency identifiers. Natural unshifted Nordsieck Taylor template:
`q k = 1` on past-`y`, `0` on past-`h·f`; `q' k = j` on past-`y`,
`1` on past-`h·f`; `q'' k = j²` on past-`y`, `2 j` on past-`h·f`.

## Result
SUCCESS — landed all four targets sorry-free:

- `adamsMoulton4_toGLM_hasOrderGe2` (8 input slots, natural Nordsieck
  template, `simp + norm_num` for the U-row + Bℓ + B c² obligations).
- `adamsMoulton4_toGLM_hasOrderGe1` (`.toHasOrderGe1` corollary).
- `bdf4_toGLM_hasOrderGe2` (same template; U-row needs an extra
  `norm_num` like BDF3 because `∑ α = 0`-style consistency leaves a
  numeric tail).
- `bdf4_toGLM_hasOrderGe1` (`.toHasOrderGe1` corollary).

`lake env lean OpenMath/LMMAsGLM.lean` builds cleanly in ~90 s with
no errors and no `maxHeartbeats` bumps.

## Dead ends
None this cycle — the strategy's recipe transferred directly. AM4 did
not need the U-row `simp`-only special case AM3 had; the
BDF3-pattern (`simp ... ; norm_num`) was unnecessary for AM4's U-row
(no leftover numeric tail there) and the cleaner three-line pattern
copied from AB4 works without modification.

## Discovery
- AM4 U-row obligation closes with the AB-style three-line block
  (`simp [...]` only, no trailing `norm_num`); the AM3 / BDF3 split
  on whether U-row needs `norm_num` is method-specific (depends on
  whether consistency drops a clean `1` or a pre-rationalized
  fraction). AM4's `∑ β = 1` lands as `1` definitionally after
  `simp`, so no `norm_num` is needed for the U-row branch.
- BDF4 Q' / Q'' obligations close within the 200000-heartbeat budget
  on `Fin 8`. The strategy's "drop only the q'' obligation back to
  `sorry` if the simp closure is too heavy" fallback was not
  triggered.

## Suggested next approach
With AM4 + BDF4 in at `HasOrderGe2`, the natural-template `s ≤ 4`
LMM-as-GLM `HasOrderGe2` family is exhausted (modulo BDF1 trivially
covered via `forwardEuler`/`backwardEuler` patterns and trapezoid
already done). Next planner targets:

1. `adamsMoulton4_toGLM_hasOrderGe3` using the cycle 780 AM2
   shifted-template recipe (`q'' shift -C` with
   `C = s² - 2 β_s s = 16 - 2 · 251/720 · 4 = 16 - 251/90`).
   Risk: `Fin 8` q''' obligation likely exceeds the 200000-heartbeat
   budget under the natural simp closure. Plan a profile / decompose
   strategy *before* the cycle (or pre-write helper lemmas that
   isolate the past-`y` and past-`h·f` rows separately).
2. Pivot to GLM-side `HasOrderGe3` predicate for general GLMs (the
   §530 plan note flagged order ≥ 3 as the next predicate-level
   extension that lands without per-method simp blow-up).
3. Return to §521 stability transports for additional methods if the
   §530 sweep exhausts.
