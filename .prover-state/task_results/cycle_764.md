# Cycle 764 Results

## Worked on
§530 GLM order ≥ 2 — projection lemma plus two RK-side witnesses.

## Approach
Followed the cycle-764 strategy verbatim. Three small additions, all
mechanical, no predicate redesign.

## Result
SUCCESS — all three additions compile sorry-free.

Theorems added:

* `GeneralLinearMethod.HasOrderGe2.toHasOrderGe1` in
  `OpenMath/GeneralLinearMethod.lean` (immediately after `HasOrderGe2`,
  inside `namespace GeneralLinearMethod`). Three-line proof using the
  flat `obtain ⟨q, q', _q'', hVq, hUq, hBq', _⟩ := h` pattern. The
  conjunction was right-associated so the flat seven-fold destructure
  worked on the first attempt.
* `rkHeun_toGLM_hasOrderGe2 : rkHeun.toGLM.HasOrderGe2` in
  `OpenMath/RKAsGLM.lean`, immediately after
  `rkImplicitMidpoint_toGLM_hasOrderGe2`. One-line term-mode proof
  through the cycle-762 bridge `ButcherTableau.toGLM_hasOrderGe2`,
  fed by `rkHeun_order2` (`OpenMath/RungeKutta.lean:441`) and
  `rkHeun_consistent` (`OpenMath/RungeKutta.lean:405`).
* `rkSDIRK2_toGLM_hasOrderGe2 : rkSDIRK2.toGLM.HasOrderGe2` in
  `OpenMath/RKAsGLM.lean`, directly after the Heun witness. Same shape,
  fed by `rkSDIRK2_order2` (`OpenMath/SDIRK.lean:112`) and
  `rkSDIRK2_consistent` (`OpenMath/SDIRK.lean:106`). `OpenMath.SDIRK`
  was already imported, so no import edit needed.

## Verification
* `lake env lean OpenMath/GeneralLinearMethod.lean` — clean.
* `lake build OpenMath.GeneralLinearMethod` — refreshed olean.
* `lake env lean OpenMath/RKAsGLM.lean` — clean (only pre-existing
  unused-simp warnings at lines 424 and 445, untouched by this cycle).
* `lake build OpenMath.RKAsGLM` — completed successfully with the same
  pre-existing warnings.

## Dead ends
None. The strategy's first destructure shape matched, and the import
graph was already wired for SDIRK2.

## Discovery
* The `HasOrderGe2` predicate's four-conjunction body is right-associated
  in the way the flat seven-element anonymous constructor wants — i.e.
  `⟨q, q', q'', a, b, c, d⟩` matches without needing the manual
  splitter fallbacks the strategy listed.
* `OpenMath.SDIRK` is already among `RKAsGLM.lean`'s imports
  (`OpenMath/RKAsGLM.lean:3`), so adding SDIRK2 witnesses inside
  `RKAsGLM` is import-free.

## Suggested next approach
The cycle 762 task result's stretch goal — `HasOrderGe3` — remains
the natural next predicate. As the cycle 764 strategy noted, that
needs both `order3a` and `order3b` RK conditions on the bridge side,
plus a third Nordsieck input vector `q'''` interpretation. A
follow-up cycle could:

1. Define `HasOrderGe3` mirroring `HasOrderGe2` with a fifth
   conjunct (third-derivative compatibility identity over a chosen
   `q'''`).
2. Prove `HasOrderGe3.toHasOrderGe2` projection.
3. Bridge `ButcherTableau.toGLM_hasOrderGe3` with `q ≡ 1`,
   `q' = q'' = q''' = 0` against `HasOrderGe3 ∧ IsConsistent`.
4. Land witnesses for at least `rkRalston3` / `rkClassicalRK4` /
   `rkRadauIIA3` (whichever already has `HasOrderGe3` proven on the
   RK side; check `OpenMath/RungeKutta.lean` and friends).

Alternatively, the LMM-side `LMM.toGLM_hasOrderGe2` bridge is still
open — that one needs fresh `q''` Nordsieck witnesses for the past-y
input block, so it is its own cycle.

Either is a clean follow-up. `HasOrderGe3` is probably the smaller
of the two.
