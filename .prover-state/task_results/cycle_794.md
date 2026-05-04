# Cycle 794 Results

## Worked on
§530 embedded-pair **embed-method** GLM order witnesses in
`OpenMath/RKAsGLM.lean`, plus the missing
`rkHeunEuler21_mainMethod_toGLM_hasOrderGe1` projection from cycle 792.

## Approach
Followed the cycle-792 main-method block (lines 1487–1574) as a literal
template. Each new theorem is a one-line wrapper of the form
`<pair>.embedMethod.toGLM_hasOrderGeN <orderHyp> <consHyp>` where
`<consHyp>` is `<pair>_consistent.embed_consistent`. Where the bridge
demands a smaller `HasOrderGeM` predicate, projected the existing
`rk*_embed_order4 : HasOrderGe4` 8-tuple via right-nested `.1 / .2.1 /
.2.2.1 / ...` accessors as the strategy spelled out.

## Result
SUCCESS — all twelve theorems landed:

1. `rkHeunEuler21_embedMethod_toGLM_hasOrderGe1`
2. `rkBS32_embedMethod_toGLM_hasOrderGe2`
3. `rkBS32_embedMethod_toGLM_hasOrderGe1`
4. `rkRKF45_embedMethod_toGLM_hasOrderGe4`
5. `rkRKF45_embedMethod_toGLM_hasOrderGe3`
6. `rkRKF45_embedMethod_toGLM_hasOrderGe2`
7. `rkRKF45_embedMethod_toGLM_hasOrderGe1`
8. `rkDOPRI5_embedMethod_toGLM_hasOrderGe4`
9. `rkDOPRI5_embedMethod_toGLM_hasOrderGe3`
10. `rkDOPRI5_embedMethod_toGLM_hasOrderGe2`
11. `rkDOPRI5_embedMethod_toGLM_hasOrderGe1`
12. `rkHeunEuler21_mainMethod_toGLM_hasOrderGe1`

`lake env lean OpenMath/RKAsGLM.lean` compiles cleanly in ~1m35s
(real). No `sorry` introduced. No new errors. Two pre-existing
`unusedSimpArgs` warnings (RKAsGLM.lean:804 and :825) are unrelated.

File grew from 1574 → 1670 lines, well under the 6000-line cap.

## Dead ends
None. The strategy gave exact copy-paste templates and the proof shapes
worked verbatim — projections of `rk*_embed_order4` via the
right-nested `∧` accessors elaborated without complaint.

## Discovery
The embed `HasOrderGe4` certificates `rkRKF45_embed_order4` /
`rkDOPRI5_embed_order4` are stored as a single right-nested 8-tuple
`⟨order1, order2, order3a, order3b, order4a, order4b, order4c,
order4d⟩`, exactly matching the `HasOrderGe4` shape — no extra
projection is needed before feeding into `toGLM_hasOrderGe4` (cf. the
main-method case where `rk*_main_order5.1` first projects off the
`order5` wrapper).

## Suggested next approach
- Stretch target from the strategy (small RK methods missing
  `_toGLM_hasOrderGe1`): Lobatto IIIA/B/C 2/3-stage, Radau IA/IIA
  2-stage, SDIRK2. Each is a one-line wrapper around the existing
  `rk*_consistent` and the `toGLM_hasOrderGe1` bridge.
- After that batch, the natural §530 follow-up is RKF45 / DOPRI5
  `_toGLM_hasOrderGe5` for the **main** methods (already landed) plus
  any missing GLM convergence corollaries (combine `HasOrderGeN` with
  `toGLM_isStable` for `IsConvergent`).
- Continue avoiding the LMM `HasOrderGe3` heartbeat wall flagged in
  cycle 786.
