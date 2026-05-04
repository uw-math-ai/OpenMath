# Cycle 796 Results

## Worked on

§530 GLM-order witness ladder: Tier A (16 missing
`_toGLM_hasOrderGe1` rungs) and Tier B (7 intermediate Radau3 / SDIRK3
projections from headline order certificates).

All work in `OpenMath/RKAsGLM.lean`, plug-and-play term-mode
one-liners over the existing tableau-side bridges
`toGLM_hasOrderGe{1..5}`.

## Approach

Followed strategy.md verbatim. Confirmed via Grep that all 16
consistency lemmas (`<M>_consistent`) named in the strategy exist in
tracked code (one is in `StiffEquations.lean:262`, the rest in the
files the strategy listed). Verified the right-nested `∧` accessor
pattern by reading the existing `rkRadauIA2_toGLM_hasOrderGe2`
projection (which uses `⟨h.1, h.2.1⟩` against `HasOrderGe3`) and the
definitions of `HasOrderGe1..HasOrderGe5` in `RungeKutta.lean`:

* `HasOrderGe5 = HasOrderGe4 ∧ order5a ∧ ... ∧ order5i`,
* `HasOrderGe4 = order1 ∧ order2 ∧ order3a ∧ order3b ∧ order4a ∧ ... ∧ order4d`,
* `HasOrderGe3 = order1 ∧ order2 ∧ order3a ∧ order3b`,
* `HasOrderGe2 = order1 ∧ order2`,
* `HasOrderGe1 = order1`.

So from a `HasOrderGe5` certificate `h5`:
* `h5.1 : HasOrderGe4`,
* `h5.1.1 = order1`, `h5.1.2.1 = order2`,
* `h5.1.2.2.1 = order3a`, `h5.1.2.2.2.1 = order3b`.

This matches exactly the cycle 794 pattern.

## Result

SUCCESS. All 23 theorems landed and `lake env lean
OpenMath/RKAsGLM.lean` exits 0 with no `sorry` and no errors. Only
pre-existing `unusedSimpArgs` warnings and the prior cycles'
`simprocCore` PANIC traces (unchanged) appear — the strategy
explicitly accepts that noise.

### Tier A (16 theorems, all `<M>.toGLM_hasOrderGe1 <M>_consistent`)

1. `rkHeun_toGLM_hasOrderGe1`
2. `rkSDIRK2_toGLM_hasOrderGe1`
3. `rkSDIRK3_toGLM_hasOrderGe1`
4. `rkMidpoint_toGLM_hasOrderGe1`
5. `rkRK4_toGLM_hasOrderGe1`
6. `rkGaussLegendre2_toGLM_hasOrderGe1`
7. `rkGaussLegendre3_toGLM_hasOrderGe1`
8. `rkRadauIA2_toGLM_hasOrderGe1`
9. `rkRadauIIA2_toGLM_hasOrderGe1`
10. `rkRadauIA3_toGLM_hasOrderGe1`
11. `rkRadauIIA3_toGLM_hasOrderGe1`
12. `rkLobattoIIIA2_toGLM_hasOrderGe1`
13. `rkLobattoIIIC2_toGLM_hasOrderGe1`
14. `rkLobattoIIIA3_toGLM_hasOrderGe1`
15. `rkLobattoIIIB3_toGLM_hasOrderGe1`
16. `rkLobattoIIIC3_toGLM_hasOrderGe1`

(`rkLobattoIIIB2` correctly skipped — strategy notes it is not
consistent.)

### Tier B (7 projections)

17. `rkSDIRK3_toGLM_hasOrderGe2` (from `rkSDIRK3_order3`)
18. `rkRadauIA3_toGLM_hasOrderGe2` (from `rkRadauIA3_order5`)
19. `rkRadauIA3_toGLM_hasOrderGe3`
20. `rkRadauIA3_toGLM_hasOrderGe4`
21. `rkRadauIIA3_toGLM_hasOrderGe2` (from `rkRadauIIA3_order5`)
22. `rkRadauIIA3_toGLM_hasOrderGe3`
23. `rkRadauIIA3_toGLM_hasOrderGe4`

## File size

`OpenMath/RKAsGLM.lean` grew from 1670 to 1831 lines (+161). Well
under the 6000-line hard cap.

## Dead ends

None. Every theorem closed in term mode on the first attempt; no
edits to the bridges, no tactic-mode workarounds, no extra imports.

## Discovery

The right-nested `∧` accessor recipe handles all of
`HasOrderGe5 → HasOrderGe{2,3,4}` cleanly without any unfolding
hand-holding — the elaborator unfolds `HasOrderGe5` automatically
when given the projection chain. This is the same shape as cycle
794 already validated for `HasOrderGe5`, and it now also works
end-to-end for `HasOrderGe2`/`HasOrderGe3`/`HasOrderGe4` projections
out of an `HasOrderGe5` certificate.

## Suggested next approach

Many `_toGLM_hasOrderGe1` rungs for the embedded-pair embed methods
already exist (cycle 794). Two complementary gaps the planner could
target next cycle:

1. **`mainMethod_toGLM_hasOrderGe1` for HeunEuler/BS3(2)/RKF45/DOPRI5**
   if it is not already present (verify via Grep first); these are
   pure plug-and-play wrappers over `<M>_consistent.main_consistent`.
2. **HasOrderGe5 / HasOrderGe6 ladder rungs for Lobatto IIIA/IIIB/IIIC
   3-stage** — the order-4 (resp. order-6) certificates exist, and
   the projection pattern landed this cycle generalises.
3. Tier-B-style projections for the **embedded-pair main methods**
   (`rkBS32_mainMethod_toGLM_hasOrderGe1` and friends) where only the
   top-rung witness is currently in tracked code.

The §530 LMM-side ladder remains capped by the 200000-heartbeat
ceiling on `s ≥ 5`; do not retry without new infrastructure.
