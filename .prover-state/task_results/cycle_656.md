# Cycle 656 Results

## Worked on
Butcher §521 — Lobatto IIIB 2-stage GLM A-stability transport.
Two new theorems in `OpenMath/RKAsGLM.lean`:
- `rkLobattoIIIB2_stabilityFunction_eq`
- `rkLobattoIIIB2_toGLM_isAStable`

## Approach
Followed the cycle 655 IIIA pattern verbatim, swapping the matrix shape:
- IIIA: `!![1, 0; -(z*(1/2)), 1 - z*(1/2)]`
- IIIB: `!![1 - z*(1/2), 0; -(z*(1/2)), 1]`

Both are lower-triangular with determinant `1 - z*(1/2)`, so the
`hne1`, `hD`, and `hdet` lemmas are identical. After `Matrix.inv_def`,
`Matrix.adjugate_fin_two_of`, and unfolding the IIIA stability
function (which IIIB shares — `lobIIIB_aStable` is literally
`lobIIIA_aStable`), `push_cast; field_simp [hne1, hD]; ring` closes
the bridge.

The A-stability transport then reuses
`ButcherTableau.toGLM_isAStable_iff` and `lobIIIB_aStable`.

## Result
SUCCESS.

`lake env lean OpenMath/RKAsGLM.lean` — only pre-existing unused-simp
warnings (lines 303, 358, 379), no errors at the new proofs.
`lake build` — completes successfully (8087 jobs).

Also added the missing `import OpenMath.LobattoIIIB` at the top of
`OpenMath/RKAsGLM.lean` (the IIIB module had not been imported by
RKAsGLM previously).

## Dead ends
None. The strategy's structural prediction matched exactly.

## Discovery
The IIIB stability bridge is even cleaner than IIIA because the
second-row diagonal of `1 - z•A` is just `1` instead of `1 - z/2`,
which `field_simp` handles trivially without needing additional
hypotheses. The IIIA-pattern hypothesis set `[hne1, hD]` was sufficient
unchanged.

## Suggested next approach
The 3-stage Lobatto methods (IIIA / IIIC) are the natural next §521
RK-side candidates. Cycle 656's strategy promotion already updated
`plan.md`'s Current Target to point at `rkLobattoIIIA3` /
`rkLobattoIIIC3` using the cycle 653 / 654 three-certificate split for
the 3×3 adjugate determinant.

Before scaffolding the 3-stage transports, the next planner cycle
should:
1. Confirm the classical stability functions and A-stability lemma
   names exist in `OpenMath/LobattoIIIA3.lean` /
   `OpenMath/LobattoIIIC3.lean`.
2. Decide whether the 3×3 determinant cross-terms produce
   `Real.sqrt`-style obstructions like Radau IIA 3-stage / GL3 (cycles
   653, 654) — if so, plan the three-certificate split shape up front.

If the Lobatto 3-stage transports stall on a `sqrt`-term obstruction
analogous to the one tracked in
`.prover-state/issues/radau_gl3_glm_aStable_sqrt_bridge.md`, fall back
to the LMM-side iff bridge (`LMM.toGLM_isAStable_iff`) tracked in
`.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md`.
