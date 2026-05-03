# Cycle 678 Results

## Worked on
File-size-cap split of `OpenMath/LMMAsGLM.lean`. The file was at 3062
lines (over the 3000-line hard cap), so per project rules and the
cycle-678 strategy the deliverable was to extract the §521
stability-matrix infrastructure into a new submodule.

## Approach
Created `OpenMath/LMMAsGLM/Stability.lean` containing:

1. The §521 stability-matrix block: lines 714–1816 of the original
   `LMMAsGLM.lean`, covering everything from
   `toGLM_stabilityMatrix_apply` through
   `bdf4_toGLM_not_isAStable`. This is the entry-projection /
   resolvent / block decomposition / rank-one decomposition / BDF
   specialisations / companion-form charpoly / `stabilityPolyPoly` /
   BDF iff bridge cluster.
2. The `LMM`-namespace rank-one charpoly identity
   `toGLM_stabilityMatrix_charpoly_rankOne` (originally lines
   2912–2938).
3. The post-`end LMM` concrete A-stability transports
   `backwardEuler_toGLM_isAStable`, `trapezoidalRule_toGLM_isAStable`,
   `bdf2_toGLM_isAStable` (originally lines 2942–3062).

These three blocks all depend on declarations from the §521 bundle.
The strategy's option (a) ("move them with the iff bridge") had to be
chosen for items (2) and (3) — option (b) was logically infeasible
because `Stability.lean` imports `LMMAsGLM` (so `LMMAsGLM` cannot
reference `Stability.lean` declarations).

The Matrix-namespace lemmas `det_add_vecMulVec` and
`charpoly_add_vecMulVec` (lines 2724–2906 of the original) stay in
the main file: they have no dependency on the §521 bundle, and
`Stability.lean` can use them through its `import OpenMath.LMMAsGLM`.

`StabilityCharpoly.lean` was updated to also
`import OpenMath.LMMAsGLM.Stability`, since it consumes
`toGLM_rankOneRow`, `toGLM_rankOneColumn`, `toGLM_V_active_lift`, and
`toGLM_stabilityMatrixPY` from the moved bundle.

No declaration was renamed, restated, or generalised — pure
copy/paste/reorganise.

## Result
SUCCESS.

Final line counts (all under cap):
- `OpenMath/LMMAsGLM.lean`: 1804 lines (was 3062).
- `OpenMath/LMMAsGLM/Stability.lean`: 1279 lines (new).
- `OpenMath/LMMAsGLM/StabilityCharpoly.lean`: 949 lines (was 948,
  plus one import line).

Verification (all green):
- `lake build OpenMath.LMMAsGLM` ✔ 113s
- `lake build OpenMath.LMMAsGLM.Stability` ✔ 100s
- `lake build OpenMath.LMMAsGLM.StabilityCharpoly` ✔ 123s
- Full `lake build` ✔ (no errors, only pre-existing
  `unusedSimpArgs` linter warnings in `OpenMath/BDF.lean`)

## Dead ends
None. The split was straightforward once the import direction was
nailed down. The strategy text suggested option (b) — keep the
charpoly-rankOne and the transports in the main file — was viable
because "the main file ... now imports `Stability.lean`-content
transitively because `Stability.lean` imports `LMMAsGLM`". That
reasoning is wrong (imports are not bidirectional), so option (a)
was forced.

## Discovery
- Only two `OpenMath/*.lean` files referenced any of the moved
  declarations: `LMMAsGLM.lean` itself (the source) and
  `LMMAsGLM/StabilityCharpoly.lean`. So the wiring update was just
  one new import line in `StabilityCharpoly.lean`.
- The §521 main block (714–1816) is internally self-contained: no
  forward reference into the post-§521 remainder, and the post-§521
  remainder (stage map / consistent / stable / convergent /
  Nordsieck / stability defect / Matrix-namespace det+charpoly
  lemmas, lines 1818–2906 of the original) has zero references to
  the moved bundle. That made the line-range extraction clean.
- The `Stability.lean` module reuses the existing `Matrix` namespace
  helpers `det_add_vecMulVec` and `charpoly_add_vecMulVec` (which
  remain in `LMMAsGLM.lean`) via the import.

## Suggested next approach
Resume the strategy's planned next deliverable now that the file is
back under cap: combine the cycle 676 column closed forms into a
closed form for `toGLM_stabilityCharpolyRowF`, then assemble the
`X^s` factorisation of `toGLM_stabilityMatrix_charpoly_explicit`,
then the general-`s` LMM-side iff bridge `LMM.toGLM_isAStable_iff`.

All of that should now live in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean` (or a further submodule
of `LMMAsGLM/`), not in `OpenMath/LMMAsGLM.lean`.
