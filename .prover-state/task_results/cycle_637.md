# Cycle 637 Results

## Worked on
Section 521 LMM-as-GLM stability-defect surface in
`OpenMath/LMMAsGLM.lean`.

## Approach
Followed the requested sorry-first workflow:

1. Added `LMM.toGLM_stabilityDefect_apply` immediately after
   `toGLM_V_nordsieckQ_eq` with a `sorry` body and verified the file
   elaborated.
2. Closed the row formula by unfolding `GeneralLinearMethod.stabilityDefect`,
   `Matrix.mulVec`, and `dotProduct` through `simp`.
3. Since the headline landed quickly, added the optional
   `LMM.toGLM_stabilityDefect_natAdd` corollary sorry-first and closed it by
   rewriting with the row formula and `toGLM_qℂ_nordsieckQ_natAdd`, then
   `ring`.
4. Added a short cycle 637 note to the recent Section 521 history in
   `plan.md`.

Aristotle was not used because the first manual tactic path closed the
headline theorem cleanly.

## Result
SUCCESS. Landed:

- `LMM.toGLM_stabilityDefect_apply`
- `LMM.toGLM_stabilityDefect_natAdd`

Both are sorry-free.

Verified:

- `lake env lean OpenMath/LMMAsGLM.lean`
- `lake env lean OpenMath/RKAsGLM.lean`
- `lake env lean OpenMath/GeneralLinearMethod.lean`

All three completed successfully.

## Dead ends
None. The proposed `simp` proof for the row formula was sufficient. The only
minor adjustment was adding a no-op use of `hm` in the proof body so the
uniform consistency hypothesis remains named without triggering the unused
variable linter.

## Discovery
The LMM row formula is fully tautological once the GLM defect is unfolded; no
`nordsieckQ_castAdd` or `nordsieckQ_natAdd` reindexing is needed for the
general row formula. The natAdd specialization uses the existing `qℂ` lift
cleanly under the `Fin.cast`/`Fin.natAdd` index shape.

## Suggested next approach
Use `LMM.toGLM_stabilityDefect_apply` as the default unfolding surface for
future LMM `HasStabilityOrder` work. The general LMM-side A-stability iff
bridge still needs the planned general-`s` characteristic-polynomial
factorisation before it should be reopened.
