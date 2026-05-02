# Cycle 633 Results

## Worked on
Butcher §521 GLM stability-order infrastructure in
`OpenMath/GeneralLinearMethod.lean`.

## Approach
Added the complex lift `GeneralLinearMethod.qℂ`, the entrywise stability
defect `GeneralLinearMethod.stabilityDefect`, the order predicate
`GeneralLinearMethod.HasStabilityOrder`, and the zero-step sanity theorem
`GeneralLinearMethod.stabilityDefect_zero`.

## Result
SUCCESS. The zero-defect theorem is sorry-free: after `M(0) = Vℂ` and
`Complex.exp 0 = 1`, the proof reduces to the real preconsistency
hypothesis `V q = q` cast into `ℂ`.

Verified:
- `lake env lean OpenMath/GeneralLinearMethod.lean`
- `lake env lean OpenMath/RKAsGLM.lean`
- `lake env lean OpenMath/LMMAsGLM.lean`

## Dead ends
The first proof attempt unfolded the function equality without simplifying
`0 k`, so `rw [sub_eq_zero]` did not match. Adding `Pi.zero_apply` to the
initial simplification fixed the goal shape.

## Discovery
The global `dotProduct` name, not `Matrix.dotProduct`, is the one exposed
in this file's existing imports. Once `Matrix.mulVec`, `dotProduct`,
`Vℂ`, and `qℂ` are unfolded, `exact_mod_cast hVq k` closes the casted
complex summation goal directly.

## Suggested next approach
Proceed to the planned §521 milestone `LMM.toGLM_isAStable_iff`, using
the cycle 632 block-charpoly factorisation pattern. Do not add more
concrete LMM A-stability transports before the general bridge.
