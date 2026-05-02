# Cycle 629 Results

## Worked on
Butcher §521 RK-to-GLM A-stability transport for implicit midpoint:
`rkImplicitMidpoint_toGLM_isAStable` in `OpenMath/RKAsGLM.lean`.

## Approach
Followed the existing `rkImplicitEuler_toGLM_isAStable` bridge:
used `ButcherTableau.toGLM_isAStable_iff`, reduced the goal to the
RK scalar stability function bound, proved the closed-left-half-plane
denominator nonzero for `1 - z * (1/2)`, and applied
`rkImplicitMidpoint_aStable`.

Submitted the sorry-first scaffold to Aristotle as project
`3311fd3b-b752-4de0-9855-f79a183811fe`. A later status check still
showed the project queued, so there was no Aristotle result to
incorporate; the local proof was closed manually because the theorem
followed the existing one-stage template.

## Result
SUCCESS. `rkImplicitMidpoint_toGLM_isAStable` is landed sorry-free.
`lake env lean OpenMath/RKAsGLM.lean` and `lake build` both pass.

## Dead ends
The first stability-function agreement proof left the goal
`1 + z * (2 - z)⁻¹ * 2 = z * (2 - z)⁻¹ + (2 - z)⁻¹ * 2` after
`field_simp [hne']`. The fix was to add the equivalent nonzero
denominator fact `(2 : ℂ) - z ≠ 0`, allowing `field_simp` to clear
the inverse before `ring`.

The optional GL2 bridge was inspected but not attempted. Its existing
A-stability theorem is stated against `gl2StabilityFn`, so it needs a
separate 2-stage `stabilityFunction = gl2StabilityFn` agreement lemma
rather than the one-stage midpoint template.

## Discovery
For one-stage RK bridges whose scalar proof uses a rescaled denominator,
it is useful to provide both denominator forms to `field_simp`: the
`IsAStable1` denominator and the normalized denominator produced by
`stabilityFunction`.

## Suggested next approach
Next §521 cycle can target `gl2_toGLM_isAStable`, but should first prove
a standalone agreement lemma for
`rkGaussLegendre2.stabilityFunction z = gl2StabilityFn z` under
`gl2Denom z ≠ 0`.
