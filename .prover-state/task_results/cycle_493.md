# Cycle 493 Results

## Worked on
Butcher §45 one-leg methods and scalar G-stability:

- `OpenMath/OneLegMethods.lean`
- `OpenMath/GStability.lean`
- root imports in `OpenMath.lean`
- `plan.md` rotation to §334 Fehlberg 4(5)

## Approach
Started with the required sorry-first scaffold for the two new modules and
verified it compiled. Submitted five Aristotle jobs after the scaffold:

- `0195b1e1-ac63-45c8-914c-8f5aec22b910`: live `OneLegMethods.lean`
- `5e6b73a0-d13f-453e-8d88-b462854d2c92`: live `GStability.lean`
- `b7aa4a39-1324-4e37-8460-b493d7a91ecb`: scratch one-leg round trips
- `bec441bc-d053-4d6b-8348-71741d598686`: scratch `gNormSq` nonnegativity
- `b53ca824-2b16-4a67-87f1-f72b6e071524`: scratch trapezoid energy algebra

Slept for the required 30 minutes, listed Aristotle projects once, and
extracted all five cycle-493 results.

## Result
SUCCESS.

`OpenMath/OneLegMethods.lean` is sorry-free with `OneLegMethod`,
`OneLegMethod.toLMM`, `LMM.toOneLeg`, both coefficient round trips, and
`OneLegMethod.trapezoid_toLMM_eq_lmm_trapezoid`.

`OpenMath/GStability.lean` is sorry-free with `gNormSq`,
`OneLegMethod.IsGStable`, and
`OneLegMethod.trapezoid_isGStable_with_G_one`. The trapezoid proof uses the
plain `Matrix.dotProduct`/`Matrix.mulVec` shape, unfolds the `Fin 1`/`Fin 2`
scalar data, proves the energy identity, and applies the scalar monotonicity
assumption for contractivity.

`OpenMath.lean` imports both new modules. `plan.md` marks §450 and §451
complete, leaves §452-§454 open, and promotes §334 Fehlberg 4(5) into Current
Target.

## Dead ends
Aristotle results were useful as hints but not directly transplantable in full:
some outputs created local stub dependencies or added `import Mathlib`.
The round-trip proofs reduced to `rfl`; the G-stability proof needed a manual
live-import proof.

`nlinarith` did not close the trapezoid energy identity directly from
`-Y 0 + Y 1 = h * F`; it needed an explicit rewrite of the correction term as
`2 * (Y 1 - Y 0) * (1 / 2 * Y 0 + 1 / 2 * Y 1)`.

## Discovery
For scalar `Fin 1` G-norm goals, `simp` with `dotProduct`, `Matrix.mulVec`,
`Fin.sum_univ_two`, and the local definitions reduces the matrix expressions
cleanly. Rational cleanup works best as a separate `norm_num at ...` step
after `simp`.

The existing trapezoidal LMM name is the root-level `trapezoidalRule`.

## Suggested next approach
Proceed with the promoted §334 Fehlberg 4(5) target in
`OpenMath/EmbeddedRK.lean`. Mirror the existing Heun-Euler and
Bogacki-Shampine embedded-pair style, and isolate any heavy RKF45 rational
order-condition arithmetic into small private helpers if direct `norm_num`
proofs become slow.
