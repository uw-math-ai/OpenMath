# Issue: Theorem 351B needs stronger hypotheses

## Blocker
The cycle 103 planner statement for Theorem 351B is not derivable from the stated Lean hypotheses.

The proposed assumption

`∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0 → ‖N.eval z / D.eval z‖ ≤ 1`

only bounds the rational function away from poles. At a point where `D.eval z = 0`, the implication is vacuous, so it cannot imply that all poles lie in the open right half-plane.

## Context
The intended theorem was:

`A-stable iff poles in RHP and E(y) ≥ 0 on the imaginary axis`

for `R(z) = N(z)/D(z)`.

For arbitrary polynomials `N, D`, the sufficiency direction also needs more than just boundary control on the imaginary axis:

- at least an explicit nonvanishing hypothesis on `Re z ≤ 0`
- and a growth/degree condition so the rational function is controlled at infinity

These extra assumptions are automatic for actual RK stability functions, but they are not present in the planner’s polynomial-only statement.

## What was tried
- Checked existing A-stability definitions in `OpenMath/RungeKutta.lean` and related files.
- Verified that all current RK A-stability proofs separately prove denominator nonvanishing on `Re z ≤ 0`.
- Reviewed the maximum-modulus infrastructure in `OpenMath/MultistepMethods.lean`.
- Attempted to align the planner statement with the existing API, and found the pole-location implication unprovable from the given premise.

## Possible solutions
- Restate 351B for rational functions with explicit hypotheses:
  `((∀ z, z.re ≤ 0 → D.eval z ≠ 0) ∧ (∀ z, z.re ≤ 0 → ‖N.eval z / D.eval z‖ ≤ 1)) ↔ ...`
- Or restate it for actual RK stability functions, where denominator nonvanishing and degree bounds come from the tableau construction.
- Prove the necessity direction first:
  poles in RHP/nonvanishing on `Re z ≤ 0` plus A-stability imply `E(y) ≥ 0`.
- For sufficiency, reuse `Complex.norm_le_of_forall_mem_frontier_norm_le` on bounded left-half-disk truncations together with a separate lemma controlling the circle-at-infinity term for RK stability functions.
