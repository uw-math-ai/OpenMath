# Issue: Positivity bridge for interval integral of polynomial square

## Blocker
The only remaining `sorry` in `OpenMath/Legendre.lean` is:

```lean
lemma poly_eq_zero_of_intervalIntegral_sq_zero (p : ℝ[X])
    (h : ∫ x in (0 : ℝ)..1, (p.eval x) ^ 2 = 0) :
    p = 0
```

This is the final step needed to close `gaussLegendreNodes_of_B_double` after the node-polynomial, monic-normalization, orthogonality, and integral-bridge reductions are all in place.

## Context
Current reduction in `gaussLegendreNodes_of_B_double`:

- `nodePoly t` is monic of degree `s`
- the monic normalization `Pm` of the mapped shifted Legendre polynomial is monic of degree `s`
- `r := nodePoly t - Pm` has `r.natDegree < s`
- for all `q` with `q.natDegree < s`, `polyMomentN (2 * s) (r * q) = 0`
- specializing to `q = r` gives `polyMomentN (2 * s) (r * r) = 0`
- `polyMomentN_eq_intervalIntegral_of_natDegree_lt` rewrites this as
  `∫ x in (0:ℝ)..1, (r.eval x)^2 = 0`

So the only missing implication is:

```lean
∫ x in (0:ℝ)..1, (p.eval x)^2 = 0  ->  p = 0
```

## What was tried
- Proved the coefficientwise bridge
  `polyMomentN_eq_intervalIntegral_of_natDegree_lt`.
- Tried an `integral_eq_zero_iff_of_nonneg` route:
  rewrite the interval integral over `0..1` as a restricted integral on `Ioc 0 1`,
  use nonnegativity of squares, then show the support of `(fun x => (p.eval x)^2)`
  inside `Ioc 0 1` has positive measure unless `p = 0`.
- Reused the Aristotle-style finite-root idea:
  nonzero polynomials have finitely many roots, hence the zero set has measure zero.

## Possible solutions
- Finish the measure-theoretic route cleanly:
  use `intervalIntegral.integral_of_le`,
  `MeasureTheory.integral_eq_zero_iff_of_nonneg`,
  `MeasureTheory.ae_restrict_iff'`,
  finite roots -> measure-zero zero set,
  then conclude the complement in `Ioc 0 1` has positive measure.
- Alternatively use
  `intervalIntegral.integral_pos_iff_support_of_nonneg_ae`
  with `f x = (p.eval x)^2` and prove its support in `Ioc 0 1` is nonempty/positive whenever `p ≠ 0`.
- If needed, add a small helper lemma:
  a nonzero real polynomial cannot vanish on all of `Ioc 0 1`.
