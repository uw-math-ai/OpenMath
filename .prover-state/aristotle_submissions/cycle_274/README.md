# Cycle 274 Aristotle submission

## Target

Butcher §342 (342d) — norm-square integral of shifted Legendre polynomials on `[0, 1]`:

```
∫₀¹ (P_n^*(x))^2 dx = 1 / (2n + 1)
```

## File

`342d_norm_square.lean` — standalone, with cycle 271–273 prerequisites
exposed as named axioms so Aristotle can cite them directly without
re-proving.

## Strategy

Rodrigues + iterated integration by parts × `n` + Beta function identity
`∫₀¹ x^n (1-x)^n dx = (n!)^2 / (2n+1)!`. See the file's docstring for
the full sketch.

## Risk

The proof involves three layers of nontrivial reasoning:
1. Iterated IBP `n` times (likely an induction on `n`).
2. Boundary-term vanishing (Leibniz + factor-counting argument).
3. The `n`-th derivative of `P_n^*` as a constant `(2n)!/n!`, plus the
   Beta integral.

Aristotle has access to the full Mathlib API, including
`Polynomial.factorial_mul_shiftedLegendre_eq`,
`Polynomial.coeff_shiftedLegendre`, and the complex `betaIntegral`
infrastructure. The IBP step is `intervalIntegral.integral_mul_deriv_eq_deriv_mul`.

## Cycle reference

Submitted in cycle 274 as fallback per strategy §B.P3 (manual P3 deferred
because Mathlib's Beta integral is complex-valued and the iterated IBP
machinery requires significant new helpers).
