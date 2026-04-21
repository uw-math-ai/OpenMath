# Issue: cycle 305 Padé defect low-order Vandermonde seam

## Blocker
The remaining blocker is `padeDefect_poly_coeff_lt`.

The leading coefficient theorem is now closed, but the low-degree coefficient proof still needs a reusable identity converting the general convolution coefficient of

`padeQ_poly p q * expTaylor_poly (p + q)`

into the closed form matching `padeP_poly_coeff`.

## Context
For `k < p + q + 1`, the product coefficient simplifies to a constant factorial factor times a finite sum of the shape

`∑ j ∈ range (k + 1), (q.choose j : ℂ) * (-1 : ℂ)^j * ((p + q - j).choose (k - j) : ℂ)`.

To finish `padeDefect_poly_coeff_lt`, this sum must equal `(p.choose k : ℂ)`.

The degree-`p+q+1` case no longer blocks:
- `alternating_choose_reciprocal_reflect` is live
- `padeQ_mul_expTaylor_coeff_succ` is live
- `padeDefect_poly_coeff_succ` is live

## What was tried
- Direct coefficient expansion with `Polynomial.coeff_mul`, `padeQ_poly_coeff`, and `expTaylor_poly_coeff`.
- Ad hoc range pruning plus endpoint handling.
- A coefficient-of-polynomial route using
  `((X + 1) + (-X))^q * (X + 1)^p`,
  aiming to read off the missing alternating-Vandermonde identity from the coefficient of `X^k`.

## Possible solutions
- Prove the alternating-Vandermonde identity as a standalone lemma by taking coefficients in
  `((X + 1) + (-X))^q * (X + 1)^p = (X + 1)^p`
  and reindexing with `sum_flip`.
- Alternatively, prove an equivalent intermediate identity first in the natural index coming from `add_pow`,
  then derive the reflected version used by `padeDefect_poly_coeff_lt`.
- Once that helper exists, `padeDefect_poly_coeff_lt` should follow by one coefficient calculation and `ring`, after which the divisibility/factorization stage can resume.
