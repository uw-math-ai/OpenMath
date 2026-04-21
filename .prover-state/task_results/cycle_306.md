# Cycle 306 Results

## Worked on
- `OpenMath/PadeAsymptotics.lean`
- Added `alternating_vandermonde_choose`
- Closed:
  - `padeDefect_poly_coeff_lt`
  - `padeDefect_poly_sub_leading_X_pow_dvd`
  - `padeDefect_sub_leading_factorization`
  - `padeR_exp_neg_leading_term`

## Approach
- Added a standalone alternating-Vandermonde helper by taking coefficients of
  `∑ j, C(q,j) (-X)^j (X+1)^(p+q-j)` and identifying that polynomial with
  `(((-X) + (X + 1))^q) * (X + 1)^p = (X + 1)^p`.
- Proved `padeDefect_poly_coeff_lt` by expanding the coefficient of
  `padeQ_poly p q * expTaylor_poly (p + q)` as a finite convolution over
  `j = 0, ..., k`, converting the factorial ratio to a binomial coefficient,
  and collapsing the sum with `alternating_vandermonde_choose`.
- Proved the divisibility step with `Polynomial.X_pow_dvd_iff`, using
  `padeDefect_poly_coeff_lt` for degrees `< p + q + 1` and
  `padeDefect_poly_coeff_succ` at degree `p + q + 1`.
- Proved the function-level defect factorization by evaluating the quotient
  polynomial from the divisibility theorem.
- Closed `padeR_exp_neg_leading_term` with the direct existential witness
  `if z = 0 then 0 else lhs / z^(n+d+2)`.

## Result
- SUCCESS
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeAsymptotics.lean`
  succeeds with no remaining `sorry`s.

## Dead ends
- Importing `OpenMath.PadeUniqueness` looked attractive because its proof shape
  matches this seam, but that module does not currently build in this checkout,
  so I dropped that path and kept the proof fully local.
- The helper proof did not simplify from the raw coefficient-of-product form with
  a single `simp`; it needed an explicit per-term coefficient calculation for
  `C(q.choose j) * (-X)^j * (X+1)^(p+q-j)`.

## Discovery
- The real asymptotic content is now captured cleanly by
  `alternating_vandermonde_choose`,
  `padeDefect_poly_coeff_lt`,
  `padeDefect_poly_sub_leading_X_pow_dvd`, and
  `padeDefect_sub_leading_factorization`.
- The current statement of `padeR_exp_neg_leading_term` is a global existential
  statement, so it can be closed directly by quotienting by `z^(n+d+2)` away
  from zero. If a later cycle needs a stronger constructive/local witness, it
  should build that from the new defect factorization lemmas rather than from
  the bare existential theorem.
- Aristotle batch after the required 30 minute wait:
  - `d3493ba8-e9e6-497c-a75f-14d6629fbb8a` (`alternating_vandermonde_choose`): `IN_PROGRESS`
  - `6a782b6a-adaf-4550-b880-cb26a3136e58` (`padeDefect_poly_coeff_lt`): `COMPLETE_WITH_ERRORS`
  - `674451e1-0e44-4e80-82e9-e6478aeb793e` (`padeDefect_poly_sub_leading_X_pow_dvd`): `QUEUED`
  - `f9b28a52-7a57-4afd-9e4d-18fa444dc1ee` (`padeDefect_sub_leading_factorization`): `QUEUED`
  - `412ad309-4e6c-4def-a415-58899ec57066` (`padeR_exp_neg_leading_term`): `QUEUED`
- The only extracted Aristotle artifact was the partial
  `padeDefect_poly_coeff_lt` result in
  `.prover-state/aristotle/cycle_306/padeDefect_poly_coeff_lt/`; it identified
  the same convolution route but was not directly incorporable.

## Suggested next approach
- If the planner wants a more informative final asymptotic witness for
  `padeR_exp_neg_leading_term`, strengthen the theorem statement so the witness
  is assembled from the new defect factorization plus the existing
  `expTaylor_exp_neg_leading_term` remainder theorem, rather than relying on the
  generic existential quotient trick.
