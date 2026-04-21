# Issue: cycle 304 Padé defect reflection and low-order vanishing seam

## Blocker
The remaining blocker is the exact coefficient/divisibility seam for

`padeP p q z - padeQ p q z * expTaylor (p + q) z`.

Cycle 304 now has the local polynomial/evaluation infrastructure in
`OpenMath/PadeAsymptotics.lean`, including:

- `expTaylor_poly_eval`
- `padeP_poly_eval`
- `padeQ_poly_eval`
- `expTaylor_poly_coeff`
- `padeP_poly_coeff`
- `padeQ_poly_coeff`
- `alternating_choose_reciprocal`

What is still missing is:

1. `padeDefect_poly_coeff_lt`
2. `padeDefect_poly_coeff_succ`
3. `padeDefect_poly_sub_leading_X_pow_dvd`

## Context
The exact leading coefficient proof nearly lands from the new helper lemmas, but
the live sticking point is the convolution/range conversion:

- the coefficient of degree `p + q + 1` in
  `padeQ_poly p q * expTaylor_poly (p + q)`
  naturally appears as a sum over `Finset.Icc 1 q`
- the usable closed form is a reflected alternating reciprocal sum
  matching `alternating_choose_reciprocal`
- the low-order vanishing theorem is still absent, so even after the leading
  coefficient is isolated, the `X^(p+q+2)` divisibility theorem is not yet
  available

An Aristotle `COMPLETE` bundle for `padeDefect_poly_coeff_succ`
(`6cfe2278-15ee-4641-a9c4-ca0adc67be17`) gave a compatible proof shape, but its
transplant still needs repair at the finite-sum conversion step in the live file.

## What was tried
- Created `OpenMath/PadeAsymptotics.lean` and kept the coefficient algebra out of
  `PadeOrderStars.lean`.
- Proved the polynomial/evaluation coefficient bridges listed above in live code.
- Proved `alternating_choose_reciprocal` in live code by induction, using
  `Finset.sum_choose_succ_mul`.
- Submitted a focused 5-job Aristotle batch on:
  - coefficient bridges
  - alternating reciprocal identity
  - low-order vanishing
  - exact leading coefficient
  - divisibility/factorization
- Waited 30 minutes and refreshed once only.
- Single refresh results:
  - `03a369e4...` coefficient bridges: `IN_PROGRESS`
  - `3f3863a9...` alternating reciprocal identity: `COMPLETE_WITH_ERRORS`
  - `ad40a2b9...` low-order vanishing: `IN_PROGRESS`
  - `6cfe2278...` exact leading coefficient: `COMPLETE`
  - `d80a9a07...` divisibility/factorization: `IN_PROGRESS`
- Inspected the `COMPLETE` and `COMPLETE_WITH_ERRORS` bundles.
  The alternating bundle was rejected because it rebuilt a stub `OpenMath/Pade.lean`.
  The exact-leading-coefficient bundle had a usable proof shape, but the direct
  transplant did not compile without repair.

## Possible solutions
- Prove a reflected corollary of `alternating_choose_reciprocal`:

  `∑ i in range (q+1), (-1)^i * choose q i / (p+q+1-i) = (-1)^q * p! q! / (p+q+1)!`

  This should discharge the exact coefficient theorem cleanly.
- For `padeDefect_poly_coeff_lt`, avoid the broken old `PadeUniqueness` proof and
  prove the low-order coefficients directly from the new coefficient lemmas plus a
  Vandermonde-style finite-sum identity.
- Once `padeDefect_poly_coeff_lt` and `padeDefect_poly_coeff_succ` are both live,
  prove `padeDefect_poly_sub_leading_X_pow_dvd` using
  `Polynomial.X_pow_dvd_iff`.
