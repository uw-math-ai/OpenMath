# Issue: AM8 vector residual port needs a dedicated tenth-order Taylor ladder

## Status
RESOLVED (cycle 455). The AM8 vector quantitative convergence chain has
been closed in `OpenMath/LMMAM8VectorConvergence.lean`, including the
three tenth-order vector Taylor helpers
(`iteratedDeriv_ten_bounded_on_Icc_vec`, `y_tenth_order_taylor_remainder_vec`,
`derivY_ninth_order_taylor_remainder_vec`) and the headline
`LMM.am8Vec_global_error_bound`. Resolution acknowledged in cycle 466
while reusing the public AM7 ninth-order helpers for the AB8 scalar
chain.

## Blocker
The AM8 vector convergence file could not be closed safely in this cycle.  A
direct mechanical rewrite of the AM7 vector residual section to AM8 is not
kernel-safe: the one-step AM8 vector norm recurrence can be ported, but the
pointwise residual proof needs a clean tenth-order vector Taylor helper
(`y_tenth_order_taylor_remainder_vec`) and a ninth-order derivative helper
(`derivY_ninth_order_taylor_remainder_vec`) before the AM8 ten-term residual
split can be made reliable.

## Context
AM8 scalar uses private scalar helpers:

```lean
iteratedDeriv_ten_bounded_on_Icc
y_tenth_order_taylor_remainder
derivY_ninth_order_taylor_remainder
```

AM7 vector had only private eighth/ninth-order vector helpers.  This cycle
promoted the AM7 vector helpers to public so the next AM8 vector attempt can
reuse them instead of duplicating the lower ladder:

```lean
iteratedDeriv_nine_bounded_on_Icc_vec
am7Vec_y_eighth_order_taylor_remainder_vec
y_ninth_order_taylor_remainder_vec
derivY_eighth_order_taylor_remainder_vec
```

## What was tried
A scaffold with the five AM8 vector target sorries was submitted to Aristotle.
I also attempted a mechanical AM7-vector to AM8-vector rewrite of the live
file.  That rewrite produced fragile residual algebra and bad scalar/vector
coercions around the ten-term residual identity, so it was discarded rather
than leaving a broken tracked module.

## Possible solutions
Start the next AM8 vector cycle by proving only the three tenth-order vector
Taylor helpers, using the newly public ninth-order helpers:

1. `iteratedDeriv_ten_bounded_on_Icc_vec`
2. `y_tenth_order_taylor_remainder_vec`
3. `derivY_ninth_order_taylor_remainder_vec`

After those compile, port the AM8 scalar residual split to vector form in
small pieces: algebra identity, bound identity, ten-term triangle, and combine
lemma.  Avoid mechanical global rewrites; the scalar `*` to vector `•`
conversion is the error-prone part.
