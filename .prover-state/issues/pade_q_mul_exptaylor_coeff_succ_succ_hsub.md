# Issue: product-side degree-(p+q+2) coefficient subtraction still open

## Blocker
The remaining sorry in `OpenMath/PadeAsymptotics.lean` is the local proof
`hsub` inside:

```lean
PadeAsymptotics.padeQ_mul_expTaylor_coeff_succ_succ
```

This is now the only remaining sorry in `OpenMath/PadeAsymptotics.lean`, and it
blocks a sorry-free path into the downstream second-order Padé expansion.

## Context
The target theorem already has:

- the convolution-support reduction `hconv` proved
- the downstream defect theorem
  `PadeAsymptotics.padeDefect_poly_coeff_succ_succ` closed
- the exact reflected-sum pieces needed later:
  - `hsplit`
  - `hsum2`
  - `hcoeff`

The open local statement is:

```lean
(∑ j ∈ Finset.Icc 2 q,
  (padeQ_poly p q).coeff j *
    (expTaylor_poly (p + q)).coeff (p + q + 2 - j)) =
∑ j ∈ Finset.range (q + 1),
  (q.choose j : ℂ) * (-1 : ℂ) ^ j / (p + q + 2 - j : ℂ) /
    (p + q + 1 - j : ℂ) / (((p + q).factorial : ℂ)) -
  1 / (((p + q + 2).factorial : ℂ)) +
  ((q : ℂ) / (p + q : ℂ)) / (((p + q + 1).factorial : ℂ))
```

## What was tried
- Reused the degree-`p+q+1` proof pattern:
  - converted `Finset.Icc 2 q` to `Finset.Ico 2 (q+1)`
  - set up the pointwise coefficient formula for `j ∈ Ico 2 (q+1)`
- Verified in scratch that the two-step factorial identity is provable:
  `((p+q+2-j)!) = (p+q+2-j)(p+q+1-j)(p+q-j)!`
- Verified in scratch that the reflected-sum normalization used later for
  `hsum2` is correct
- Verified in scratch that the defect-theorem assembly works once `hsub` is
  available

## Possible solutions
- Keep the current `hconv` proof and finish `hsub` with a separate decomposition:
  1. pointwise formula on `Finset.Ico 2 (q+1)`
  2. `q = 0` handled as its own branch
  3. `Finset.sum_Ico_eq_sub _ hq` for the `q > 0` branch
  4. a dedicated `hrange2` lemma for the `j = 0, 1` subtraction
- Avoid heavy `simp` on the `Finset.range 2` expression; instead prove:
  - `hsmall0` for the `j = 0` term
  - `hsmall1` for the `j = 1` term
  - then assemble `hrange2` from those two lemmas
- Do not try one large `ring`/`field_simp` proof for the whole `hsub`; the
  localized scratch experiments suggest the heartbeats are spent in the mixed
  `range 2` normalization rather than in the reflected-sum algebra itself.
