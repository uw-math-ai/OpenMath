# Issue: Missing bridge from recursive shifted Legendre values to Mathlib polynomial facts

## Blocker
`OpenMath/Legendre.lean` contains two generic sorries:
- `ButcherTableau.gaussLegendre_B_double`
- `ButcherTableau.gaussLegendreNodes_of_B_double`

The first theorem needs polynomial degree/root machinery, but the file currently defines
`shiftedLegendreP` only as a recursive function `ℕ → ℝ → ℝ`. The repo does not yet prove that this
function agrees with Mathlib's `Polynomial.shiftedLegendre` after mapping coefficients to `ℝ`.

## Context
Current partial proof in `OpenMath/Legendre.lean` already reaches the fact that
`(Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff s ≠ 0`.
That is not enough on its own. The missing next step is a bridge of the form

```lean
shiftedLegendreP s x =
  Polynomial.aeval x (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s))
```

or an equivalent polynomial identity.

Without that bridge, `hGL : t.HasGaussLegendreNodes` cannot be converted into a root statement
about a degree-`s` polynomial, and the generic Gaussian quadrature argument stalls.

The converse theorem is even less supported: there is currently no theorem in the repo turning
`B(2*s)` into a characterization of the nodes as roots of `P_s^*`.

## What was tried
- Verified that `OpenMath/Legendre.lean` still compiles locally except for the two existing sorries.
- Submitted five Aristotle jobs:
  - `c247a02b-88ab-4acf-924c-9619789856ef` bridge lemma
  - `aa121cc8-b838-46a7-8ba3-4fc68e302165` degree/root helpers
  - `4d7d2176-98f7-4f51-be01-e92b830775bc` `gaussLegendre_B_double`
  - `5221522e-6cb1-4f71-8ac9-aae6833a91c2` converse theorem
  - `1ec30a4e-6838-4a05-bed0-ad1131fedd0f` bridge package
- Waited the required 30 minutes before checking results once.
- Aristotle did not return a proof that can be incorporated safely into the project.

## Possible solutions
- Prove the bridge lemma by induction on `s`, matching the base cases `0` and `1` and then using
  the three-term recurrence on both sides.
- After the bridge is available, prove a helper rewriting `HasGaussLegendreNodes` as membership in
  the `roots` multiset of the mapped polynomial.
- Use `Polynomial.natDegree_shiftedLegendre`, `Polynomial.card_roots'`, and the already-available
  nonzero leading coefficient to support the forward Gaussian quadrature proof.
- Treat the converse theorem separately if needed; it likely requires an additional uniqueness or
  orthogonality statement not yet present in the repo.
