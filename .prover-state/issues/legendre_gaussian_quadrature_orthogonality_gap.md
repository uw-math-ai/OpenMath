# Issue: Legendre Gaussian quadrature needs a real polynomial bridge and orthogonality lemma

## Blocker
`OpenMath/Legendre.lean` still has two remaining sorries:
- `ButcherTableau.gaussLegendre_B_double`
- `ButcherTableau.gaussLegendreNodes_of_B_double`

Both theorems need a bridge from the recursive function
`shiftedLegendreP : ℕ → ℝ → ℝ`
to Mathlib's polynomial
`Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)`,
plus an orthogonality statement on `[0,1]` for the degree-`s` shifted Legendre polynomial.

## Context
Current file:
- `OpenMath/Legendre.lean:184`
- `OpenMath/Legendre.lean:232`

Existing local facts are not enough:
- `Polynomial.coeff_shiftedLegendre`
- `Polynomial.natDegree_shiftedLegendre`
- `Polynomial.factorial_mul_shiftedLegendre_eq`
- `Polynomial.shiftedLegendre_eval_symm`

The missing chain is:
1. identify `shiftedLegendreP s x` with evaluation of the mapped Mathlib polynomial
2. reformulate `HasGaussLegendreNodes` in terms of polynomial roots/evaluation
3. use Euclidean division of monomials by the degree-`s` shifted Legendre polynomial
4. prove orthogonality of the polynomial term on `[0,1]`
5. combine with `SatisfiesB s` / `SatisfiesB (2*s)` to prove the two Gaussian quadrature directions

## What was tried
- Checked the failing CI run `24641918796`; it was a stale workflow failure in `lean-action`'s Mathlib cache fetch, not a Lean error.
- Confirmed `origin/main` already contains the CI fix (`d27e9bc433`, `use-mathlib-cache: false`).
- Re-read `OpenMath/Legendre.lean` and previous Aristotle output from cycle 163.
- Reused the useful observation from prior Aristotle output that a direct bridge theorem is plausible, but did not import that file verbatim because it was proved in a standalone environment with `maxHeartbeats 800000`, which violates project rules.
- Wrote a new cycle-165 Aristotle batch with five focused scratch files:
  - `01_shifted_legendre_bridge.lean`
  - `02_shifted_legendre_root_bridge.lean`
  - `03_shifted_legendre_division.lean`
  - `04_shifted_legendre_orthogonality.lean`
  - `05_gauss_legendre_reduction.lean`
- Verified each scratch file compiles with `sorry`.

## Possible solutions
- First prove the bridge theorem in-project, without exceeding `maxHeartbeats 200000`.
- Then prove a root reformulation lemma:
  `t.HasGaussLegendreNodes ↔ ∀ i, eval (...) (t.c i) = 0`.
- For the backward direction `gaussLegendre_B_double`, isolate a purely polynomial lemma for Euclidean division of `X^(k-1)` by the mapped shifted Legendre polynomial and use a separate orthogonality lemma.
- For the forward direction `gaussLegendreNodes_of_B_double`, reduce to the statement that the node polynomial is orthogonal to all lower-degree polynomials and then identify the unique degree-`s` orthogonal polynomial by normalization or leading coefficient.
