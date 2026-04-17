# Issue: B(2s) and E(s,s) converse implications need Gaussian quadrature uniqueness

## Blocker
The converse directions in Theorem 342C,
`B(2s) ∧ E(s,s) ⇒ C(s)` and `B(2s) ∧ E(s,s) ⇒ D(s)`,
do not reduce to finite-sum algebra alone in the current formalization.

## Context
`OpenMath/Collocation.lean` now defines
`ButcherTableau.SatisfiesE` using equation (321c):

`∑ i, ∑ j, b_i * c_i^(k-1) * a_ij * c_j^(l-1) = 1 / (l * (k + l))`.

The forward implications
`SatisfiesE_of_B_C` and `SatisfiesE_of_B_D`
are proved by collapsing one sum with `C` or `D`, then applying `B`.

For the converse directions, the textbook proof multiplies the `C(s)`-failure matrix by a
non-singular `b`-weighted Vandermonde matrix and concludes the original matrix vanishes.
Our current `ButcherTableau` API does not encode the distinct-node / Gaussian-quadrature
facts needed to justify that non-singularity.

## What was tried
- Recovered the exact `E(η,ζ)` formula from extracted equation `(321c)` and theorem `343B`.
- Set up all four theorem stubs and submitted `OpenMath/Collocation.lean` to Aristotle
  (`project_id = c776d9e1-9ced-477d-96b5-d00f54e42908`).
- Proved the forward directions manually:
  `B(2s) ∧ C(s) ⇒ E(s,s)` and `B(2s) ∧ D(s) ⇒ E(s,s)`.
- Explored a polynomial-orthogonality proof to avoid explicit matrix inversion, but that still
  needs a way to pass from vanished weighted moments to pointwise stage identities. Without a
  distinct-node / nonzero-weight theorem, the argument stops at aggregated node data.

## Possible solutions
- Formalize the Gaussian quadrature uniqueness package implied by `B(2s)` for `s` stages:
  distinct nodes, nonzero weights, and weighted Vandermonde non-singularity.
- Alternatively, add a separate hypothesis such as `Function.Injective t.c` plus a proof that
  the relevant weighted evaluation map is injective when `B(2s)` holds.
- Or prove the polynomial form of `E` from theorem `343B` and then derive `C`/`D` via Lagrange
  interpolation on distinct nodes, once the node distinctness lemma is available.
