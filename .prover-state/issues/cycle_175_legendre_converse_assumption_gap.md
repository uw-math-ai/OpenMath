# Issue: `gaussLegendreNodes_of_B_double` still looks under-assumed

## Blocker
The theorem
`ButcherTableau.gaussLegendreNodes_of_B_double`
currently asks for
`t.SatisfiesB (2 * s) -> t.HasGaussLegendreNodes`
with no distinctness, normalization, or uniqueness hypotheses on the nodes.

The current repository infrastructure does not yet justify that conclusion.

## Context
- File:
  [OpenMath/Legendre.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/Legendre.lean:262)
- Nearby proved infrastructure is enough for the backward direction
  `HasGaussLegendreNodes + B(s) -> B(2s)` only after the missing bridge/orthogonality step.
- The forward direction would need some uniqueness principle identifying the degree-`s`
  orthogonal polynomial from quadrature exactness alone, or additional node assumptions.

## What was tried
- Re-read the old blocker notes and previous cycle results.
- Submitted a fresh focused Aristotle file for the converse theorem:
  `cycle_175/05_gaussLegendreNodes_of_B_double.lean`
- Checked older Aristotle converse jobs:
  - `90c4d148-c1e1-4211-a425-5ebe46b3cd8d`
  - `287bc1a0-a780-4b0c-9423-ca7ed825456a`
- No completed in-repo-compatible proof is available yet.

## Possible solutions
- Strengthen the theorem with the missing hypotheses if the textbook argument really uses them.
- Prove a uniqueness theorem for the node polynomial under `B(2*s)` plus appropriate distinctness/nondegeneracy assumptions.
- Defer the converse theorem and close only `gaussLegendre_B_double` first once the bridge theorem lands.
