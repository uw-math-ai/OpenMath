# Issue: `gaussLegendreNodes_of_B_double` still appears under-assumed after closing `gaussLegendre_B_double`

## Blocker
The remaining theorem

```lean
theorem gaussLegendreNodes_of_B_double (t : ButcherTableau s)
    (hB : t.SatisfiesB (2 * s)) :
    t.HasGaussLegendreNodes
```

still looks too strong for the current abstraction. After closing
`gaussLegendre_B_double`, the repository now has the forward Gaussian
quadrature exactness direction, but it still does not have the converse
uniqueness/root-count package needed to recover the Gauss nodes from `B(2*s)`
alone.

## Context
- File: `OpenMath/Legendre.lean`
- Current status: `gaussLegendre_B_double` is proved; the converse is the only
  remaining `sorry` in the file.
- Existing concern to preserve:
  `.prover-state/issues/gauss_legendre_nodes_converse_missing_hypotheses.md`
- Matching cycle-175 assessment:
  `.prover-state/issues/cycle_175_legendre_converse_assumption_gap.md`

## What was tried
- Re-checked the cycle-181 Aristotle converse job
  `4e9daa1f-a201-4e84-8c9c-3bf1f26163d8`; it is still `IN_PROGRESS`.
- Inspected the ready Aristotle bundles requested by the planner.
  They helped with the backward `B(2*s)` proof infrastructure, but did not
  supply a clean in-repo converse proof.
- After the new moment/orthogonality package was in place, reconsidered whether
  `B(2*s)` alone now implies the node condition. The missing step is still not
  the bridge theorem; it is the converse identification argument.

## Possible solutions
- Strengthen the converse theorem with the missing hypotheses if the textbook
  argument uses them implicitly, likely distinct nodes and/or a normalization
  plus uniqueness statement for the orthogonal degree-`s` polynomial.
- Prove an intermediate theorem:
  `B(2*s)` implies the node polynomial is orthogonal to all lower-degree
  polynomials, then add a separate uniqueness theorem identifying it with the
  shifted Legendre polynomial.
- If the planner wants to keep the present statement unchanged, first prove the
  extra hypotheses from the existing tableau assumptions; otherwise the theorem
  is likely not derivable as currently stated.
