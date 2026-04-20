# Issue: `gaussLegendreNodes_of_B_double` likely needs stronger hypotheses

## Blocker
The current theorem

```lean
theorem gaussLegendreNodes_of_B_double (t : ButcherTableau s)
    (hB : t.SatisfiesB (2 * s)) :
    t.HasGaussLegendreNodes
```

looks too strong as stated. `B(2*s)` says the quadrature moments match up to
degree `2*s - 1`, but the usual converse characterization of Gauss nodes also
uses a uniqueness argument for an `s`-node rule, typically requiring distinct
nodes and/or a root-count argument for the orthogonal polynomial.

## Context
- File: `OpenMath/Legendre.lean`
- Remaining sorry location: theorem `ButcherTableau.gaussLegendreNodes_of_B_double`
- Prior cycle notes already flagged this as the harder goal than
  `gaussLegendre_B_double`

## What was tried
- Reviewed the current statement against the surrounding infrastructure in
  `OpenMath/Legendre.lean`.
- Checked prior Aristotle artifacts and task reports. Multiple harvested proofs
  either left this theorem as `sorry` or changed the meaning of
  `HasGaussLegendreNodes`, making them unusable in the current file.
- Checked the new ready Aristotle bundle `c247a02b-88ab-4acf-924c-9619789856ef`;
  it only supplied a bridge proof for a different shifted-Legendre definition.

## Possible solutions
- Strengthen the theorem statement with the hypotheses actually used by the
  converse argument, likely distinct nodes and the polynomial bridge needed for
  root counting.
- Split the converse into:
  1. `B(2*s)` implies every tableau node is a root of the relevant shifted
     Legendre polynomial.
  2. A root-count / degree argument packages this as `HasGaussLegendreNodes`.
- If the planner wants to keep the current statement unchanged, first prove a
  lemma showing those extra hypotheses are already derivable from the tableau
  setup; otherwise the theorem may simply be false in the present abstraction.
