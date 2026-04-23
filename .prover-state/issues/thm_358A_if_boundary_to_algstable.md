# Issue: `thm_358A_if` needs a boundary-to-PSD bridge

## Blocker
The remaining `sorry` in `OpenMath/CollocationAlgStability.lean` is
`ButcherTableau.thm_358A_if`, the reverse implication

`HasAlgStabilityBoundaryNodes -> IsAlgStable`.

The forward direction is now repaired, but the reverse direction still needs a
proof that turns the boundary-node hypothesis into:

1. nonnegative weights `b_i >= 0`, and
2. positive semidefiniteness of the algebraic-stability quadratic form.

The current file does not yet contain that bridge.

## Context
- `algStabilityBoundaryPoly` had a sign-convention bug: it used Mathlib's
  `shiftedLegendre` basis directly, even though the file documents the textbook
  `P_n^*` convention. Cycle 370 fixed this by introducing the textbook-sign
  basis `shiftedLegendreStarPoly` and rewriting the boundary polynomial in that
  basis.
- After the repair, the following now compile and are proved:
  - `orthogonal_degree_eq_boundaryPoly`
  - `boundary_theta_nonneg_of_algStable`
  - supporting lemmas for `shiftedLegendreStarPoly` degree, leading coefficient,
    orthogonality, square-integral positivity, and scalar uniqueness.
- The file still compiles with one remaining `sorry` at `thm_358A_if`.

## What was tried
- Searched prior Aristotle artifacts. The most relevant partial attempt is
  `.prover-state/aristotle_results/995901fc-98bc-4885-a95e-c5dc63a0cabb/...`,
  which introduces a separate Lagrange-basis proof stack:
  - `lagrangeBasisPoly`
  - `weight_eq_integral_lagrange`
  - `weights_nonneg_of_boundary`
  - `stabMatrix_quadForm_nonneg_of_boundary`
- That route looks viable, but it is not a small local patch. It requires a new
  quadrature-exactness argument from the boundary polynomial to both weight
  positivity and the stability-matrix quadratic-form estimate.
- Also checked whether the existing
  `stabilityMatrix_quadForm_eq_neg_integral` machinery could be reused in
  reverse. It cannot directly, because that theorem already assumes
  `hAlg : t.IsAlgStable`.

## Possible solutions
- Import the Lagrange-basis route from the older Aristotle sketch and adapt it
  to the corrected `shiftedLegendreStarPoly` sign convention. This looks like
  the most direct next step.
- Alternatively, extract a new theorem-local bridge:
  `HasAlgStabilityBoundaryNodes -> (quadrature defect >= 0 on degree <= 2s-1)`
  and derive both weight nonnegativity and PSD from that bridge.
