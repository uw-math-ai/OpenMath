# Cycle 399 Results

## Worked on
`OpenMath/LMMTruncationOp.lean`: added the four polynomial-eval truncation
operator wrappers requested by the strategy:

- `LMM.truncationOp_polynomial_eval_eq_zero_of_HasOrder`
- `LMM.truncationOp_polynomial_eval_eq_leading_of_HasOrder`
- `LMM.truncationOp_polynomial_evalShift_eq_zero_of_HasOrder`
- `LMM.truncationOp_polynomial_evalShift_eq_leading_of_HasOrder`

## Approach
Followed the sorry-first workflow: added the four theorem statements with
`sorry`, checked `OpenMath/LMMTruncationOp.lean`, then closed them.

For the origin theorems, added two private helpers:

- `polynomial_eval_eq_finset_sum_of_natDegree_le`
- `derivative_eval_eq_finset_sum_of_natDegree_le`

The first helper uses `Polynomial.eval_eq_sum_range'` plus
`Fin.sum_univ_eq_sum_range`. The derivative helper uses
`Polynomial.derivative_eval` and `Polynomial.sum_over_range'`, which avoids the
planned derivative reindex because Mathlib already expands the derivative in
the desired `coeff k * k * u^(k-1)` form. The origin wrappers then reduce to
`truncationOp_polyCombination_eq_zero_of_HasOrder` and
`truncationOp_polyDegSucc_eq_leading_of_HasOrder`.

The shifted wrappers lift the origin wrappers through
`truncationOp_translation`, exactly like the existing finite-tuple shifted
theorems.

## Result
SUCCESS.

- `OpenMath/LMMTruncationOp.lean` compiles with no `sorry`.
- `plan.md` updated under §1.2 with the cycle 399 polynomial-eval wrappers.
- `lean_verify` on all four new public theorems reports only standard axioms:
  `propext`, `Classical.choice`, `Quot.sound`.

Aristotle:

- Rejected previous ready project `ec8b2dab-c76c-4bac-8c3d-b596267520eb` as a
  stale BDF7 stub-replacement bundle, per strategy.
- Submitted exactly five cycle 399 jobs and slept 30 minutes before one
  refresh:
  - Task A: `142ceb00-b240-44c9-ae4e-1b44472e7c0f`
  - Task B: `d3079062-5500-43c1-a66b-9c169afdb5fe`
  - Task C: `d845dba2-1588-44fe-931c-dd12f4bf6ff5`
  - Task D: `4701b7a2-1488-4678-bc68-d1acda040479`
  - diagnostic: `4832d223-63dc-4a28-8ca2-d45a6b44893f`
- All five refreshed as `COMPLETE_WITH_ERRORS`. Extracted and triaged them.
  Every returned bundle created a tiny stub `OpenMath/MultistepMethods.lean`
  redefining live LMM infrastructure, so none was transplantable. Several also
  left unrelated `sorry`s in non-target theorem bodies.

## Dead ends
The Aristotle bundles reproduced the known non-incorporable pattern: a local
toy `OpenMath/MultistepMethods.lean` with fresh `LMM`, `HasOrder`, and
`errorConstant` definitions. Those results were useful as confirmation of the
proof idea but were not safe to merge.

## Discovery
`Polynomial.derivative_eval` is the right polynomial-side bridge for this
thread. It expands `(P.derivative).eval u` as `P.sum fun n a => a * n *
u^(n-1)`, so `Polynomial.sum_over_range'` turns it directly into the finite
`Fin (N+1)` tuple form used by the truncation-operator lemmas.

This keeps the polynomial wrapper layer small and avoids a bespoke derivative
index-shift lemma.

## Suggested next approach
Cycle 400 can start the Taylor / smooth-solution bridge. Use the new
`Polynomial.eval` wrappers instead of finite coefficient tuples when applying
Taylor polynomials at the origin or at evaluation point `t`.

The next proof layer should introduce the local truncation error normalization
and a Taylor-with-remainder statement for smooth `y`, then apply:

- `truncationOp_polynomial_evalShift_eq_zero_of_HasOrder` to the degree `≤ p`
  Taylor polynomial piece;
- `truncationOp_polynomial_evalShift_eq_leading_of_HasOrder` to the degree
  `p+1` leading term when needed.
