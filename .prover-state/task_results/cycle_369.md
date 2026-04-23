# Cycle 369 Results

## Worked on
- `OpenMath/CollocationAlgStability.lean`
- Required Aristotle bundle triage:
  - `dad34573-3089-43da-a712-6bbe8b4a3947`
  - `2b70cee0-6f12-45f1-a209-e9fbad8b9620`
  - `5ec4eea3-fb95-4a9d-90c2-146c9cd0bb36`
  - `b851527f-b4e1-469f-a67e-5646728cadfe`
  - `4f3ee601-6534-4991-b802-4c99623bec7f`
  - `b3b1362b-0567-4a48-b42d-d65635586332`

## Approach
- Read the planner-required live context first:
  - `OpenMath/CollocationAlgStability.lean`
  - `.prover-state/task_results/cycle_368.md`
  - `.prover-state/issues/cycle_367_stabilityMatrix_general_q_reduction.md`
- Triaged the ready Aristotle bundles exactly as instructed:
  - accepted theorem-local proof ideas from `dad34573...`, `2b70cee0...`, and `5ec4eea3...`
  - used `b851527f...` only as a sanity check for the already-landed `1 < s` remainder lemma fix
  - rejected `4f3ee601...` as stale/monolithic
  - used `b3b1362b...` only as a warning to trigger the post-frontier theorem-sanity check
- Implemented the three planner-priority proofs in order:
  1. `algStabMatrix_poly_bilinear_zero`
  2. `algStabMatrix_top_monomial_eq_neg_integral`
  3. `stabilityMatrix_quadForm_eq_neg_integral_of_eq`
- After closing the three frontier lemmas, performed the required sanity check for
  `orthogonal_degree_eq_boundaryPoly` by tracing the leading coefficient of
  `algStabilityBoundaryPoly s θ` back to Mathlib’s `coeff_shiftedLegendre`.

## Result
- SUCCESS: `algStabMatrix_poly_bilinear_zero` is proved in the live file.
  The proof expands polynomial evaluations over `Finset.range s`, reorders the resulting double
  coefficient sum, and kills each admissible monomial pair with
  `algStabMatrix_monomial_bilinear_zero`; out-of-range coefficient pairs vanish because the
  coefficients are zero above `natDegree`.
- SUCCESS: `algStabMatrix_top_monomial_eq_neg_integral` is proved in the live file.
  The proof uses
  `p := nodePoly t * X^(s - 1)`, degree-drop on `p - X^(2*s - 1)`, exactness at degree `2*s - 1`,
  and `quadEvalPoly_nodePoly_mul_eq_zero`.
- SUCCESS: `stabilityMatrix_quadForm_eq_neg_integral_of_eq` is proved in the live file.
  The proof follows the planner’s branch structure:
  - `s = 1`: reduce directly to the pure top-monomial case
  - `1 < s`: subtract the leading term, kill `r/r` and mixed terms with
    `algStabMatrix_poly_bilinear_zero`, kill the lower-degree integral with `hzero`, and finish
    with `algStabMatrix_top_monomial_eq_neg_integral`
- SUCCESS: the live file now compiles with only the three later 358A sorries remaining.
- PARTIAL SUCCESS: the required theorem-sanity check found a real blocker rather than a proof gap.
  Under the live sign convention, the leading coefficient of `algStabilityBoundaryPoly s θ` is
  `(-1)^s * Nat.choose (2*s) s`, so the current existential with `0 < a` is false for odd `s`.

## Dead ends
- A direct transplant of the Aristotle finite-sum bijection proof for
  `algStabMatrix_poly_bilinear_zero` was brittle in the live file; it was replaced by a cleaner
  nested-sum reordering argument.
- A direct reuse of the stale monolithic route from `4f3ee601...` was intentionally avoided.
- The next theorem, `orthogonal_degree_eq_boundaryPoly`, should not be attacked as currently
  stated; the obstruction is the theorem surface, not the Legendre-orthogonality proof plan.

## Discovery
- The three frontier sorries from cycles 367-368 are now closed.
- The next real blocker is exactly the planner-predicted parity issue:
  `algStabilityBoundaryPoly s θ` inherits the degree-`s` coefficient from `shiftedLegendrePoly s`,
  so its leading sign alternates with `s`.
- The current statement of `orthogonal_degree_eq_boundaryPoly` is therefore false for odd `s`.

## Suggested next approach
- Repair the theorem surface around `orthogonal_degree_eq_boundaryPoly` before attempting a proof.
  The minimal viable repair is likely:

```lean
∃ θ a : ℝ, a ≠ 0 ∧ φ = Polynomial.C a * algStabilityBoundaryPoly s θ
```

- Then re-evaluate the downstream statements that currently assume `0 < a`, especially the path
  into `boundary_theta_nonneg_of_algStable`.
- Issue written:
  `.prover-state/issues/cycle_369_boundary_poly_positive_scalar_false_for_odd_s.md`
