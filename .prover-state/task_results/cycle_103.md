# Cycle 103 Results

## Worked on
- Housekeeping updates in `plan.md` for the completed Padé recurrence work from cycle 102.
- New file `OpenMath/AStabilityCriterion.lean` for Theorem 351B infrastructure.
- A blocker analysis for the planner's proposed 351B statement.
- Aristotle batch submissions for a strengthened version of the 351B theorem.

## Approach
- Checked the prior Aristotle Padé result directories first; they were stale relative to the current tree and did not yield new changes to incorporate.
- Reviewed existing A-stability proofs and the maximum-modulus infrastructure in `OpenMath/MultistepMethods.lean`.
- Compared that infrastructure with the planner’s proposed statement for 351B.
- Formalized the `ePoly` definition and the valid necessity-direction lemmas that do not require the missing sufficiency machinery.
- Wrote a scratch Aristotle file with a strengthened theorem statement that includes explicit nonvanishing and degree hypotheses.
- Submitted five Aristotle jobs:
  - `122a208c-7910-422c-9a8c-b95d25d3e3df` for `poles_in_rhp_of_nonvanishing_on_clhp`
  - `a2ca24cd-509d-4634-b66d-42ed984230d3` for `ePoly_nonneg_of_aStable`
  - `c70786b3-cbc3-4010-8e15-5b8c7e32611f` for `aStable_of_nonvanishing_and_ePoly_nonneg`
  - `d1050b9a-7f36-4b62-b220-e0bddf70a03d` for the strengthened iff theorem
  - `b4d3a154-b62b-497e-9a70-a8002f936c22` for a Phragmen-Lindelof style sufficiency proof

## Result
FAILED — the exact theorem statement from the planner is not derivable from the hypotheses it gives.

Concretely, the hypothesis

`∀ z, z.re ≤ 0 → D.eval z ≠ 0 → ‖N.eval z / D.eval z‖ ≤ 1`

is vacuous at zeros of `D`, so it cannot imply that all poles lie in the open right half-plane. The arbitrary-polynomial sufficiency direction also needs extra control at infinity, typically via a degree bound and an explicit nonvanishing hypothesis on the closed left half-plane.

Meaningful progress made this cycle:
- `plan.md` was updated per housekeeping.
- `OpenMath/AStabilityCriterion.lean` now contains the 351B setup and proved necessity lemmas:
  - `evalImag_ne_zero_of_poles_rhp`
  - `ePoly_nonneg_of_imag_axis_bound`
  - `ePoly_nonneg_of_aStable`
  - `ePoly_nonneg_of_aStable_and_poles_rhp`
- `lean_status.json` now marks `thm:351B` as `in_progress`.
- A structured blocker issue was written.

## Dead ends
- The direct theorem statement from the planner cannot prove pole exclusion because the denominator-nonzero premise appears inside an implication.
- A general sufficiency proof for arbitrary polynomials is not available from the current hypotheses; the maximum-modulus route still needs a bounded-domain truncation plus a separate infinity-control lemma.
- Local verification is temporarily blocked by a first-time mathlib build in this lake root, not by the new Lean code itself.

## Discovery
- The repository’s existing RK A-stability proofs always establish denominator nonvanishing on `Re z ≤ 0` separately before proving `‖N/D‖ ≤ 1`; that separation is exactly what 351B also needs.
- The most reusable analytic tool already in-tree is `re_nonneg_of_frontier_re_nonneg` from `OpenMath/MultistepMethods.lean`.
- A workable next statement is a strengthened version of 351B for rational functions with:
  - explicit nonvanishing on `Re z ≤ 0`
  - the boundary condition `ePoly ≥ 0` on the imaginary axis
  - and a degree condition such as `N.natDegree ≤ D.natDegree`

## Suggested next approach
- Harvest the Aristotle results once ready and see whether they can prove the strengthened nonvanishing-based theorem.
- Restate 351B in Lean with the hypotheses actually needed for rational functions, or specialize it to RK stability functions where those hypotheses are already available from the tableau.
- Reuse `Complex.norm_le_of_forall_mem_frontier_norm_le` on bounded left-half-disk truncations and pair it with a separate lemma controlling the large-semicircle boundary from the degree condition.
