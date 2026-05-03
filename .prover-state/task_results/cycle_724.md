# Cycle 724 Results

## Worked on
§521 Step E ladder in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`:
E.1, E.2, E.3, E.4. E.5 (stretch) skipped — see Discovery.

## Approach
Followed the planner's named skeletons. Each theorem was appended just
before `end LMM` and verified with `lake env lean` in isolation.
Committed each theorem to git immediately after it verified, per the
incremental-commit guidance.

## Result
SUCCESS — all four mandatory theorems landed, sorry-free, committed:

1. `D_mul_toGLM_charpoly_eval_one_collapsed_of_bdf` (E.1)
   — commit `7935acab65`
2. `D_mul_toGLM_charpoly_eval_one_reduced_of_bdf` (E.2)
   — commit `57aa0dde45`
3. `rowFAlphaResidual_eval_zero_of_bdf_eq_zero` (E.3, private)
   — commit `d3404446c1`
4. `D_mul_toGLM_charpoly_eval_zero_collapsed_of_bdf` (E.4)
   — commit `3363b2360b`

File grew from 2225 → 2314 lines, well under the 3000-line cap.

## Dead ends
- The E.2 skeleton's `← Finset.sum_neg_distrib` step did not apply: after
  `Finset.mul_sum`, the goal is `∑ l, (β l - β_last·α l) = ∑ i, -β_last·α i`,
  which is already termwise-comparable; pulling the `-` outside the sum was
  unnecessary. Dropped that step and used `Finset.sum_congr` directly with
  the BDF castSucc-vanishing hypothesis. ~1 minute fix.

## Discovery
- E.5 (`toGLM_charpoly_eval_zero_eq_zero_of_bdf`) **already exists** at
  line 1677 — it was landed in cycle 704 as the §521 Step C.18 theorem,
  with the same statement (`((m.toGLM.stabilityMatrix z).charpoly).eval 0
  = 0` under BDF + `hz`). The planner's E.5 stretch was a duplicate
  derivation of this. The planner's E.5 was actually a *third* path
  (via the new E.4 collapsed form) — D.2 (line 1753) is the second
  derivation via D.1. So the underlying fact is well-established; only
  the redundant alias was skipped.
- E.4 fits the pattern of D.2 / Step C.18: both produce
  `D · charpoly.eval 0 = 0`, but via the *substituted residual*
  identity (D.11a + E.3) rather than via the cycle 698 textbook
  headline + zero-power collapse. This gives an independent witness of
  the same identity through the rowF-residual ladder, useful as a
  cross-check.
- The cycle 720/722 cofactor-expansion playbook continues to apply
  cleanly. E.3 was a verbatim rotation of D.16d at ξ = 0.

## Suggested next approach
Step F: bridge from the BDF unit-circle eval at ξ = 1 (E.2's reduced
form) to the textbook scalar stability polynomial. The RHS of E.2 still
contains `(rowYQuot m).eval 1` and `∑ l, α(castSucc l)` as abstract
terms; what's needed is:

- A lemma reducing `(rowYQuot m).eval 1` under BDF, parallel to E.3 for
  rowFAlphaResidual. Under BDF, `toGLM_stabilityMatrixPY m 0` is upper
  triangular with `-1`s on the diagonal off the last row (cycle 645
  block-vanishing). The cofactor sum `D.14c` should collapse to a
  closed form involving only `α(castSucc k)` entries. This is the
  natural F.1 next cycle.
- Once `rowYQuot.eval 1` collapses, the RHS of E.2 should match
  `(stabilityPolyPoly z).eval 1 - (something involving α and β_last)`,
  giving the BDF unit-circle bridge.

Do NOT attempt the full unit-circle iff (`|ξ| = 1` for all ξ) yet —
that requires a full polynomial-equality lemma, not just `eval 0` and
`eval 1` evaluations. Pin to closing more named eval points or the
`rowYQuot` BDF collapse first.
