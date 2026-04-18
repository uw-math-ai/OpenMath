# Cycle 111 Results

## Worked on
- Remaining sorry `norm_stabilityFn_imagBasis_gt_one` in `OpenMath/ANStability.lean`
- Aristotle harvest check for the previously completed Padé jobs
- New Aristotle submissions for the AN-stability blocker and two helper lemmas

## Approach
- Confirmed the two completed Padé Aristotle results are unrelated to the current
  AN-stability sorry, so they were not incorporated this cycle
- Checked the old cycle-110 Aristotle AN-stability job via project listing:
  `95f3a6d4-c727-4482-9525-94f795041d07` is still `IN_PROGRESS`
- Attempted to decompose the remaining sorry into:
  - a quadratic-form identity for `algStabMatrix`
  - a small-`τ` determinant nonvanishing lemma
- Reverted that decomposition when the helper proof attempt left
  `ANStability.lean` in a non-compiling intermediate state
- Created standalone Aristotle inputs for the helper lemmas instead

## Result
FAILED — the main sorry is still open, but the file was restored to a clean
single-sorry state and four new Aristotle jobs were queued:

- `1be8d0a1-92d5-42c4-b1ae-6d766b88a48b` for `OpenMath/ANStability.lean`
- `b0bfbf1f-2b35-41d3-a4bc-ac5057557660` for `cycle_111_algStabMatrix_quadForm.lean`
- `1dfac67a-d980-41a0-8873-a395285eb451` for `cycle_111_imagBasis_det.lean`
- `ebff41fc-ac07-411c-a5ed-caef513bb041` for `cycle_111_norm_imagBasis.lean`

## Dead ends
- Rewriting post-`ring_nf` finite sums with previously proved equalities was too
  brittle: monomial order changed enough that `rw` no longer matched the target
- Combining `Finset.sum_congr`, `Finset.sum_comm`, and `ring_nf` inside the same
  proof created fragile normal forms that were hard to stabilize

## Discovery
- The continuity proof for determinant nonvanishing appears feasible with
  `Metric.continuousAt_iff`, `Continuous.matrix_diagonal`, and
  `Continuous.matrix_det`
- The quadratic-form identity is the best candidate for a standalone Aristotle
  helper because it is pure finite-sum algebra with no analytic remainder terms

## Suggested next approach
- Check the four new Aristotle jobs after they have had time to run
- If the quadratic-form helper comes back complete, port it first
- Then prove the determinant nonvanishing helper locally or from Aristotle
- Keep the main theorem modular: exact first/second-order expansion plus an
  explicit remainder bound, rather than a monolithic proof
