# Cycle 368 Results

## Worked on
- `OpenMath/CollocationAlgStability.lean`
- mandatory one-pass triage for prior Aristotle bundles:
  - `28f20c33-a2cc-48ed-807e-e184fecdee2d`
  - `7b2bf1cb-5eb9-4e45-ad12-8591dd23f0f0`
  - `fb765e3d-98de-4254-afd3-2b928f226032`
  - `9fd0c5c8-911a-4daa-9393-a762eeff297d`
- new Aristotle submissions for the live split/residual scaffold:
  - `dad34573-3089-43da-a712-6bbe8b4a3947`
  - `b851527f-b4e1-469f-a67e-5646728cadfe`
  - `2b70cee0-6f12-45f1-a209-e9fbad8b9620`
  - `5ec4eea3-fb95-4a9d-90c2-146c9cd0bb36`
  - `feee12d6-2a89-4094-943e-584d34f7edda`

## Approach
- Read the required live context first:
  - `.prover-state/strategy.md`
  - `.prover-state/issues/cycle_367_stabilityMatrix_general_q_reduction.md`
  - `.prover-state/task_results/cycle_367.md`
  - `OpenMath/CollocationAlgStability.lean`
- Triaged the four planner-listed Aristotle bundles exactly once, restricted to:
  - `ARISTOTLE_SUMMARY.md`
  - `CollocationAlgStability.lean`
- Rejected all four prior bundles as transplant sources:
  - `28f20c33...` rewrites the shifted-Legendre sign convention and depends on stub infrastructure.
  - `7b2bf1cb...` uses the explicitly banned antiderivative / mod-by-monic route and stub infrastructure.
  - `fb765e3d...` and `9fd0c5c8...` are stale full-file rebuilds around already-landed material and still depend on rebuilt sidecars.
- Landed the live sorry-first split required by the planner:
  - added theorem-local helper scaffold `algStabMatrix_poly_bilinear_zero`
  - added a top-term remainder helper scaffold
  - added a pure top-monomial defect lemma scaffold
  - split `stabilityMatrix_quadForm_eq_neg_integral` into low-degree and top-degree branch lemmas
- Proved the low-degree branch wrapper `stabilityMatrix_quadForm_eq_neg_integral_of_lt`.
- Found and fixed a real soundness bug in the new remainder helper:
  - the original statement with only `0 < s` is false at `s = 1`,
  - replaced it by the true statement with `1 < s`,
  - proved the corrected lemma `sub_leading_term_natDegree_lt`.
- Submitted five new Aristotle jobs against the live file after the sorry-first scaffold compiled, then waited ~30 minutes before a single refresh.

## Result
- SUCCESS: the live file now has the required low-degree/top-degree split for `stabilityMatrix_quadForm_eq_neg_integral`.
- SUCCESS: the top-degree seam is isolated as the single residual lemma `algStabMatrix_top_monomial_eq_neg_integral`.
- SUCCESS: the corrected helper `sub_leading_term_natDegree_lt` is proved in the live file.
- SUCCESS: the low-degree branch `stabilityMatrix_quadForm_eq_neg_integral_of_lt` is in place and compiles against the new scaffold.
- PARTIAL SUCCESS: `dad34573...`, `2b70cee0...`, and `5ec4eea3...` each produced theorem-local proof ideas worth reading, but none could be transplanted directly without cleanup; `b851527f...` proved a corrected statement rather than the live one; `feee12d6...` was still `IN_PROGRESS` at the single post-wait refresh and was left alone.

## Dead ends
- A direct transplant of the Aristotle proof for `algStabMatrix_poly_bilinear_zero` turned into heavy finite-sum reindexing noise and was not worth forcing into the live file this cycle.
- The Aristotle run `b851527f...` correctly detected that the original `sub_leading_term_natDegree_lt` statement was false at `s = 1`; its exact patch was not transplantable because it changed the statement surface and commented out the old lemma.
- The Aristotle proofs for the top-monomial defect and top-degree branch still depend on theorem-local cleanup before they can be trusted in the live repository.

## Discovery
- The theorem-local remainder lemma really needs an explicit `1 < s` hypothesis; otherwise the supposed degree drop is false in the `s = 1` top-degree case.
- After the split, the remaining live frontier is cleanly concentrated in two seams:
  - finite-sum reindexing for `algStabMatrix_poly_bilinear_zero`
  - the pure top-monomial defect calculation in `algStabMatrix_top_monomial_eq_neg_integral`

## Suggested next approach
- Prove `algStabMatrix_poly_bilinear_zero` locally by a cleaner two-stage expansion:
  - expand only one polynomial at a time,
  - factor coefficients out of the `Finset` sums with small helper calcs,
  - apply `algStabMatrix_monomial_bilinear_zero` only on the true support range `natDegree + 1`.
- Then finish `algStabMatrix_top_monomial_eq_neg_integral` using the `p := nodePoly t * X^(s - 1)` decomposition against `B(2 * s - 1)`.
- Finally, reopen `stabilityMatrix_quadForm_eq_neg_integral_of_eq` and handle `s = 1` separately from the `1 < s` remainder-subtraction branch.
