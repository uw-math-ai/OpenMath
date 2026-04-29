# Cycle 551 Results

## Worked on
§387 `QuotEquiv.npow` arithmetic in `OpenMath/ButcherGroup.lean`.

Added the requested multiplication-exponent and small-exponent corollaries:

- `ButcherProduct.npowStages_mul`
- `ButcherProduct.npowStages_mul_eq`
- `QuotEquiv.weightsSum_npow_mul`
- `QuotEquiv.cSum_npow_mul`
- `QuotEquiv.weightsSum_npow_le`
- `QuotEquiv.weightsSum_npow_five`
- `QuotEquiv.cSum_npow_five`
- `QuotEquiv.npowStages_npow_eq_mul`

The planner called this seven deliverables, but item 6 names two separate
`n = 5` theorems, so eight declarations were added.

## Approach
Followed the sorry-first workflow:

1. Inserted all theorem statements with `sorry`.
2. Checked `lake env lean OpenMath/ButcherGroup.lean`; it compiled with only
   the expected `declaration uses sorry` warnings.
3. Submitted five Aristotle jobs:
   `npowstages_mul`, `weightssum_npow_mul`, `csum_npow_mul`,
   `weightssum_npow_five`, and `csum_npow_five`.
4. All five Aristotle submissions returned immediate HTTP 429:
   "You have too many requests in progress." There were no project IDs to
   sleep on or poll, so no Aristotle proof was usable this cycle.
5. Closed the proofs manually from the existing closed forms.

Proof styles:

- `simpa`: `ButcherProduct.npowStages_mul`,
  `QuotEquiv.weightsSum_npow_mul`, `QuotEquiv.cSum_npow_mul`,
  `QuotEquiv.weightsSum_npow_five`.
- `rw` + Nat arithmetic: `ButcherProduct.npowStages_mul_eq`.
- `push_cast` + `nlinarith`: `QuotEquiv.weightsSum_npow_le`.
- `push_cast` + `linarith`: `QuotEquiv.cSum_npow_five`.
- `simp [ButcherProduct.npowStages_eq]`:
  `QuotEquiv.npowStages_npow_eq_mul`.

## Result
SUCCESS.

The new §387 arithmetic surface compiles with zero sorries. The existing
theorem `QuotEquiv.npowStages_npow_eq_npowStages_mul` was already present,
so I left it in place and added the distinct nested-stage statement
`QuotEquiv.npowStages_npow_eq_mul`.

Verification run:

- `grep -n "sorry" OpenMath/ButcherGroup.lean` returned no matches.
- `lake env lean OpenMath/ButcherGroup/Core.lean`
- `lake env lean OpenMath/ButcherGroup/Section384.lean`
- `lake env lean OpenMath/ButcherGroup/Section384Slices.lean`
- `lake env lean OpenMath/ButcherGroup.lean`
- `lake build`

All Lean checks passed. `lake build` emitted unrelated pre-existing warnings
in other modules, but completed successfully.

This cycle deliberately did not touch
`OpenMath/ButcherGroup/Section384.lean` or
`OpenMath/ButcherGroup/Section384Slices.lean`.

This cycle deliberately did not add another parametric shape-specific slice,
in line with the cycle 550 directive.

## Dead ends
One proof attempt for `QuotEquiv.cSum_npow_five` used `norm_num at h` after
instantiating `cSum_npow q 5`. That unfolded the named `(q.npow 5).cSum`
term into explicit nested products, losing the desired left-hand side. The
cycle 508 pattern was correct: use `push_cast at h` and then `linarith`.

## Discovery
The multiplication-exponent closed forms are all immediate from the existing
cycle 506-513 closed forms. No §384 convolution machinery is involved.

`QuotEquiv.weightsSum_npow_le` is most robust if proved from the closed form
at `n + 1`, then `push_cast`, then `nlinarith` with `0 ≤ (n : ℝ)` and the
base nonnegativity hypothesis.

## Suggested next approach
Continue treating §387 arithmetic as the unblocked path when small concrete
power-surface lemmas are needed. For `G1.mul`, the gating obstruction remains
the §384 honest convolution; future work should either attack that
structurally with cuts/trunks or pivot to another planned backlog target.
