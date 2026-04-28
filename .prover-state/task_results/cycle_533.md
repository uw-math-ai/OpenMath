# Cycle 533 Results

## Worked on
Butcher §384 right-block convolution infrastructure in
`OpenMath/ButcherGroup.lean`. Landed the depth-2 trunk kept-children
pass-through theorem
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_two_level_eq`
and its bSeries-form corollary
`ButcherProduct.bSeries_natAdd_node_trunk_kept_two_level_eq`.

## Approach
Started from the cycle 532 unified kept-children theorem
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq`, then used
`Finset.sum_congr rfl`, `congr 1`, and `Finset.prod_congr rfl` to drill
into the kept-side product. In the kept root-child node branch, the proof
descends into the inner powerset over grandchildren, case-splits each kept
grandchild with an inline `match`, collapses leaf grandchildren via
`rightAuxAtCoef_leaf`, and unfolds node grandchildren with
`rightAuxAtCoef_node_eq_powerset_sum`.

The bSeries corollary is the direct specialization at
`coef := t₁.bSeries` after rewriting through
`ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef`.

## Result
SUCCESS. `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/ButcherGroup.lean` succeeds with no `sorry`.

`plan.md` was updated in the §384 chapter ledger and in the
`## Current Target` paragraph to record the two cycle 533 theorem names and
to point the next seam at depth-3 trunk pass-through.

## Aristotle protocol
After the sorry-first scaffold compiled, submitted
`OpenMath/ButcherGroup.lean` once to Aristotle with the two cycle 533
sorries. The service immediately returned HTTP 429:

`You have too many requests in progress. Please cancel or wait for a project to complete before starting a new one.`

Per the cycle strategy, no retry, polling, or sleep was performed. The
proofs were closed manually.

## Dead ends
The first manual proof attempt used
`rw [ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq]` without
supplying the unused `t₁` argument, leaving Lean unable to infer the theorem
specialization. Supplying
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq t₁ t₂ coef children`
fixed the rewrite.

## Discovery
The depth-2 proof is structurally the same as cycle 532 with one more nested
`Finset.sum_congr` / `Finset.prod_congr` layer. The important alignment is
to rewrite from the cycle 532 theorem, leave the cut-side products untouched,
and only case-split the attached grandchild factor inside the child-node
branch.

Inline `match` remains manageable at this depth; no private helper or
heartbeat-saving abbreviation was needed.

## Suggested next approach
Push the same trunk pass-through one layer deeper (depth 3), expanding the
remaining attached `rightAuxAtCoef` calls inside the great-grandchild node
branch. If the statement becomes too large, start packaging the ladder as a
depth-indexed helper or a `BTree.rec` motive, but only after one more direct
layer confirms the recurring shape.
