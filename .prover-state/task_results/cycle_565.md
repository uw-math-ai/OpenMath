# Cycle 565 Results

## Worked on
The §384 mixed leaf + triple-leaf replicate family:

`BTree.node (List.replicate a BTree.leaf ++
List.replicate b (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))`

## Approach
Added a sorry-first scaffold for the raw `bConv`/`bSeries` slice in
`OpenMath/ButcherGroup/Section384SlicesMixed/Replicate.lean` and the
quotient/G1 transport in `OpenMath/ButcherGroup.lean`.

Submitted five Aristotle jobs:

- `51a1b1c3-0515-4245-9658-ab80e2ef9d01` for the raw `bConv` theorem.
- `c015ec03-8b4b-4744-be1c-2c0b249e7bc9` for the raw `bSeries` theorem.
- `a93cdd73-1cda-427a-9d4c-4cb53da582b3` for the quotient lift.
- `2f3abe5a-140a-4068-96f4-e5605de2a5c0` for the `IsG1Equiv` slice.
- `f7e14314-baf1-48d1-9bfa-e6fba23bf30b` for the weighted-stage sum helper.

After the required 30-minute wait, all five were still `QUEUED`, so there
were no result files to incorporate this cycle.

Manually followed the existing all-triple-leaf and mixed double-leaf
templates: prove a stage polynomial expansion, commute the stage-weighted
sum through the cut sums, collapse the remaining stage sum with the common
four-shape `bSeries` helper, then lift to `QuotEquiv` and `IsG1Equiv`.

## Result
SUCCESS.

Added:

- `mixedLeafTripleLeafChoiceTree`
- `ButcherProduct.bConv_node_replicate_mixed_leaf_triple_leaf_eq`
- `ButcherProduct.bSeries_node_replicate_mixed_leaf_triple_leaf_eq`
- `QuotEquiv.bSeriesHom_product_node_replicate_mixed_leaf_triple_leaf`
- `IsG1Equiv.product_congr_node_replicate_mixed_leaf_triple_leaf`

The order budget is discharged via the identity `1 + a + 4 * b`.

## Dead ends
No mathematical dead end. Aristotle remained queued after the mandated wait,
so the proof was completed locally.

## Discovery
The mixed family needs a residual-tree helper carrying the kept root leaves:
`mixedLeafTripleLeafChoiceTree (a - S_leaf.card) χ`. This is the direct
triple-leaf analogue of the `doubleLeafChoiceTree aKeep χ` shape.

`OpenMath/ButcherGroup.lean` is now 3206 lines, still below the hard cap.

## Suggested next approach
The next slice can extend the same pattern to another mixed triple-leaf
family. The reusable pieces are the new residual-tree helper and the
weighted mixed leaf/triple-leaf stage expansion template.

## Verification
`lake env lean OpenMath/ButcherGroup/Section384SlicesMixed/Replicate.lean`

`lake env lean OpenMath/ButcherGroup.lean`

`lake build`
