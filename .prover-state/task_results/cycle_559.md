# Cycle 559 Results

## Worked on
Standalone four-children mixed §384 slice:
`BTree.node [BTree.leaf, BTree.leaf, BTree.leaf, BTree.node [BTree.leaf]]`
(three leaves plus one singleton-leaf child).

## Approach
Created `OpenMath/ButcherGroup/Section384SlicesQuadMixed.lean` and adapted
the cycle 557 standalone triple-leaf template to a `Fin 4 × Fin 3`
decomposition. The `Fin 4` axis reuses the triple-leaf grouped cut count; the
`Fin 3` axis records the singleton-leaf child state: root cut, kept with inner
cut, or kept with inner kept. Added the quotient lift and the `IsG1Equiv`
single-tree product congruence in `OpenMath/ButcherGroup.lean`.

Submitted the sorry-first file to Aristotle in one batch:
- Step 2 `convAt` job `ecfa6dfd-63ba-4d00-a057-68f70e660efc`: still
  `IN_PROGRESS` after the required 30-minute wait.
- Step 3 weighted-collapse job `97576add-af2e-48ad-b862-2e067633f3d2`:
  still `IN_PROGRESS` after the required 30-minute wait.
- Step 5 product `bSeries` job `c57f7eb9-3357-4afb-8473-02a52a9a284c`:
  still `IN_PROGRESS` after the required 30-minute wait.

With no completed Aristotle output available, closed the proofs manually using
the cycle 557 grouping pattern plus local copies of the private
leaf/singleton-leaf elementary-weight and `convAt` helpers.

## Result
SUCCESS. Added the standalone quad-mixed slice with:
`tQuadMixed`, `quadMixedSingletonLeafCount`,
`quadMixedSingletonNodeCount`, `quadMixedSingletonChoiceCoef`,
`quadMixedSingletonStageChoiceCoef`, `quadMixedChoiceTree`,
`quad_mixed_singleton_stage_expand`,
`quad_mixed_stage_polynomial_expand`,
`ButcherProduct.convAt_node_quadMixed_at_i_eq`,
`ButcherProduct.bWeighted_convAt_node_quadMixed_eq`,
`ButcherProduct.bConv_node_quadMixed_eq`,
`ButcherProduct.bSeries_node_quadMixed_eq`,
`QuotEquiv.bSeriesHom_product_node_quadMixed`, and
`IsG1Equiv.product_congr_node_quadMixed`.

Step 5's bSeries-only closed form was possible. The kept-singleton state folds
into `t₂.bSeries (quadMixedChoiceTree k h)`; no raw kept-side row-sum
obstruction remained.

## Dead ends
No structural blocker. Aristotle did not finish within the mandated wait, so
the final proofs were closed manually.

## Discovery
For a single singleton-leaf child, the mixed kept side can still be expressed
entirely as `t₂.bSeries` on
`BTree.node (replicate leaves ++ replicate singleton-leaves)`, with the
singleton's inner cut contributing one extra kept leaf.

## Suggested next approach
The next seam can be a four-child tree with two singleton-leaf children, or a
five-children pure-leaf standalone slice, depending on whether the planner
wants to grow mixed depth or pure breadth first.
