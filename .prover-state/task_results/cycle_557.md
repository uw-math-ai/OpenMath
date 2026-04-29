# Cycle 557 Results

## Worked on
Standalone §384 triple-leaf slice for
`BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]`.

## Approach
Checked the listed Aristotle result summaries; they target older `npow` /
`cSum` or unrelated work and were not applicable to this §384 slice. Wrote a
scratch sorry-first scaffold with five triple-leaf goals at
`.prover-state/aristotle_scaffolds/cycle_557/TripleLeafScaffold.lean`, verified
it compiled, and submitted it to Aristotle as project
`9f99a790-f3e0-4c32-b6b5-9df096ac42e8`. After the mandated 30-minute wait, the
single status check still showed `QUEUED`, so no Aristotle proof was available
to incorporate.

Manually added the `Fin 4` cut-count helper, grouped polynomial expansion,
per-stage `convAt` closed form, weighted collapse, `bConv` / product
`bSeries` closed forms, quotient lift, and `IsG1Equiv` single-tree slice.

## Result
SUCCESS. The new declarations are:
`tripleLeafChoiceCoef`, `tripleLeafChoiceCount`,
`tripleLeafChoiceCount_sum`, `triple_leaf_stage_polynomial_expand`,
`ButcherProduct.convAt_node_triple_leaf_at_i_eq`,
`ButcherProduct.bWeighted_convAt_node_triple_leaf_eq`,
`ButcherProduct.bConv_node_triple_leaf_eq`,
`ButcherProduct.bSeries_node_triple_leaf_eq`,
`QuotEquiv.bSeriesHom_product_node_triple_leaf`, and
`IsG1Equiv.product_congr_node_triple_leaf`.

## Dead ends
No mathematical blocker. The first `ButcherGroup.lean` check saw stale imported
`.olean` data for `Section384SlicesMixed`; building that module refreshed the
new helper names. The first G1 proof also needed an explicit `4 ≤ p` fact from
the triple-leaf order hypothesis before `omega` could close the leaf and kept
subtree bounds.

## Discovery
For this standalone all-leaves shape, grouping by cut count is much smaller
than redoing the powerset proof. The existing mixed leaf/singleton stage helper
with `a = 3, b = 0` gives the per-stage cube immediately, and the existing
replicate-leaf elementary-weight helper collapses the weighted row-sum powers.

## Suggested next approach
Use the new `Fin 4` grouped helper as the inner choice package for the next
four-way mixed family involving leaf, singleton-leaf, double-leaf, and
triple-leaf root children.
