# Cycle 564 Results

## Worked on
Structural split of `OpenMath/ButcherGroup/Section384SlicesMixed.lean`
(3389 lines, over the approaching-cap line). REFACTOR_COMMIT.

## Approach
Following the cycle 564 strategy: no new §384 slice family, no
Aristotle (refactor has no proof obligations to outsource). Did the
split in four steps:

1. Inventoried the file via `lean_file_outline`-equivalent grep on
   `private theorem` / `theorem` / `def` / `/-! ###` markers.
   Identified seven cohesive `/-! ###` sections after a 432-line
   foundational helper preamble.

2. Decided on a 4-file split (each ≤ ~1500 lines, all cohesive):
   - `Section384SlicesMixed/Common.lean` — foundational
     `elementaryWeight` / `bSeries` closed-form helpers and the
     two powerset-binomial helpers (`prod_const_add_eq_powerset` /
     `pow_add_eq_powerset`). 475 lines.
   - `Section384SlicesMixed/LeafFamilies.lean` — cycles 543–549
     (mixed leaf + singleton-leaf) and cycles 552–553 (mixed leaf +
     double-leaf), plus `doubleLeafChoiceCount` /
     `doubleLeafChoiceTree` / `doubleLeafChoiceCoef`. 1200 lines.
   - `Section384SlicesMixed/Mixed3Way.lean` — cycle 554 (mixed
     singleton-leaf + double-leaf) and cycle 556 (three-way leaf +
     singleton-leaf + double-leaf). 1145 lines.
   - `Section384SlicesMixed/Replicate.lean` — cycle 557 (standalone
     triple-leaf single tree), cycle 562 (parametric all-double-leaf),
     cycle 563 (parametric all-triple-leaf), plus
     `tripleLeafChoiceCount` / `tripleLeafChoiceCoef` /
     `tripleLeafRootChoiceCount` / `tripleLeafChoiceFunctionCoef` /
     `tripleLeafChoiceTree`. 670 lines.

3. Carved each family into its own file, promoting from `private` to
   non-`private` exactly the helpers used across the new file
   boundary (with a comment noting why on each promoted helper):
   - `Common.lean`: `elementaryWeight_node_replicate_leaf`,
     `convAt_singleton_leaf_eq`,
     `bSeries_node_replicate_leaf_append_replicate_singleton_leaf`,
     `bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf`,
     `bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf_append_replicate_triple_leaf`,
     `prod_const_add_eq_powerset`, `pow_add_eq_powerset`.
   - `LeafFamilies.lean`: `convAt_node_mixed_leaf_singleton_leaf_at_i_eq`
     (used by `Replicate.lean`'s standalone triple-leaf and parametric
     all-triple-leaf), `convAt_double_leaf_eq` (used by
     `Mixed3Way.lean`), `double_leaf_kept_pow_expand` (used by
     `Mixed3Way.lean`), `bWeighted_kept_double_leaf_summand_eq`
     (used by `Mixed3Way.lean`).
   - All other `private` helpers stayed `private` inside their new
     home file.

4. Replaced the original `OpenMath/ButcherGroup/Section384SlicesMixed.lean`
   with a 33-line umbrella that imports the four new submodules.

5. Surprise: discovered `OpenMath/ButcherGroup/Section384SlicesQuadMixed.lean`
   (cycles 559–561) had carried inline duplicate `private` copies of
   `convAt_singleton_leaf_eq`, `elementaryWeight_node_replicate_leaf`,
   `elementaryWeight_node_replicate_singleton_leaf`,
   `elementaryWeight_node_replicate_leaf_append_replicate_singleton_leaf`,
   `bSeries_node_replicate_leaf_append_replicate_singleton_leaf`, and
   `convAt_node_mixed_leaf_singleton_leaf_at_i_eq`. Once the split
   promoted four of those to non-`private` in `Common.lean` /
   `LeafFamilies.lean`, the duplicates produced
   "non-private declaration … has already been declared" errors.
   Resolution: dropped all six duplicates from the QuadMixed file and
   let the imports from `Section384SlicesMixed` carry them.
   (Side benefit: QuadMixed dropped from 1032 → 788 lines.)

## Result
SUCCESS. `lake build` is green (8082 jobs).

File sizes after split:
- `OpenMath/ButcherGroup/Section384SlicesMixed.lean`: 33 lines
  (umbrella).
- `Section384SlicesMixed/Common.lean`: 475 lines.
- `Section384SlicesMixed/LeafFamilies.lean`: 1200 lines.
- `Section384SlicesMixed/Mixed3Way.lean`: 1145 lines.
- `Section384SlicesMixed/Replicate.lean`: 670 lines.

Total: 3523 lines across the new files (vs. 3389 lines in the old
monolith, +134 lines coming from the per-file boilerplate
imports/namespace headers and the helper-promotion comments). Net
reduction in the *largest* file: 3389 → 1200 lines (the new largest).

All public deliverables listed in the strategy resolve under their
existing fully-qualified names. Verified by `lake build` succeeding,
which transitively rebuilt:
- `OpenMath/ButcherGroup.lean` (consumes
  `IsG1Equiv.product_congr_le_two`,
  `IsG1Equiv.product_congr_node_replicate_leaf`,
  `IsG1Equiv.product_congr_node_replicate_singleton_leaf`,
  `IsG1Equiv.product_congr_node_replicate_double_leaf`,
  `IsG1Equiv.product_congr_node_replicate_triple_leaf`,
  `IsG1Equiv.product_congr_node_triple_leaf`, etc.)
- `OpenMath/ButcherGroup/Section384SlicesQuadMixed.lean`
  (consumes the cycle 549 / 552-553 / 557 closed-form helpers).

No new live `sorry`. No semantic change to any theorem statement.

## Dead ends
None. The split followed straightforwardly from the section markers
already in the source.

## Discovery
- The QuadMixed duplicate-definition pattern (cycle 564 surprise) is
  worth keeping in mind: when a future cycle moves a helper between
  files, grep across the whole `OpenMath/ButcherGroup/` tree for any
  copy-pasted private duplicates before promoting access. The
  duplicates were silent bloat under the previous file-scoped
  `private`.
- `OpenMath/ButcherGroup.lean` is also currently 3034 lines (just
  over the 3000 approaching-cap line). The cycle 564 strategy
  explicitly deferred splitting it. Note for a future cycle: that
  file's natural seams are the per-tree-shape `IsG1Equiv.product_congr_node_*`
  theorems plus their `QuotEquiv.bSeriesHom_product_*` quotient lifts,
  which already follow the same family structure as the new
  `Section384SlicesMixed/*` submodules.

## Suggested next approach
Per the cycle 564 strategy preview: the next cycle's natural target
is the mixed leaf + triple-leaf parametric family
`BTree.node (List.replicate a BTree.leaf ++ List.replicate b
(BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))`, reusing
`tripleLeafChoiceFunctionCoef` / `tripleLeafChoiceTree` from cycle
563. That family lands in `Section384SlicesMixed/Replicate.lean`
(now the natural home of the all-triple-leaf machinery).

If a cycle wants to do another structural split, the `OpenMath/ButcherGroup.lean`
file is the next candidate (3034 lines, just past the approaching-cap
line). Suggested seams: split off the `IsG1Equiv.product_congr_node_*`
theorems plus their quotient lifts into a sibling
`OpenMath/ButcherGroup/G1ProductCongr.lean`, leaving the umbrella for
the post-§384 quotient lift, `IsRKEquivalentExt` / `IsG1Equiv` / `G1`
infrastructure, and `IsG1Equiv.product_congr_le_two`. Defer the split
itself to a dedicated cycle so it doesn't compete with proof work.
