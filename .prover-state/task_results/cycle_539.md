# Cycle 539 Results

## Worked on

Butcher §384 honest bSeries-only convolution in
`OpenMath/ButcherGroup/Section384.lean`, specifically the mixed-leaf/node
kept-child closed form at the `convAt` level.

## Approach

Added the sorry-first statements for
`ButcherProduct.bWeighted_convAt_node_kept_eq` and
`ButcherProduct.bSeries_natAdd_node_kept_eq`, verified that the file
compiled with only those intended sorries, then attempted the mandated
Aristotle batch. Aristotle returned HTTP 429 immediately on the first
target (`bWeighted_convAt_node_kept_eq`), so no further Aristotle jobs
were submitted per the cycle strategy.

The manual proof bridges the left side from `convAt` back to
`rightAuxAtCoef` using `ButcherProduct.rightAuxAtCoef_eq_convAt`, applies
the existing trunk recursion
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion`, and then
case-splits each kept child. Leaf children simplify by
`ButcherProduct.rightAuxAtCoef_leaf`; node children are bridged back to
`convAt` with `ButcherProduct.rightAuxAtCoef_eq_convAt`.

The bSeries specialization is then a direct rewrite through
`ButcherProduct.bSeries_natAdd_eq_convAt` and the new weighted `convAt`
lemma.

## Result

SUCCESS.

- Landed `ButcherProduct.bWeighted_convAt_node_kept_eq`.
- Landed `ButcherProduct.bSeries_natAdd_node_kept_eq`.
- Added one depth-2 all-leaves-grandchildren collapse lemma,
  `ButcherProduct.bWeighted_kept_node_all_leaves_summand_eq`, converting
  the kept-node row-sum product for a fixed grandchild cut subset into
  `t₂.bSeries (BTree.node [BTree.node (List.replicate n BTree.leaf)])`.
- Updated `plan.md` in the Chapter 3 §384 entry and the §38 Current Target
  body.
- `lake env lean OpenMath/ButcherGroup/Section384.lean` succeeds.
- `lake build` succeeds (8075 jobs; only pre-existing warnings in unrelated
  modules were replayed).
- `rg -n "sorry" OpenMath/ButcherGroup/Section384.lean` finds no sorries.
- Lean LSP `lean_verify` reported no warnings for all three new theorem
  declarations.

## Dead ends

Aristotle was unavailable: the first `submit_file` attempt returned
HTTP 429 ("too many requests in progress"). The cycle strategy explicitly
said not to retry or wait in that case, so manual closure was used.

No Lean-side proof dead end remained. The clean proof avoided applying the
older fully expanded
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_eq`; using the
raw trunk recursion instead kept the node branch in the more useful
recursive `convAt` shape.

## Discovery

The mixed kept-child `convAt` theorem is shorter and more future-proof when
proved from `bWeighted_rightAuxAtCoef_node_trunk_recursion` rather than the
cycle 532 expanded kept theorem. That lets the final RHS match the desired
closed recursive auxiliary:

- kept leaf: `∑ j, t₂.A i j`
- kept node: `∑ j, t₂.A i j * convAt t₂ coef (BTree.node gc) j`

The existing private helper `elementaryWeight_node_replicate_leaf` also
immediately gives the depth-2 all-leaves-grandchildren summand collapse
once the complement-cardinality rewrite is isolated with
`Finset.card_compl` and `Fintype.card_fin`.

## Suggested next approach

Package the remaining full `(trunk, cuts)` closed form by `BTree.rec`:
each kept node branch should recursively contribute the same style of cut
subset sum, while leaf branches use the row-sum base case. Do not retry
`IsG1Equiv.product_congr` until that arbitrary-tree closed form is
available.
