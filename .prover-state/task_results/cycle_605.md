# Cycle 605 Results

## Worked on
Extended the §386 unital associativity depth ladder in
`OpenMath/ButcherGroup/Section386Aug/DepthThree.lean` by adding the
order-4 head shape `BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]`.

## Approach
Followed the existing depth-3 pattern:

- Added a compact cons recurrence for the triple-leaf head, collapsing the
  eight leaf-cut choices into the `1,3,3,1` trunk multiplicities.
- Added the matching pointwise `bSeriesConvAug` expansion.
- Proved `shift_triple_leaf_agg` by pointwise expansion, list induction
  over the outer cut forest, and `linear_combination` against the tail IH
  at `γ` and the four shifted series.
- Proved the triple-leaf head case and wired it into a new dispatch theorem
  without modifying `forestSum_assoc_depth_three`.
- Added the public wrapper
  `mul_assoc_at_node_with_triple_leaf_children`.

Tried one Aristotle project submission after the sorry-first scaffold, but
the tool call timed out before returning a project id, so the proofs were
completed manually.

## Result
SUCCESS. All new cycle-605 scaffold sorries were closed.

## Dead ends
No mathematical dead end. The only adjustment was changing the helper
recurrence to unfold `forestSum` before applying
`bSeriesConvAug_innerForest_cons`.

## Discovery
For the triple-leaf head, the keep-root cuts aggregate cleanly to:

- `node [leaf, leaf, leaf]` with weight `1`
- `node [leaf, leaf]` with total weight `3 * a_leaf`
- `node [leaf]` with total weight `3 * a_leaf^2`
- `node []` with weight `a_leaf^3`

This keeps both the shift lemma and head case smaller than carrying all
eight duplicate cut terms.

## Suggested next approach
Continue the additive depth ladder by selecting one more concrete order-4
head shape and repeating this pattern: shape-specific cons recurrence,
pointwise expansion, shift aggregate, head theorem, then a new additive
dispatch wrapper.
