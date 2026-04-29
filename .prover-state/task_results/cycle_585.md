# Cycle 585 Results

## Worked on

Butcher §386 unital augmented convolution in
`OpenMath/ButcherGroup/Section386Aug.lean`.

Targets:
- `bSeriesConvAug_node_node_nil`
- `mul_assoc_at_node_node_nil`
- `bSeriesConvAug_node`

## Approach

Followed the cycle 585 sorry-first path: added the three theorem
surfaces, checked the file with the new `sorry`s, then closed the
small depth-2 lemmas before submitting the single general node split
scaffold to Aristotle.

For `BTree.node [BTree.node []]`, direct unfolding of
`bSeriesConvAug`, `BTree.innerCut`, and `BTree.innerCutForest` produced
the expected three terms.  The two tail terms appeared in the opposite
order from the target, so the proof uses `add_comm` / `add_left_comm`
in the final `simp`.

For `mul_assoc_at_node_node_nil`, the two closed forms reduce both
sides to a polynomial identity after substituting
`β.emptyVal = 1` and `γ.emptyVal = 1`; `ring` closes the goal.

For `bSeriesConvAug_node`, unfolding `bSeriesConvAug` and rewriting
the node case of `BTree.innerCut` exposes the root-prune head and the
mapped forest-cut tail.  A single simplification with `List.map_cons`,
`List.map_map`, and `Function.comp_def` closes the theorem.

## Result

SUCCESS.

Landed:
- `bSeriesConvAug_node_node_nil`
- `mul_assoc_at_node_node_nil`
- `bSeriesConvAug_node`

Verified:
- `lake env lean OpenMath/ButcherGroup/Section386Aug.lean`
- `lake env lean OpenMath/ButcherGroup.lean`
- `lake env lean .prover-state/aristotle_scaffolds/cycle_585/bSeriesConvAug_node.lean`

No live `sorry` remains in the modified §386 Lean file.

## Dead ends

The literal planner proof for `bSeriesConvAug_node_node_nil` with
`add_assoc` alone did not close because Lean normalized the two tail
summands as
`α(node []) * β(node []) + β(node [node []])`, while the target states
`β(node [node []]) + α(node []) * β(node [])`.  Adding commutative
normalization closed it.

## Discovery

The symmetric node split is already definitional after the node-case
`innerCut` rewrite.  No separate list reindexing lemma is needed for
this closed form; the future associativity lift will need reindexing
only when comparing nested uses of this split.

Aristotle submission:
- Scaffold: `.prover-state/aristotle_scaffolds/cycle_585/bSeriesConvAug_node.lean`
- Result: HTTP 429, "too many requests in progress"
- Action: no retry, per strategy.  The scaffold was then closed
  manually with the same proof as the live theorem.

## Suggested next approach

Use `bSeriesConvAug_node` as the node-case normalization for the next
associativity cycle.  The remaining hard step is the list-level
reindexing over `BTree.innerCutForest children` needed to align the
two nested augmented convolutions under unital hypotheses.
