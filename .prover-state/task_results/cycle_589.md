# Cycle 589 Results

## Worked on
Primary task (A): the first order-2 partial-trunk-cut tree
`BTree.node [BTree.node [BTree.leaf]]` in
`OpenMath/ButcherGroup/Section386Aug.lean`.

## Approach
Added the sorry-first structure for:

- `bSeriesConvAug_singleton_singleton_leaf`
- `mul_assoc_at_singleton_singleton_leaf`

The cut enumeration has four branches:

- `(none, α(node [node [leaf]]))`, contributing
  `α(node [node [leaf]]) * β.emptyVal`
- `(some (node []), α(node [leaf]))`, contributing
  `α(node [leaf]) * β(node [])`
- `(some (node [node [leaf]]), 1)`, contributing `β(node [node [leaf]])`
- `(some (node [node []]), α(leaf))`, contributing the partial-trunk term
  `α(leaf) * β(node [node []])`

Submitted two Aristotle scaffolds under
`.prover-state/aristotle_scaffolds/cycle_589/`:

- `bSeriesConvAug_singleton_singleton_leaf.lean`
- `mul_assoc_at_singleton_singleton_leaf.lean`

Both submissions immediately returned HTTP 429, so no 30-minute polling was
useful. I proceeded manually per the cycle 589 Aristotle policy.

## Result
SUCCESS.

`bSeriesConvAug_singleton_singleton_leaf` closes by direct unfolding of
`bSeriesConvAug`, `BTree.innerCut`, and `BTree.innerCutForest`, followed by
`ring`.

`mul_assoc_at_singleton_singleton_leaf` closes by rewriting both sides with
the existing small closed forms plus the new closed form, applying the
unital hypotheses on `β.emptyVal` and `γ.emptyVal`, and finishing with
`ring`.

I also added the required one-paragraph note to `plan.md`'s current §38
target section.

## Dead ends
None after the cut list was enumerated. The only mismatch with the strategy
text was that the genuine partial-trunk branch necessarily involves
`β.toFun (BTree.node [BTree.node []])`; omitting that coefficient would miss
the new branch.

## Discovery
The smallest order-2 partial-trunk case is still symbolically associative
under the existing unital hypotheses. The new summand
`α.toFun BTree.leaf * β.toFun (BTree.node [BTree.node []])` on the outer
closed form is exactly matched on the associativity check by the existing
`bSeriesConvAug_node_node_nil` closed form on the right-associated side.

## Suggested next approach
Generalize this four-branch audit into a list-level combinator for one
order-2 child position. A useful API would split each child choice into
fully pruned, fully kept, and partial-trunk-kept-with-inner-cut branches, so
future cycles can prove the `innerCutForest` reindexing theorem without
transporting the order-1 replicate proofs again.
