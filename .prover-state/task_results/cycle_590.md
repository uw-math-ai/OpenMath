# Cycle 590 Results

## Worked on
Primary task (Theorems A and B): the two-child order-2 sanity case
`BTree.node [BTree.node [BTree.leaf], BTree.node [BTree.leaf]]` in
`OpenMath/ButcherGroup/Section386Aug.lean`.

## Approach
Wrote a sorry-first scaffold for:

- `bSeriesConvAug_two_singleton_leaves` (Theorem A) — closed form on
  the two parallel order-2 children.
- `mul_assoc_at_two_singleton_leaves` (Theorem B) — depth-3 unital
  associativity at the same shape.

Plus three private inner-trunk closed-form helpers needed by Theorem
B's right-hand expansion of the `(βγ)` convolution on the asymmetric
two-child trunks that appear during the cut enumeration:

- `bSeriesConvAug_node_singleton_leaf_node_nil` for trunk
  `node [node [leaf], node []]`.
- `bSeriesConvAug_node_nil_node_singleton_leaf` for trunk
  `node [node [], node [leaf]]`.
- `bSeriesConvAug_two_node_nils` for trunk `node [node [], node []]`.

Submitted two Aristotle scaffolds under
`.prover-state/aristotle_scaffolds/cycle_590/`:

- `bSeriesConvAug_two_singleton_leaves.lean`
- `mul_assoc_at_two_singleton_leaves.lean`

The first submission queued (project id
`5331994b-f61b-4d50-9ab7-aab42b7eef09`); the second returned HTTP 429
verbatim ("You have too many requests in progress. Please cancel or
wait for a project to complete before starting a new one."). Per the
documented one-batch-only policy I did not retry. Manual closure
proceeded immediately because both proofs reduce to direct
`simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]; ring`
unfoldings (Theorem A) plus a `simp only` rewrite chain through the
inner closed forms (Theorem B).

## Result
SUCCESS. Both theorems land sorry-free.

### Theorem A — exact RHS Lean accepts
```
α.toFun (BTree.node [BTree.node [BTree.leaf],
    BTree.node [BTree.leaf]]) * β.emptyVal
  + β.toFun (BTree.node [BTree.node [BTree.leaf],
      BTree.node [BTree.leaf]])
  + α.toFun (BTree.node [BTree.leaf]) ^ 2
      * β.toFun (BTree.node [])
  + 2 * α.toFun (BTree.node [BTree.leaf])
      * β.toFun (BTree.node [BTree.node [BTree.leaf]])
  + 2 * α.toFun (BTree.node [BTree.leaf]) * α.toFun BTree.leaf
      * β.toFun (BTree.node [BTree.node []])
  + α.toFun BTree.leaf
      * β.toFun (BTree.node [BTree.node [BTree.leaf], BTree.node []])
  + α.toFun BTree.leaf
      * β.toFun (BTree.node [BTree.node [], BTree.node [BTree.leaf]])
  + α.toFun BTree.leaf ^ 2
      * β.toFun (BTree.node [BTree.node [], BTree.node []])
```
Closed by `simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]; ring`.

### Theorem B
Closed by rewriting both sides with Theorem A, applying the existing
`bSeriesConvAug_*` closed forms (including the three new private
helpers), the unital hypotheses on `β.emptyVal` and `γ.emptyVal`, and
finishing with `ring`.

## Aristotle status
- `bSeriesConvAug_two_singleton_leaves`: QUEUED, project id
  `5331994b-f61b-4d50-9ab7-aab42b7eef09`.
- `mul_assoc_at_two_singleton_leaves`: HTTP 429 verbatim ("You have
  too many requests in progress. Please cancel or wait for a project
  to complete before starting a new one."). Single batch policy → no
  retry.

Both manually closed in this cycle independent of Aristotle.

## Stretch task
The parametric replicate closed form for
`bSeriesConvAug α β (node (replicate n (node [leaf])))` was identified
but not landed.  See the new issue file
`.prover-state/issues/butcher_section386_aug_replicate_singleton_leaf.md`
for the full three-branch parameterization (disjoint
`(S₁, S₂) : Finset (Fin n) × Finset (Fin n)`) and a sketch of the
list-level combinator that would prove it.  The associated unital
associativity headline at this family additionally needs a new
disjoint-pair binomial identity that is **not** a direct rewrite of
`replicate_leaf_assoc_aux`.

## Dead ends
None. The three private helpers were anticipated by the strategy
note ("If `ring` leaves a residual, it will be due to a missing inner
closed form for some sub-shape that appears"), so the pattern was
just to enumerate which `(βγ)`-applied trunks appear in the Theorem A
expansion and add the matching closed form.

## Discovery
The 9-entry forest enumeration on two parallel order-2 children
naturally produces three asymmetric two-child trunks of total order
≤ 3 (`[X, node []]`, `[node [], X]`, `[node [], node []]` where
`X = node [leaf]`).  Each closes by the same single-step
`simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]; ring`
recipe that closed Theorem A — the inner-trunk direct evaluations
are not harder than the outer one.  Position ordering of the trunk
children is load-bearing: a symmetric-powerset closed form would
collapse `[X, node []]` and `[node [], X]` and is therefore
distinguishable as wrong without a counterexample evaluation.

## Suggested next approach
Two possible next cycles:

1. **Combinator-first design cycle** for the parametric replicate
   closed form (issue
   `butcher_section386_aug_replicate_singleton_leaf.md`).  Define
   the disjoint-pair `threeChoice n` enumeration and the trunk
   reindexing combinator before any sorry-first scaffold lands, since
   the associativity binomial identity is genuinely new.
2. **Continue the case-by-case ladder** to the next-smallest shape
   the planner deems load-bearing for the §388 antipode work — for
   example, three parallel order-2 children, or the
   `node [BTree.leaf, BTree.node [BTree.leaf]]` mixed shape, both of
   which exercise the same three-branch per-child structure but with
   one position the existing `node_replicate_leaf` machinery already
   covers.
