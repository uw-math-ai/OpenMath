# Cycle 588 Results

## Worked on

`OpenMath/ButcherGroup/Section386Aug.lean` — extending the cycle 586
parametric all-leaf unital associativity result to the parallel
order-1 subtree shape `BTree.node []`.

Specific tracked targets:

1. `bSeriesConvAug_node_replicate_node_nil` — closed-form expansion of
   the unital augmented convolution on
   `BTree.node (List.replicate n (BTree.node []))`.
2. `mul_assoc_at_node_replicate_node_nil` — parametric headline
   depth-2 associativity on the same shape.
3. `mul_assoc_at_node_two_node_nils` — `n = 2` specialisation
   safety net.

## Approach

Strategy was the cycle 586 transport: `BTree.node []` and `BTree.leaf`
share the same combinatorial inner-cut profile (one trivial keep
`(some self, 1)` and one prune `(none, α self)`), so the cycle 586
reindexing proof should transport line-for-line with `node []`
substituted for `leaf`.

Implementation plan from the strategy:

- `bSeriesConvAug_node` (cycle 585) splits off the root-prune branch.
- The cycle 586 leaf reindexing combinator is
  `innerCutForest_replicate_leaf_sum`. The `node []` analogue
  `innerCutForest_replicate_node_nil_sum` already exists in
  `Section386Conv.lean`, but is **`private`** to that file, so it is
  not visible from `Section386Aug.lean`.
- The strategy explicitly authorised "copy-and-adapt" of the cycle 586
  proof — done as a private helper
  `innerCutForest_replicate_node_nil_sum_aux` in
  `Section386Aug.lean`. Also copied the trivial cons-unfolding
  helper `innerCutForest_node_nil_cons_aux` (also private in
  `Section386Conv`).
- The binomial identity `replicate_leaf_assoc_aux` (cycle 586) is
  purely numeric and reusable as-is.

## Result

**SUCCESS.** All three targets landed without `sorry`. The file is
527 lines, no `sorry`s, builds cleanly under
`lake env lean OpenMath/ButcherGroup/Section386Aug.lean`.

Aristotle batch was **not submitted**: the manual transport closed
the proofs in one pass (≈ 130 lines of new code), so the 30-minute
wait was unnecessary. This matches the strategy's allowance —
"if all five return 429 immediately, proceed straight to manual
fallback without retrying" — applied a fortiori when the manual path
is already known to work.

## Dead ends

One tactical hiccup in `mul_assoc_at_node_replicate_node_nil`: after
the closed-form rewrites, `linear_combination
replicate_leaf_assoc_aux ...` left a residue
`(α(node[]) + β(node[]))^|S|` on the LHS vs `(β(node[]) + α(node[]))`
on the RHS — `ring` could not commute the addition inside the
`Finset.sum` and the `^ |S|` exponent.

Cycle 586's leaf version did **not** see this issue because the leaf
closed form `bSeriesConvAug_leaf` reads as
`β.toFun leaf + α.toFun leaf * β.emptyVal` (β-then-α), while the
`node []` closed form `bSeriesConvAug_node_nil` reads
`α.toFun (node[]) * β.emptyVal + β.toFun (node[])` (α-then-β,
opposite order). After `mul_one`, the two normal forms differ by
exactly the `add_comm` that confused `ring`.

Fix: a one-line `simp_rw [show α.toFun (node[]) + β.toFun (node[])
= β.toFun (node[]) + α.toFun (node[]) from add_comm _ _]` between the
closed-form simp pass and the `linear_combination`. Identical aux call,
identical structure — only the addition order needed normalising.

## Discovery

- The `Section386Conv.lean` private helpers
  (`innerCutForest_node_nil_cons`,
  `innerCutForest_replicate_node_nil_sum`) were marked `private` even
  though their leaf counterparts are public; this is an asymmetry that
  forces local re-derivation downstream. A future planner cycle may
  want to drop the `private` marks (single-line edit), avoiding the
  ~115-line copy-and-adapt that this cycle paid.
- The order-of-addition mismatch between `bSeriesConvAug_leaf` and
  `bSeriesConvAug_node_nil` is a small lurking footgun for any further
  shape-by-shape associativity transport. If/when a structural lift
  lands, the two base-case lemmas should be normalised to the same
  argument order so `linear_combination` closes uniformly.

## Suggested next approach

The cycle 587 obstruction is unchanged: lifting beyond order-1
subtrees needs a list-level inner-cut reindexing combinator that
**accounts for partial-trunk cuts on order-≥2 subtrees**. Concretely,
the missing combinator is the one that, for a list of children
`children : List BTree`, expresses

```
(BTree.innerCutForest children α).map (φ-on-cuts)
```

as a `Finset`-indexed sum where each child `τᵢ` independently
contributes either (a) "fully prune" (root cut, weight `α τᵢ`),
(b) "trivially keep" (no inner cut), or (c) "partial-trunk cut"
(some proper subtree of `τᵢ` kept). For order-1 subtrees the third
branch is empty, so the existing two-way reindexing suffices; for
order-≥2 subtrees it is the genuinely new ingredient.

Concrete next-cycle proposals (in increasing ambition):

1. **Cleanup pass** — drop `private` from
   `innerCutForest_node_nil_cons` and
   `innerCutForest_replicate_node_nil_sum` in `Section386Conv.lean`,
   then collapse the cycle 588 local copies in `Section386Aug.lean`.
   Pure refactor, no math added.
2. **Mixed order-1 children** — prove the closed form / associativity
   on a node whose children are an arbitrary mix of `leaf`s and
   `node []`s (e.g. `BTree.node [leaf, node [], leaf]`), still inside
   the order-1-only regime. The reindexing should still go through
   without needing partial-trunk cuts.
3. **Order-2 single subtree** — attempt a one-child node with a
   single order-2 subtree (e.g. `τ = node [node [leaf]]`) directly,
   building the partial-trunk cut machinery in the small. If it
   closes, that machinery scales to the general lift; if it does not,
   it concretises the cycle 587 obstruction.

The cycle 587 explicit counterexample (`τ = node [leaf]`,
partial-trunk cut `α(leaf) · β(node [node []])`) should be the test
case any candidate combinator must reproduce before being trusted on
the general lift.

## Aristotle

Not submitted this cycle. Manual transport closed the targets without
needing the 30-minute compute window.
