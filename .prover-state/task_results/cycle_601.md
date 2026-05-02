# Cycle 601 Results

## Worked on
Butcher Section 386 depth-3 unital augmented associativity prerequisites in
`OpenMath/ButcherGroup/Section386Aug.lean`: the aggregate shift lemmas
`shift_pair_agg` and `shift_singleton_node_singleton_agg`.

## Approach
Followed the cycle-599 `shift_singleton_agg` pattern.  First added both
lemmas sorry-first and checked the file.  Then, for each head shape, rewrote
the shifted L-aggregation by a pointwise compact expansion from cycle 600,
lifted that expansion over the inner-cut forest list by induction, and closed
the residual algebra with `linear_combination` against tail-IH instances.

## Result
SUCCESS.  Landed both required lemmas sorry-free:

- `shift_pair_agg`, using IH at `gamma`, `gamma.shiftBy (node [])`,
  `gamma.shiftBy (node [a])`, `gamma.shiftBy (node [b])`, and
  `gamma.shiftBy (node [a, b])`.
- `shift_singleton_node_singleton_agg`, using IH at `gamma`,
  `gamma.shiftBy (node [])`, `gamma.shiftBy (node [node []])`, and
  `gamma.shiftBy (node [node [e]])`.

Verification completed:

- `rg -n "sorry" OpenMath/ButcherGroup/Section386Aug.lean` found no hits.
- `lake env lean OpenMath/ButcherGroup/Section386Aug.lean` succeeded.
- `lake build` succeeded.

## Dead ends
No mathematical blocker.  A first `shift_pair_agg` script had two proof-script
issues: an extra `ring` after a rewrite that had already closed the pointwise
goal, and a line break that split the `simp ... at` target list.  Both were
fixed locally.

Lean LSP goal inspection timed out on the large new proof block after 120s, so
the final verification used the standard Lean and Lake commands instead.

## Discovery
Factoring the tail associativity hypothesis into an explicit top-level
argument makes the new aggregate shift lemmas reusable for the future
`forestSum_assoc_depth_three` list induction.  No unitality hypothesis is
needed directly in these aggregate shift lemmas; all unitality remains carried
by the future source of the tail IH.

For these depth-3 shapes, the final `linear_combination` is stable as long as
the RHS sums are first rewritten into `bSeriesConvAug beta delta (node xs) -
beta(node xs) * delta.emptyVal` form.  No `ring_nf` was needed at the final
aggregate step.

## Suggested next approach
Use the new top-level `shift_pair_agg` and
`shift_singleton_node_singleton_agg` in `forestSum_assoc_depth_three`.  The
next proof should be a list induction over children, dispatching the cons head
with `BTree.order_le_three_iff`; reuse the existing depth-1/depth-2 local
head-case patterns for the old shapes and these two aggregate lemmas for the
new pair and singleton-of-singleton shapes.
