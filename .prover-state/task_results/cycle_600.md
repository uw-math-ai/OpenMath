# Cycle 600 Results

## Worked on
`OpenMath/ButcherGroup/Section386Aug.lean` and `OpenMath/RootedTree.lean`,
laying the depth-3 mixed-children scaffold for unital augmented convolution
associativity.  Cycle 598 closed depth-1, cycle 599 closed depth-2; this
cycle stops short of the depth-3 headline (`mul_assoc_at_node_depth_three_children`)
but lands all the structural cons recurrences and bSeries expansion
lemmas needed for it.

## Approach
Sorry-first.  The strategy authorised either the parametric
`forestSum_assoc_children_order_le p` strong induction or the slightly
weaker depth-3 fallback.  The parametric form is blocked by a
cut-associativity Hopf-algebra identity (issue
`section386aug_strong_induction_obstruction.md`), so the cycle pursued the
fallback.  Two new depth-3 head shapes appear that did not exist at
depth-2: the two-children pair `BTree.node [a, b]` (with `a, b` of order
≤ 1) and the singleton-of-singleton `BTree.node [BTree.node [e]]` (with
`e` of order ≤ 1).  Each needed its own cons recurrence and bSeries
expansion in the same style as the depth-1 and depth-2 helpers.

## Result
SUCCESS for the scaffold.  Landed:

- `BTree.order_le_three_iff` (`RootedTree.lean`) — closed-form
  enumeration of the ten BTrees with order ≤ 3, plus the helper
  `eq_nil_or_singleton_or_pair_of_order_sum_le_two`.
- `forestSum_cons_node_pair_depth_one` — keep-root branch enumerates
  four trunks `node [a, b]`, `node [a]`, `node [b]`, `node []`.
- `forestSum_cons_node_singleton_node_singleton_depth_one` — keep-root
  branch enumerates three trunks `node [node [e]]`, `node [node []]`,
  `node []`.
- Compact `forestSum`-style wrappers for both.
- `bSeriesConvAug_node_cons_node_pair_depth_one_expand_compact` and
  `bSeriesConvAug_node_cons_node_singleton_node_singleton_depth_one_expand_compact`.

`rg -n "sorry" OpenMath/ButcherGroup/Section386Aug.lean OpenMath/RootedTree.lean`
reports no sorrys.  `lake env lean OpenMath/ButcherGroup/Section386Aug.lean`
and `lake build` both complete successfully.

The depth-3 headline `mul_assoc_at_node_depth_three_children` was NOT
landed this cycle.  It requires four new `shift_*_agg` lemmas (one per
new head shape: pair, singleton-of-singleton, plus reused `singleton`
and `node`/`leaf`) and a head-case dispatch with ten subcases (per
`BTree.order_le_three_iff`).  Estimated ~600 lines, beyond a single
cycle's reach.

## Dead ends
- First attempt at the pair-shape proof tried `ring` to close after a
  single `hscale` per case.  Failed because `ring_nf` re-normalises
  scalars back inside the `List.map` lambda when combining like terms,
  so two opaque sums with identical-looking but distinct trunks were
  getting merged or left distinct inconsistently.  Switched to
  `linarith` after multiple `hscale` applications (one per non-`1` α
  coefficient that decorates a kept-root cut), which treats each unique
  `(coeff, trunk)` map-sum pair as an opaque atom and closes by linear
  permutation.
- First attempt at the singleton-of-singleton proof tried to expand the
  inner `node [e]` `innerCut` via the recursive definition plus `simp`
  on `BTree.innerCutForest`.  The `match head.1 with | none ⇒ [] | some
  trunk ⇒ ...` did not reduce because the `head` came from a `List.map`
  whose argument list wasn't fully concretised.  Replaced with explicit
  closed-form `hcut` lemmas for both `node [node [BTree.leaf]]` and
  `node [node [BTree.node []]]`, computed by `simp [BTree.innerCut,
  BTree.innerCutForest]`.  This took two iterations to get the right
  list order (`(some _, 1)` for the no-prune cut comes BEFORE the
  inner-leaf-prune `(some _, α leaf)` cut, not after — order is
  determined by the recursive flatMap on the inner forest).

## Discovery
- For a depth-3 head `node [a, b]` with both children of order ≤ 1 the
  keep-root branch produces four distinct trunks (`node [a, b]`,
  `node [a]`, `node [b]`, `node []`).  When `a = b`, the two cross
  trunks `node [a]` and `node [b]` collapse to the same shape and add
  with a factor of 2 — this matters for the `linarith` step, which sees
  the two summands as the same opaque term.
- For a depth-3 head `node [node [e]]` the keep-root branch has FOUR
  trunks (the prune-all `(none, ...)` plus three `(some _, ...)`):
  `node [node [e]]`, `node [node []]`, and `node []`.  The order of
  these in the list comes from the inner `node [e].innerCut`'s order:
  `(none, α(node[e]))`, `(some(node[e]), 1)`, then `(some(node[]), α e)`
  — so the `node [node []]` trunk lands AFTER the no-prune `node [node
  [e]]` trunk in the outer list.

## Suggested next approach
Cycle 601 should land `mul_assoc_at_node_depth_three_children` using the
following template, mirroring cycle 599:

1. **`shift_pair_agg`**: lift the pair-shape pointwise expansion
   (`bSeriesConvAug_node_cons_node_pair_depth_one_expand_compact`) to
   the L-aggregation that appears inside
   `forestSum α (Aug(βγ).shiftBy (node [a, b])) cs`.  Combine with the
   tail IH instantiated at `γ`, `γ.shiftBy (node [])`, `γ.shiftBy
   (node [a])`, `γ.shiftBy (node [b])`, and `γ.shiftBy (node [a, b])`
   for each (a, b) ∈ {leaf, node[]}².  Close by `linear_combination`.
2. **`shift_singleton_node_singleton_agg`**: same shape, three trunks.
3. Reuse cycle 599's `shift_singleton_agg` and `shift_node_agg` for the
   five depth-≤2 head shapes that survive into depth-3.
4. **`forestSum_assoc_depth_three`**: list induction on `children`,
   dispatching the cons head via `BTree.order_le_three_iff` to one of
   the ten head-shape branches.  Each branch follows the cycle 599
   template (cons split, aggregate shift, tail IH instantiation,
   `linear_combination`).
5. **`mul_assoc_at_node_depth_three_children`**: apply
   `forestSum_assoc_depth_three` and reduce via `bSeriesConvAug_node`.

If cycle 601 also stalls (the pair-shape `shift_agg` is the riskiest
piece — it needs to handle the four-trunk fan-out at the L-aggregation
step), fall back to landing each shift_agg as its own cycle.

The cut-associativity obstruction blocking the parametric form is
unchanged; revisit only with the BTree-size strong-induction route from
the issue file's "Possible solutions" §3.
