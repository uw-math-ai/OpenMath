# Issue: §388 cancellation peeling lemma

## Status

CLOSED in cycle 577.

## Closed steps

- **Step 1**: `OpenMath/ButcherGroup/Section386Conv.lean` now proves the
  canonical no-cut count pair
  `innerCut_canon_count` / `innerCutForest_canon_count`, then uses it to
  prove
  `bSeriesConv_eq_root_plus_nonRoot`.
- **Step 3**: `OpenMath/ButcherGroup.lean` now proves
  `bSeriesConv_inverseCoeff_cancel_node`, the node-level cancellation
  obtained from the peeling lemma and `QuotEquiv.inverseCoeff_node_eq`.

## Resolution details

The count proof follows Path (1): a private mutual `List.countP`
induction.  The forest cons case reduces `countP` across
`List.flatMap` / `List.map`; the head branch contributes exactly when
the head cut is `(some head, 1)`, and the tail contributes exactly when
the tail cut list is canonical.

The node case also needs the forest-level structural classification that
was internal to cycle 576's proof, so cycle 577 added a private
`innerCutForest_root_only_at_full_order` helper.  This identifies the
unique forest preimage of the no-cut node entry.

One correction from the planner sketch: the displayed Step 3 theorem
without the leading `q.bSeries (BTree.node children)` term is not implied
by the recursion.  Peeling gives `q.inverseCoeff node + nonRoot`; this
cancels to zero only after adding the original node coefficient, exactly
as stated by `QuotEquiv.inverseCoeff_node_eq`.  The landed theorem
therefore proves the algebraic node cancellation:

```lean
q.bSeries (BTree.node children)
  + bSeriesConv q.bSeries q.inverseCoeff (BTree.node children) = 0
```

## Remaining §388 frontier

- Prove the symmetric direction where `q.inverseCoeff` is the first
  convolution argument.
- Use the two-sided cancellation facts to define and lift `G1.inv`, then
  finish the `Group (G1 p)` instance.
