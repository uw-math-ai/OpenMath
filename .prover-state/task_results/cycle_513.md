# Cycle 513 Results

## Worked on
`OpenMath/ButcherGroup.lean` §381 cross-stage equivalence invariants, §387
quotient-power arithmetic, and a small §381 padding natAdd follow-up.

## Approach
Sorry-first scaffolded the requested batch and verified it with:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean
```

Submitted the planned Aristotle batch:

- Job A: `IsRKEquivalentExt.satisfiesTreeCondition_iff`
- Job B: `IsRKEquivalentExt.hasTreeOrder_iff`
- Job C: `QuotEquiv.weightsSum_npow_four`

All three returned HTTP 429 immediately: "You have too many requests in
progress." Per strategy, I did not retry and closed the goals manually.

## Result
SUCCESS.

Landed Tier 1:

- `IsRKEquivalentExt.satisfiesTreeCondition_iff`
- `IsRKEquivalentExt.hasTreeOrder_iff`

Landed Tier 2:

- `QuotEquiv.weightsSum_npow_four`
- `QuotEquiv.cSum_npow_four`
- `QuotEquiv.npowStages_npow_eq_npowStages_mul`

Landed the safe part of Tier 3:

- `ButcherTableau.padRight_elementaryWeight_natAdd_node_of_ne_nil`

The Tier 3 statement includes `children ≠ []` because
`BTree.node []` has elementary weight `1`, not `0`.

Updated `plan.md` under §381 and §387. The Current Target and backlog queue
were unchanged.

## Dead ends
The first direct quotient-induction proof of
`IsRKEquivalentExt.hasTreeOrder_iff` was brittle because the dependent
cross-stage hypothesis was not generalized in the desired shape. I replaced
it with the private helper `hasTreeOrder_iff_forall`, unfolding quotient
`hasTreeOrder` to the expected universal tree-condition form before applying
`forall_congr'`.

## Discovery
`IsRKEquivalentExt.satisfiesTreeCondition_iff` is just the existing
`bSeriesHom_eq` applied pointwise and rewritten through
`QuotEquiv.satisfiesTreeCondition_iff_bSeries`.

The natAdd elementary-weight closure is false for the degenerate node
`BTree.node []`; future natAdd lemmas should either require nonempty child
lists or work with order hypotheses that exclude the degenerate node.

The §384 convolution was deliberately deferred this cycle. No tree-indexed
coefficient product, tautological `bSeriesConv`, or `ButcherProduct` change
was attempted.

## Suggested next approach
Use the new cross-stage `satisfiesTreeCondition_iff` and `hasTreeOrder_iff`
as the quotient-facing surface for future `G₁` packaging. For padding
natAdd-side work, phrase node vanishing with `children ≠ []` or derive the
nonemptiness from a positive order/classification hypothesis.
