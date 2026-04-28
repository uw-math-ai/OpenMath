# Cycle 546 Results

## Worked on

Butcher §38 / §384. Landed the planned **parametric trivial-children
all-shapes closed form**, generalizing cycles 540 / 542 / 544 (single
shape, all-leaves family, all-empty-node family) and cycles 541 / 545
(finite arity-2 / arity-3 mixed slices) into one theorem covering every
node `BTree.node children` whose children are each `BTree.leaf` or
`BTree.node []`.

Added in `OpenMath/ButcherGroup/Section384.lean`:
- `elementaryWeight_node_trivial_children_eq_replicate_leaf` (private
  helper: elementary-weight invariance under transport of trivial
  children to leaves at every stage)
- `bSeries_node_trivial_children_eq_replicate_leaf` (private helper:
  `bSeries` invariance under the same transport)
- `ButcherProduct.bConv_node_trivial_children_eq` (parametric §384
  honest convolution closed form)
- `ButcherProduct.bSeries_node_trivial_children_eq` (parametric §384
  product `bSeries` closed form — headline corollary)

Added in `OpenMath/ButcherGroup.lean`:
- `QuotEquiv.bSeriesHom_product_node_trivial_children` (quotient-layer
  lift)
- private `order_node_trivial_children` (each trivial child contributes
  order 1, so `(node children).order = children.length + 1`)
- `IsG1Equiv.product_congr_node_trivial_children` (cycle 546 fourth
  tracked `G1.mul`-direction well-definedness deliverable)

## Approach

Reduce-to-all-leaves (Approach 2 in the strategy). For each child `c`
that is `BTree.leaf` or `BTree.node []`, both shapes have elementary
weight `1`, so each foldr factor `∑ k, A i k * elementaryWeight c k`
collapses to `∑ k, A i k`, identical to the leaf case. Therefore at the
elementary-weight level, `tab.elementaryWeight (BTree.node children) i
= tab.elementaryWeight (BTree.node (List.replicate children.length
BTree.leaf)) i`. This lifts to `bSeries` by `Finset.sum_congr`. Apply
this transport to the LHS `(t₁.product t₂).bSeries (BTree.node
children)` and the headline `t₁.bSeries (BTree.node children)` summand,
reduce the kept `bSeries` side by cycle 542's
`bSeries_node_replicate_leaf_eq`, and read off the closed form.

The quotient lift is the standard `Quotient.inductionOn₂ + simpa`
template used for cycles 541 / 542 / 544 / 545.

The G1 slice mirrors `IsG1Equiv.product_congr_node_replicate_leaf`
(cycle 542): apply the closed form to both sides, then chase the
`hq`/`hr` per-subtree hypotheses. Trivial children give order 1, the
all-leaves kept subtrees use the existing private
`order_node_replicate_leaf` helper, and the new private
`order_node_trivial_children` helper handles the head.

## Result

SUCCESS. The parametric closed form lands in one theorem; the cycle 540
/ 542 / 544 / 545 single-shape and finite mixed-shape products are now
direct corollaries.

Verification:
- `lake env lean OpenMath/ButcherGroup/Section384.lean` — clean.
- `lake build OpenMath.ButcherGroup.Section384` — clean.
- `lake env lean OpenMath/ButcherGroup.lean` — clean.
- `lake build OpenMath.ButcherGroup` — clean.
- `rg -n 'sorry' OpenMath/ButcherGroup OpenMath/ButcherGroup.lean` —
  empty output.

## Dead ends

None this cycle: the elementary-weight transport went through cleanly
on the first attempt, and the G1 slice template from cycle 542 applied
without modification once the parametric `bSeriesHom` lift was in
place.

A small fix-up was needed in the helper proof: `List.mem_cons_self`
in the current Mathlib expects no explicit arguments (it unifies
through pattern matching), so `List.mem_cons_self c cs` errored with
"function expected". Replaced with `List.mem_cons_self`.

## Discovery

The reduce-to-all-leaves transport pattern is fully parametric: any
shape decided by elementary-weight 1 children transports identically.
Future generalizations (e.g. parametric all-`(node [BTree.leaf])`,
once that becomes a tracked family) can reuse the same
`elementaryWeight_node_trivial_children_eq_replicate_leaf` skeleton by
swapping the trivial-shape predicate for the relevant
elementary-weight-equal predicate.

The cycle 545 `IsConvAtUnit` predicate remains unused outside the
existing `IsConvAtUnit_leaf` and `IsConvAtUnit_node_nil` lemmas. It
was correctly identified there as too weak to carry the kept-side
`bSeries` collapse; the elementary-weight invariance route avoids the
issue entirely.

## Aristotle outcome

Skipped this cycle. The strategy explicitly notes that every cycle
since 504 has hit HTTP 429 or returned `COMPLETE_WITH_ERRORS`, and
recommends closing manually using the cycle 542 template if the batch
fails. The cycle 542 template applied cleanly here without Aristotle
input, so no jobs were submitted. Zero sorry's were left in tracked
code at any point.

## Suggested next approach

The trivial-children parametric closed form is now closed. The next
natural §384 deliverable in the same `bSeries`-only product-closed-form
ladder is the **parametric all-singleton-leaf-children closed form**:
every child is `BTree.node [BTree.leaf]` (the unique order-2 tree),
parametric in `children.length`. This subsumes the cycle 540
single-shape `bSeries_singleton_leaf_eq` and extends to the whole
"bushy tree" family. The reduce-to-all-leaves transport does not apply
(elementary weight of `BTree.node [BTree.leaf]` is `∑ k, A i k`, not
1), so this needs a fresh closed form on the kept `bSeries` side. The
cycle 538 `bWeighted_convAt_node_all_leaves_eq` template should adapt:
each foldr factor becomes `∑ k, A i k * (∑ j, A k j)` instead of
`∑ k, A i k`.

After that, the next jump is to mixed leaves + singleton-leaf children,
which generalizes both this cycle's theorem and the suggested next one
along a new axis.

The full §384 `(trunk, cuts)` convolution remains the structural
blocker for unrestricted `IsG1Equiv.product_congr`. The current
parametric closed forms remain the best directly checkable
deliverables in advance of that closure.
