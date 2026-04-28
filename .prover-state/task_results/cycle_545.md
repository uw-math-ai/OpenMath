# Cycle 545 Results

## Worked on

Butcher §38 / §384. Attempted the planned unified all-trivial-children
closed form, but landed the scheduled Option B finite mixed-shape slice after
finding that the proposed `IsConvAtUnit` hypothesis is too weak for the
`t₂.bSeries` kept side.

Added:
- `ButcherProduct.IsConvAtUnit`
- `ButcherProduct.IsConvAtUnit_leaf`
- `ButcherProduct.IsConvAtUnit_node_nil`
- `ButcherProduct.bSeries_node_leaf_node_nil_eq`
- `ButcherProduct.bSeries_node_node_nil_leaf_eq`
- `ButcherProduct.bSeries_node_leaf_leaf_node_nil_eq`
- the three matching `QuotEquiv.bSeriesHom_product_...` lifts
- the three matching `IsG1Equiv.product_congr_...` slices

## Approach

The planned `bWeighted_convAt_node_all_unit_eq` would need to identify the
kept product

`∏ p ∈ Sᶜ, ∑ j, t₂.A i j * convAt t₂ coef (children.get p) j`

with an elementary-weight product inside `t₂.bSeries`. But `convAt = 1`
does not imply `t₂.elementaryWeight = 1`; the two notions depend on different
data. I therefore did not add the false parametric theorem.

For the fallback shapes, I transported each mixed `node []` occurrence to a
leaf at the `bSeries` level. This works because both `BTree.leaf` and
`BTree.node []` have elementary weight `1` for every tableau. The existing
cycle 542 theorem `bSeries_node_replicate_leaf_eq` then supplies the closed
form for arities `2` and `3`.

The quotient lifts are direct `Quotient.inductionOn₂ + simpa` proofs. The G1
slices mirror `product_congr_node_replicate_leaf`: the head term closes with
`hq` at the mixed root, the cut factor closes with `hq` at `BTree.leaf`, and
the kept all-leaves subtrees close with `hr` plus the existing private
`order_node_replicate_leaf` helper.

## Result

SUCCESS for Option B. The unified Option A theorem did not land because the
statement needs a stronger hypothesis than `IsConvAtUnit`.

Verification:
- `lake env lean OpenMath/ButcherGroup/Section384.lean` — clean.
- `lake build OpenMath.ButcherGroup.Section384` — clean.
- `lake env lean OpenMath/ButcherGroup.lean` — clean.
- `lake build OpenMath.ButcherGroup` — clean.
- `rg -n 'sorry' OpenMath/ButcherGroup OpenMath/ButcherGroup.lean` — empty output.

## Dead ends

The target `bWeighted_convAt_node_all_unit_eq` was blocked for mathematical,
not reindexing, reasons. A one-stage tableau with `A = 1/2` and a coefficient
choice making `convAt (BTree.node [BTree.leaf]) = 1` still has
`elementaryWeight (BTree.node [BTree.leaf]) = 1/2`, so the proposed kept-side
`t₂.bSeries` conclusion cannot follow from `IsConvAtUnit` alone.

## Discovery

No new public order helper in `RootedTree.lean` was needed. The fallback G1
proofs reused the existing private `order_node_replicate_leaf` helper in
`OpenMath/ButcherGroup.lean`.

No new private helpers were added or relocated.

## Aristotle outcome

Submitted the sorry-first batch attempt after the scaffolding compiled, but
Aristotle rejected the first submission with HTTP 429:
`too many requests in progress`. No project ID was created, so there was no
result to poll or merge. I still waited the required 30 minutes before manual
closure.

## Suggested next approach

Replace the planned unified hypothesis with a stronger predicate requiring
both:
- `∀ j, convAt t₂ coef c j = 1`
- `∀ j, t₂.elementaryWeight c j = 1`

or specialize the parametric theorem directly to
`∀ p, children.get p = BTree.leaf ∨ children.get p = BTree.node []`.
That should make the all-trivial-children kept-side `bSeries` statement true.
