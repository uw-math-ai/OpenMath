# Cycle 529 Results

## Worked on
Butcher §384 right-block convolution in `OpenMath/ButcherGroup.lean`,
specifically the trunk-side kept-leaf simplification
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq`.

## Approach
- Added the target theorem immediately after
  `ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion`.
- Followed the sorry-first workflow: first inserted the theorem with the
  intended proof skeleton and temporary `sorry`s, then checked the shape
  with `lake env lean`.
- Closed the proof manually by deriving
  `children.get p = BTree.leaf` from `hAllLeaf` and `List.get_mem`,
  rewriting the trunk recursion with `Finset.powerset_univ`, and using
  pointwise `Finset.sum_congr` / `Finset.prod_congr` rewrites. The kept
  factor then simplified by `ButcherProduct.rightAuxAtCoef_leaf`.
- Aristotle was not submitted this cycle because the cycle 529 strategy
  explicitly said not to burn the 30-minute queue on Aristotle jobs after
  repeated HTTP 429 / QUEUED failures in recent cycles.

## Result
SUCCESS. The new theorem landed:

`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq`

It states that under the all-leaves hypothesis on `children`, the
trunk-recursion RHS collapses each cut coefficient to `coef BTree.leaf`
and each kept recursive auxiliary factor to the plain row sum
`∑ j, t₂.A i j`.

## Dead ends
- The first sorry skeleton included
  `simp only [Finset.mem_univ, true_and]` after rewriting by
  `Finset.powerset_univ`; Lean reported that `simp` made no progress.
  The goal was already in the two-sided `∑ S ∈ Finset.univ` form, so the
  line was unnecessary.
- The initial closed proof produced unused-variable warnings from the
  intentionally unused `t₁` parameter and from product binders whose bodies
  are constant in the leaf-specialized expression. A harmless local witness
  for `t₁` and anonymous product binders removed the warnings.

## Discovery
- For this all-leaves specialization, no heavier reindexing is needed
  beyond the cycle 528 trunk recursion. The whole simplification is local:
  `hAllLeaf` plus `List.get_mem` rewrites both the cut product and the kept
  product pointwise.
- The theorem deliberately retains the explicit `t₁` parameter from the
  planned statement even though the coefficient-parametric lemma does not
  use it computationally; this keeps the shape ready for the upcoming
  `coef := t₁.bSeries` specialization.

## Suggested next approach
Next cycle should specialize this lemma at `coef := t₁.bSeries` to land
`ButcherProduct.bSeries_natAdd_node_trunk_kept_leaf_eq`, using
`ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef` to reduce the product
tableau statement to the coefficient-parametric theorem from this cycle.
After that, the remaining structural seam is the kept-node pass-through
case; do not jump to `G1.mul` or product congruence before the honest
§384 convolution closes.
