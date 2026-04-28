# Cycle 531 Results

## Worked on
Butcher §384 right-block convolution in `OpenMath/ButcherGroup.lean`.
Landed the primary kept-node pass-through theorem
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_node_eq`, plus the
secondary bSeries-form singleton-node corollary
`ButcherProduct.bSeries_natAdd_node_trunk_kept_singleton_node_eq`.

## Approach
- Followed the cycle 530 skeleton for
  `ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq`.
- Wrote the Task 1 theorem sorry-first and verified the statement elaborated
  with `lake env lean OpenMath/ButcherGroup.lean`.
- Submitted the live file to Aristotle with the single Task 1 sorry. Aristotle
  immediately returned HTTP 429 (`too many requests in progress`), so no
  30-minute wait was useful; manual closure proceeded per the planner's
  explicit fallback.
- Closed Task 1 by rewriting with
  `ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion` and
  `Finset.powerset_univ`, rewriting each child through `hChild`, and expanding
  each kept recursive factor using
  `ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum` on the grandchild list
  `gc p`.
- Added Task 2 by specializing cycle 530's singleton-node trunk theorem at
  `coef := t₁.bSeries` via
  `ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef`.

## Result
SUCCESS. `OpenMath/ButcherGroup.lean` now contains:

1. `ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_node_eq`
   - coefficient-parametric kept-node trunk simplification for arbitrary
     grandchild lists.
2. `ButcherProduct.bSeries_natAdd_node_trunk_kept_singleton_node_eq`
   - product-tableau bSeries corollary of the cycle 530 singleton-node
     theorem.

`plan.md` was updated in the §384 tracking paragraphs to record both cycle
531 theorem names. The targeted check
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
compiled cleanly with no `sorry` or `admit` remaining in the file.

## Dead ends
- Aristotle could not be used this cycle because the submission returned HTTP
  429 before a project was created.
- No Lean proof dead ends. The proof closed directly with the same
  `Finset.sum_congr` / `Finset.prod_congr` skeleton as cycle 530, replacing
  the singleton-node rewrite with `rightAuxAtCoef_node_eq_powerset_sum`.

## Discovery
- The arbitrary kept-node theorem is essentially the singleton-node theorem
  with one local change: after `hChild p`, the kept factor
  `rightAuxAtCoef t₂ coef (BTree.node (gc p)) j` rewrites directly to the
  inner powerset sum over `Fin (gc p).length`.
- The bSeries-level singleton corollary remains a one-line specialization of
  the coefficient-parametric theorem once the RHS is stated with
  `t₁.bSeries` in the cut and grandchild coefficient positions.

## Suggested next approach
Continue one structural layer at a time toward the honest `(trunk, cuts)`
closed form. The next useful seam is to combine the kept-leaf and kept-node
pass-through cases into a theorem for arbitrary kept children, likely by
case-splitting each kept child and reusing
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq` /
`ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_node_eq` as the
leaf and node local simplifications.
