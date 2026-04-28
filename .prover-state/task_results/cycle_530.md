# Cycle 530 Results

## Worked on
Butcher §384 right-block convolution in `OpenMath/ButcherGroup.lean`.
Both planner-prescribed seams landed:
- Task 1: `ButcherProduct.bSeries_natAdd_node_trunk_kept_leaf_eq`
  — bSeries-form corollary of cycle 529's all-leaves trunk
  simplification, specialized at `coef := t₁.bSeries`.
- Task 2: `ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq`
  — kept-side single-node-children case, expanding the kept-side
  recursive auxiliary one structural level via
  `rightAuxAtCoef_node_singleton`.

## Approach
- Sorry-first / inspection-first ordering: skimmed cycle 529's
  structure to confirm the trunk-recursion cycle 528 lemma and the
  cycle 528 leaf-form corollary `bSeries_natAdd_leaf_eq`, then mirrored
  the same `bSeries_natAdd_eq_rightAuxAtCoef` chain for task 1.
- Task 1 reduces to a one-line two-rewrite combination: rewrite the
  product-tableau `b`-weighted stage sum at `BTree.node children` via
  `ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef` to land at
  `coef = t₁.bSeries`, then close with cycle 529's
  `bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq` applied at
  `coef := t₁.bSeries`. No reindexing needed; the RHS is exactly the
  cycle 529 form with `coef BTree.leaf` replaced by `t₁.bSeries
  BTree.leaf`.
- Task 2 is structurally identical to cycle 529's proof skeleton, but
  the per-child simplification is one level deeper. The hypothesis
  `hChild : ∀ p, children.get p = BTree.node [gc p]` rewrites each
  child to a singleton-node tree, and the kept inner factor
  `rightAuxAtCoef t₂ coef (BTree.node [gc p]) j` then unfolds via
  `rightAuxAtCoef_node_singleton` into
  `coef (gc p) + ∑ k, t₂.A j k * rightAuxAtCoef t₂ coef (gc p) k`.
- Verified with `lake env lean OpenMath/ButcherGroup.lean` after each
  insertion. Both compile cleanly with no errors and no new sorries.
- No Aristotle jobs submitted, per the cycle 530 strategy default
  (HTTP 429 / QUEUED on cycles 515-529; manual closure was fast for
  these `Finset.sum` / `Finset.prod` rewrites).

## Result
SUCCESS. Two new theorems landed in `OpenMath/ButcherGroup.lean`:

1. `ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq`
   — coefficient-parametric kept singleton-node trunk simplification.
2. `ButcherProduct.bSeries_natAdd_node_trunk_kept_leaf_eq` —
   bSeries-form corollary of cycle 529.

The trunk recursion now factors through `coef`-only values on
subtrees one full level beyond the leaf base case, and the cycle 529
structural identity is exposed at the product-tableau bSeries level
ready to feed the eventual `(trunk, cuts)` closed form.

## Dead ends
- None this cycle. Both lemmas closed on the first attempt with the
  recipes the planner identified. The kept singleton-node proof uses
  the same `Finset.sum_congr` / `Finset.prod_congr` skeleton as cycle
  529; the only change is one extra `Finset.sum_congr` step inside the
  kept-factor product to expand `rightAuxAtCoef` of the singleton-node
  child via `rightAuxAtCoef_node_singleton`.

## Discovery
- The kept-singleton-node lemma deliberately avoids the `t₁` parameter
  (cycle 529 retained an unused `t₁`); the structurally cleanest
  statement here is purely coefficient-parametric, since no
  `t₁.bSeries` specialization is requested at this level. A bSeries
  specialization can be assembled in a future cycle by chaining with
  `bSeries_natAdd_eq_rightAuxAtCoef` at `coef := t₁.bSeries`, mirroring
  the task 1 / cycle 528 recipe.
- The natural next structural step is the kept-node *pass-through*
  case for arbitrary children: replace the singleton-node hypothesis
  `children.get p = BTree.node [gc p]` with the general node case
  `children.get p = BTree.node gc_p` for some `gc_p : List BTree`,
  expanding the kept inner factor via
  `bWeighted_rightAuxAtCoef_node` (i.e. the powerset over `gc_p`).
  That is the exact seam the planner left for the next cycle.

## Suggested next approach
Next cycle's planner should pick exactly one of:
1. Generalize task 2 to arbitrary kept node-children:
   `ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_kept_node_eq`,
   with hypothesis
   `hChild : ∀ p : Fin children.length, ∃ gc, children.get p = BTree.node gc`
   (or the function form) and inner expansion via
   `rightAuxAtCoef_node_eq_powerset_sum` on the grandchild list. This
   is the kept-node pass-through case the strategy named.
2. Land the bSeries-form corollary of cycle 530's task 2 — i.e.
   specialize `bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq`
   at `coef := t₁.bSeries` to get
   `bSeries_natAdd_node_trunk_kept_singleton_node_eq`, the same
   one-line `bSeries_natAdd_eq_rightAuxAtCoef` chain as cycle 530's
   task 1.

Option (1) advances the structural recursion one more level toward
the honest `(trunk, cuts)` closed form. Option (2) is symmetry-only
work but tightens the bSeries-level surface for the eventual
`bSeriesHom_product` step. Recommend (1) since it is the load-bearing
seam.

`OpenMath/ButcherGroup.lean` is now ~2740 lines (up from 2701; well
under the 3000-line cap). No split needed.
