# Cycle 538 Results

## Worked on

Butcher §384 honest bSeries-only convolution: the first concrete closed
forms for the b-weighted right block, all landing in
`OpenMath/ButcherGroup/Section384.lean`. Strategy specified three
sequential steps (singleton-node, kept-leaf, all-leaves), all attempted
and all landed.

## Approach

Skipped Aristotle entirely. Recent ~10 cycles (509, 511, 512, 513, 515,
516, 517, 519, 521, 523, 524, 529, 537) have hit HTTP 429 on first
submit per the planner's notes; manual closure was the load-bearing
path for those cycles, and the strategy explicitly green-lit going
straight to manual closure for Step 1 ("purely arithmetic; should not
need Aristotle"). Steps 2 and 3 reduced to existing cycle 525-534
helpers plus a single new private helper, so all three closed by hand.

### Step 1: `ButcherProduct.bWeighted_convAt_singleton_node_eq`

Bridged LHS to `rightAuxAtCoef` form via `rightAuxAtCoef_eq_convAt`,
applied cycle 525's `bWeighted_rightAuxAtCoef_node_singleton`, bridged
the kept inner sum back to `convAt`, and reordered the cut term with
`mul_comm` so the RHS reads `t₂.weightsSum * coef c + ...`.

### Step 2: `ButcherProduct.bWeighted_convAt_kept_leaf_eq`

One-line `simp` using `ButcherTableau.bSeries`,
`elementaryWeight_singleton`, and `convAt_leaf`. The inner kept sum
`∑ j, A i j * convAt t₂ coef leaf j` reduces to `∑ j, A i j` via
`convAt_leaf`, which is exactly `elementaryWeight (node [leaf]) i` by
`elementaryWeight_singleton`, so the full b-weighted sum is
`t₂.bSeries (node [leaf])` by definition of `bSeries`.

### Step 3: `ButcherProduct.bWeighted_convAt_node_all_leaves_eq`

Two layers:

1. Private helper `elementaryWeight_node_replicate_leaf`: by induction
   on `n`,
   `tab.elementaryWeight (BTree.node (List.replicate n BTree.leaf)) i
     = (∑ k, tab.A i k) ^ n`. Zero case unfolds to `1`; successor case
   uses `List.replicate_succ` and `simp [elementaryWeight, List.foldr]`
   to peel one factor `(∑ k, A i k * 1)`, then `pow_succ`.
2. Main lemma: bridge LHS to `rightAuxAtCoef`; apply cycle 529's
   `bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq` (with `t₁ := t₂`
   for the vestigial parameter); rewrite the per-`S` summand by
   converting `∏ _p ∈ Sᶜ, ∑ j, A i j` to `(∑ j, A i j) ^ Sᶜ.card` via
   `Finset.prod_const`, and `Sᶜ.card = children.length - S.card` via
   `Finset.card_compl` plus `Fintype.card_fin`. Then unfold the RHS
   `t₂.bSeries (node (replicate (children.length - S.card) leaf))` via
   the helper, and the two sides match summand by summand.

## Result

SUCCESS.

- `OpenMath/ButcherGroup/Section384.lean` compiles cleanly with zero
  new sorries (`lake env lean` exit 0).
- `lake build` succeeds (8075/8075 jobs, no errors).
- All three target theorems landed as real proofs (no `:= rfl` stubs).
- File grew from 1776 to 1912 lines, well under the 3000-line cap.

## Dead ends

None this cycle. The strategy's pre-baked plan from cycles 525-534
helpers and the convAt/rightAuxAtCoef bridge made the proof path
direct.

The only minor friction was the vestigial `t₁ : ButcherTableau s`
parameter on
`bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq`. Resolved by passing
`t₂ t₂` (the body of that lemma only uses `t₁` through `_ht₁ : t₁ = t₁`,
so `t₁ := t₂` is fine). A follow-up cleanup could drop that vestigial
arg, but it's not worth a cycle.

## Discovery

- `Finset.card_compl S = Fintype.card α - S.card` plus
  `Fintype.card_fin` cleanly closes the
  `Sᶜ.card = children.length - S.card` lemma without needing
  `Finset.card_univ` or a manual cardinality argument.
- `List.replicate_succ` is the only `simp`-friendly unfold lemma that
  reliably exposes the cons head; `simp [List.replicate]` alone does
  not reach the cons form (it keeps the recursive function
  unevaluated).
- The strategy's RHS shape `BTree.node (List.replicate n BTree.leaf)` is
  exactly the right shape for `elementaryWeight`-style recursion: the
  helper lemma is one direct induction with no auxiliary fact.

## Suggested next approach

The next §38 seam (per the strategy text) is the mixed-leaf/node
generalization toward the full `(trunk, cuts)` closed form. Concretely,
the next cycle should attempt one of:

1. Generalize Step 3 to allow each child of the root to be either a
   leaf or a one-child node `BTree.node [gc p]`, by case-splitting on
   `children.get p` inside the kept-side product. The cycle 532
   `bWeighted_rightAuxAtCoef_node_trunk_kept_eq` already provides the
   coefficient-parametric mixed-children pass-through; the new work is
   showing that the kept factor on a node child also collapses to a
   `t₂.bSeries`-shaped value (probably via cycle 530's
   `bWeighted_rightAuxAtCoef_node_trunk_kept_singleton_node_eq` and
   another `convAt` ↔ `bSeries (node ...)` bridge).
2. Or, more ambitiously, attempt a full `BTree.rec`-driven closed form
   `bWeighted_convAt_eq_bSeries_sum_over_cuts` covering arbitrary node
   trees of any depth. This likely needs an explicit `(trunk, cuts)`
   datatype, mirroring the §386 structure in Butcher.

`IsG1Equiv.product_congr` is still blocked on the cross-stage gap; do
not retry it until the closed form covers arbitrary trees.

The current file size (1912 lines) is comfortable. No split needed
this cycle.
