# Cycle 570 Results

## Worked on
- `ButcherProduct.bSeriesConv_consistency` (headline) in
  `OpenMath/ButcherGroup/Section386Conv.lean`.
- Stagewise auxiliaries: `cutAt`, `cutAt_leaf`, `cutAt_node_nil`,
  `bSeriesConv_eq_sum_b_cutAt`, `cutAt_eq_convAt`,
  `innerCutForest_sum_eq`, `innerCutForest_sum_eq_listProd`.
- `QuotEquiv.bSeriesHom_product_eq` re-export in
  `OpenMath/ButcherGroup.lean`.

## Approach
Followed the strategy: add a stagewise `cutAt` aux and reduce the
headline through two bridge lemmas:

1. `bSeriesConv_eq_sum_b_cutAt`: `bSeriesConv α t₂.bSeries τ = ∑ i, t₂.b i * cutAt α t₂ τ i`.
   Generalised the inner-cut list to a fresh `L`, induct on `L`, with the
   `some trunk` step using `Finset.mul_sum`, `Finset.sum_add_distrib`,
   and `ring`.
2. `cutAt_eq_convAt`: stagewise bridge. Reduces via list-level forest
   invariant `innerCutForest_sum_eq` (Finset.prod_add bridge once the
   `listProd` form holds).

Submitted 5 Aristotle scaffolds covering the simp lemmas,
`innerCutForest_sum_eq`, `cutAt_eq_convAt`, `bSeriesConv_eq_sum_b_cutAt`,
and `bSeriesConv_consistency` headline.

## Result
PARTIAL SUCCESS:
- ✅ Headline `ButcherProduct.bSeriesConv_consistency` lands modulo two
  small helper sorries.
- ✅ `bSeriesConv_eq_sum_b_cutAt` PROVED manually.
- ✅ `cutAt_leaf`, `cutAt_node_nil` PROVED.
- ✅ `innerCutForest_sum_eq` PROVED, modulo the `listProd` helper.
- ✅ `QuotEquiv.bSeriesHom_product_eq` lifted via
  `Quotient.inductionOn₂` and `bSeriesConv_consistency`.
- ❌ `innerCutForest_sum_eq_listProd`: structure (flatMap decomposition,
  tailSum factor) compiled, but the trunk-cons `elementaryWeight` step
  required an explicit lemma rather than `unfold ... ; rfl`. Stripped to
  `sorry` to keep the file green.
- ❌ `cutAt_eq_convAt`: depends on `innerCutForest_sum_eq` being fully
  proved; left as `sorry`.
- ⏳ All 5 Aristotle jobs were still `QUEUED` 30+ minutes after
  submission. None landed in time to incorporate.

Both `OpenMath/ButcherGroup/Section386Conv.lean` and
`OpenMath/ButcherGroup.lean` compile cleanly with `lake env lean`.

## Dead ends
- `innerCutForest_sum_eq_listProd` cons step: tried `set tailSum := …`
  to fold the inner-cut tail expression, but a prior
  `simp [Function.comp_def]` had already unfolded the shape, so
  `rw [htailSum, ih]` could not find the pattern. Workarounds (`change`,
  `show`) were attempted but introduced fresh shape mismatches. The
  underlying `unfold ButcherTableau.elementaryWeight; rfl` step also
  failed because `BTree.node (trunk :: cs)` does not reduce
  definitionally to the desired factorization in the current
  `elementaryWeight` definition. The clean fix is a small explicit
  lemma:
    `elementaryWeight (BTree.node (trunk :: cs)) i =
      elementaryWeight (BTree.node cs) i *
        ∑ k, t₂.A i k * t₂.elementaryWeight trunk k`.

## Discovery
- `bSeriesConv_eq_sum_b_cutAt` does NOT need any structural induction on
  `τ`; the list induction on the inner-cut list discharges everything
  cleanly. This is a robust, reusable pattern for converting between
  `bSeries`-weighted and elementary-weight-keyed cut sums.
- `Finset.prod_add` matches the `Finset.univ.powerset` form, but
  unification needs `show`-rewriting because the pattern uses `↑p` vs `p`.
- The `congrArg₂ (· * ·)` move closed the final S-comparison after `congr 1`
  was over-eagerly accepting both subgoals.

## Suggested next approach
1. **Cycle 571 priority**: prove the explicit
   `elementaryWeight_node_cons` factor lemma, then close
   `innerCutForest_sum_eq_listProd` cleanly without `rfl`. With this
   helper, both outstanding sorries should close in a single cycle.
2. After cycle 570's Aristotle queue clears, harvest any successful
   proofs from project IDs:
   - `90fc84fa-…` (cutAt_simp)
   - `e0cf5ab0-…` (innerCutForest_sum_eq)
   - `85b22fdf-…` (cutAt_eq_convAt)
   - `2b44b99f-…` (bSeriesConv_eq_sum_b_cutAt)
   - `aacfe5bb-…` (bSeriesConv_consistency)
3. Once `cutAt_eq_convAt` is fully proved, `IsG1Equiv.product_congr`
   can replay through `bSeriesHom_product_eq` to handle ALL trees, not
   just the family slices currently enumerated in `ButcherGroup.lean`.
